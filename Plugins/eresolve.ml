(** Adds a kind [EResolve] of hints which are only used by [eauto] and
    always with [eapply] regardless of their types. *)

(* All of this file is adaptated from Coq's [auto.ml] *)

let rec nb_hyp c = let open Term in match kind_of_term c with
  | Prod(_,_,c2) -> if noccurn 1 c2 then 1+(nb_hyp c2) else nb_hyp c2
  | _ -> 0

let make_eapply_entry env sigma hnf pri ?(name=Auto.PathAny) (c,cty) =
  let open Auto in
  let open Term in
  let cty = if hnf then Tacred.hnf_constr env sigma cty else cty in
    match kind_of_term cty with
    | Prod _ ->
        let ce = Clenv.mk_clenv_from Goal.V82.dummy_goal (c,cty) in
	let c' = Clenv.clenv_type (* ~reduce:false *) ce in
	let pat = snd (Pattern.pattern_of_constr sigma c') in
        let hd =
	  try Pattern.head_pattern_bound pat
          with Pattern.BoundPattern -> failwith "make_apply_entry" in
        let nmiss = List.length (Clenv.clenv_missing ce) in
        (Some hd,
         { pri = (match pri with None -> nb_hyp cty + nmiss | Some p -> p);
           pat = Some pat;
	   name = name;
           code = ERes_pf(c,cty) })
    | _ -> failwith "Eresolve.make_eapply_entry"

let make_eresolves env sigma hnf pri ?name c =
  let cty = Retyping.get_type_of env sigma c in
  let ents =
    Util.map_succeed
      (fun f -> f (c,cty))
      [Auto.make_exact_entry sigma pri ?name; make_eapply_entry env sigma hnf pri ?name]
  in
  if ents = [] then
    Pp.(Util.errorlabstrm "Hint"
      (Printer.pr_lconstr c ++ spc() ++
        (str"cannot be used as a hint.")));
  ents

type eresolve_obj = bool * string * Auto.hint_entry list  (* locality, name, action *)

let get_db dbname =
  try Auto.searchtable_map dbname
  with Not_found -> Auto.Hint_db.empty Names.empty_transparent_state false

let add_hint dbname hintlist = 
  let db = get_db dbname in
  let db' = Auto.Hint_db.add_list hintlist db in
  Auto.searchtable_add (dbname,db')

let cache_eresolve (_,(local,name,hints)) =
  add_hint name hints

let subst_path_atom subst p =
  let open Auto in
  match p with
  | PathAny -> p
  | PathHints grs ->
    let gr' gr = fst (Libnames.subst_global subst gr) in
    let grs' = Util.list_smartmap gr' grs in
      if grs' == grs then p else PathHints grs'

let subst_eresolve (subst,(local,name,hintlist as obj)) =
  let open Auto in
  let subst_key gr =
    let (lab'', elab') = Libnames.subst_global subst gr in
    let gr' =
      (try Pattern.head_of_constr_reference (fst (Tactics.head_constr_bound elab'))
       with Tactics.Bound -> lab'')
    in if gr' == gr then gr else gr'
  in
  let subst_hint (k,data as hint) =
    let k' = Option.smartmap subst_key k in
    let pat' = Option.smartmap (Pattern.subst_pattern subst) data.pat in
    let code' = match data.code with
      | ERes_pf (c,t) ->
          let c' = Mod_subst.subst_mps subst c in
          let t' = Mod_subst.subst_mps subst t in
          if c==c' && t'==t then data.code else ERes_pf (c',t')
      | _ -> assert false
    in
    let name' = subst_path_atom subst data.name in
    let data' =
      if data.pat==pat' && data.name == name' && data.code==code' then data
      else { data with pat = pat'; name = name'; code = code' }
    in
    if k' == k && data' == data then hint else (k',data')
  in
  let hintlist' = Util.list_smartmap subst_hint hintlist in
  if hintlist' == hintlist then obj else
  (local,name,hintlist')


let classify_eresolve ((local,name,hintlist) as obj) =
  if local or hintlist = [] then Libobject.Dispose else Libobject.Substitute obj

let eresolveHint : eresolve_obj -> Libobject.obj =
  let open Libobject in
  declare_object {(default_object "ERESOLVEHINT") with
                    cache_function = cache_eresolve;
		    load_function = (fun _ -> cache_eresolve);
		    subst_function = subst_eresolve;
		    classify_function = classify_eresolve; }

let add_hints_eresolve lc n bl =
  if List.mem "nocore" bl then
    Util.error "The hint database \"nocore\" is meant to stay empty.";
  let env = Global.env() and sigma = Evd.empty in
  let lc =
    List.map begin fun c ->
      let c = Constrintern.interp_constr Evd.empty env c in
      (n,true,Auto.PathAny,c)
    end lc
  in
  List.iter
    (fun dbname ->
      Lib.add_anonymous_leaf
	(eresolveHint
	   (false,dbname,
     	     (List.flatten (List.map (fun (x, hnf, path, y) ->
	       make_eresolves env sigma hnf x ~name:path y) lc)))))
    bl

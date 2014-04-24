(** A "reduction" strategy which folds a term into a combinatorial
    term. *)

let t_of_qn qp id =
  Coqlib.check_required_library qp;
  let pp_qn = (List.fold_left (fun acc id -> acc^id^".") "" qp)^id in
  let not_found = "Cannot find: "^pp_qn^" ." in
  let gref = Coqlib.find_reference not_found qp id in
  Libnames.constr_of_global gref

let base_lib = ["Cosa";"Lib";"Tactics"]

let id = t_of_qn base_lib "id"
let k = t_of_qn base_lib "kc"
let s = t_of_qn base_lib "sc"
let comp = t_of_qn base_lib "compc"



(* spiwack: copied from termops, the v8.4 version is incorrect *)
let rec eta_reduce_head c =
  let open Term in
  match kind_of_term c with
    | Lambda (_,_,c') ->
	(match kind_of_term (eta_reduce_head c') with
           | App (f,cl) ->
               let lastn = (Array.length cl) - 1 in
               if lastn < 0 then Util.anomaly "application without arguments"
               else
                 (match kind_of_term cl.(lastn) with
                    | Rel 1 ->
			let c' =
                          if Int.equal lastn 0 then f
			  else mkApp (f, Array.sub cl 0 lastn)
			in
			if noccurn 1 c'
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c


let close_constant env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda (_,ta,c') when noccurn 1 c' ->
      let c'' = lift (-1) c' in
      let tc = Retyping.get_type_of env sigma c'' in
      mkApp ( k , [|tc;ta;c''|] )
  | _ -> c

let close_id _ _ c =
  let open Term in
  match kind_of_term c with
  | Lambda (_,ta,c') when eq_constr c' (mkRel 1) -> mkApp(id,[|ta|])
  | _ -> c

let yank_comp env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda (na,ta,c') ->
      begin match kind_of_term c' with
      | App (h,aps) ->
          assert (Array.length aps > 0);
          let lastn = Array.length aps - 1 in
          let c'' = mkApp (h,Array.sub aps 0 lastn) in
          if noccurn 1 c'' then
            let c''' = lift (-1) c'' in
            let tc = Retyping.get_type_of env sigma c''' in
            let (_,tca,tcb) = destProd tc in
            if noccurn 1 tcb then
              mkApp ( comp , [|ta;tca;tcb;c''';mkLambda(na,ta,aps.(lastn))|])
            else
              c
          else
            c
      | _ -> c
      end
  | _ -> c

let push_app env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda(na,ta,c') ->
      begin match kind_of_term c' with
      | App (h,aps) ->
          assert (Array.length aps > 0);
          let lastn = Array.length aps - 1 in
          let c'' = mkApp (h,Array.sub aps 0 lastn) in
          let c1 = mkLambda(na,ta,c'') in
          let c2 = mkLambda(na,ta,aps.(lastn)) in
          let tc = Retyping.get_type_of env sigma c1 in
          (* spiwack: [c1] is closed under the environmenent but it
             may be a simpler idea to retype [c''] under an extended
             environment.*)
          let (_,_,tc) = destProd tc in
          let (_,tca,tcb) = destProd tc in
          if noccurn 1 tcb then
            mkApp ( s , [|ta;tca;tcb;c1;c2|] )
          else
            c
      | _ -> c
      end
  | _ -> c

let combinatorize_head env sigma c =
  push_app env sigma (
  yank_comp env sigma (
  close_constant env sigma (
  close_id env sigma (
  eta_reduce_head c))))


let combinatorize env sigma c =
  let rec combinatorize env c =
  let open Term in
  match kind_of_term c with
  | Lambda (na,ta,c') ->
      let env' = Environ.push_rel (na,None,ta) env in
      Reductionops.strong combinatorize_head env sigma
        (mkLambda(na,ta,combinatorize env' c'))
  | _ -> Termops.map_constr_with_full_binders Environ.push_rel combinatorize env c
  in
  combinatorize env c
(* let rec combinatorize env c = *)
  (*   combinatorize_head env sigma (Termops.map_constr_with_full_binders Environ.push_rel combinatorize env c) *)
  (* in *)
  (* combinatorize env c *)

(** Declares the reduction function, so that it can be used as [eval
    combinatorize in t]. *)
let _ = Redexpr.declare_reduction "combinatorize" combinatorize

(* debugging:
let _ = Redexpr.declare_reduction "debugeta" (fun _ _ -> eta_reduce_head)
let _ = Redexpr.declare_reduction "debugk" close_constant
let _ = Redexpr.declare_reduction "debugid" close_id
let _ = Redexpr.declare_reduction "debugs" push_app
let _ = Redexpr.declare_reduction "debugcomp" yank_comp
*)

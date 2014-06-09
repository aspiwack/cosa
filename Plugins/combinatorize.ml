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
let swap = t_of_qn base_lib "swapc"


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
                          if lastn == 0 then f
			  else mkApp (f, Array.sub cl 0 lastn)
			in
			if noccurn 1 c'
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c


(** λx.M ↝ KM (x∉M)*)
let close_constant env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda (_,ta,c') when noccurn 1 c' ->
      let c'' = lift (-1) c' in
      let tc = Retyping.get_type_of env sigma c'' in
      mkApp ( k , [|tc;ta;c''|] )
  | _ -> c

(** λx.x ↝ I *)
let close_id _ _ c =
  let open Term in
  match kind_of_term c with
  | Lambda (_,ta,c') when eq_constr c' (mkRel 1) -> mkApp(id,[|ta|])
  | _ -> c

(** λx.uM ↝ u∘(λx.M) (x∉u) *)
(* currently unused *)
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
              mkApp ( comp , [|ta;tca;(lift (-1) tcb);c''';mkLambda(na,ta,aps.(lastn))|])
            else
              c
          else
            c
      | _ -> c
      end
  | _ -> c

(** S(KM) ↝ M∘- *)
let fold_comp env sigma c =
  let open Term in
  match kind_of_term c with
  | App (h,ha) when Array.length ha >= 4 && eq_constr h s ->
      let km = ha.(3) in
      begin match kind_of_term km with
      | App (h',[|_;_;m|]) when eq_constr h' k ->
	  (* l:a->b m:b->c *)
          let a = ha.(0) in
	  let b = ha.(1) in
	  let c = ha.(2) in
	  let spine = Array.sub ha 4 (Array.length ha - 4) in
          mkApp ( mkApp (comp,[|a;b;c;m|]) , spine )
      | _ -> c
      end
  | _ -> c

(** SM(KN) ↝ swap M N *)
let fold_swap env sigma c =
  let open Term in
  match kind_of_term c with
  | App (h,ha) when Array.length ha >= 5 && eq_constr h s ->
      let m = ha.(3) in
      let kn = ha.(4) in
      begin match kind_of_term kn with
      | App (h',[|_;_;n|]) when eq_constr h' k ->
	  (* m:a->b->c n:b *)
          let a = ha.(0) in
	  let b = ha.(1) in
	  let c = ha.(2) in
	  let spine = Array.sub ha 5 (Array.length ha - 5) in
          mkApp ( mkApp (swap,[|a;b;c;m;n|]) , spine )
      | _ -> c
      end
  | _ -> c
(** λx.MN ↝ (λx.M)(λx.N) *)
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

(** λx.SKM ↝ KI (John Tromp uses SK instead of KI because I are costly
    in his model. But it is not always a well-typed reduction, whereas KI
    always is). *)
let close_kid env sigma c =
  let open Term in 
  match kind_of_term c with
  | Lambda(na,ta,c') ->
      begin match kind_of_term c' with
      | App (h,[|tb;tc;td;u;m|]) when eq_constr h s ->
          begin match kind_of_term u with
          | App (h',[|te;tf;|]) when eq_constr h' k ->
              let tk = mkArrow tb (lift 1 tb) in
              mkApp (k , [| tk ; ta ; mkApp( id , [| tb |] ) |])
          | _ -> c
          end
      | _ -> c 
      end
  | _ -> c

(** Tromp has a rule λx.xMx ↝ λx.(SSKMx). My understanding is that
    this rule is useful because in his system I is costly. I don't
    believe I need to implement it. *)

(** λx.M(NL) ↝ λx.S(λx.M)NL (M,N closed). Note that λx.M = KM,
    however, it may be possible to optimise using the {!close_kid}
    rule. *)
let yank_dcomp env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda (na,ta,b) ->
      let env' = Environ.push_rel (na,None,ta) env in
      begin match kind_of_term b with
      | App (h,ha) when Array.length ha >= 1->
          begin match kind_of_term ha.(Array.length ha - 1) with
          | App (h',ha') when Array.length ha >=1 ->
              let m = mkApp (h,Array.sub ha 0 (Array.length ha-1)) in
              let n = mkApp (h',Array.sub ha' 0 (Array.length ha'-1)) in
              let l = ha'.(Array.length ha'-1) in
              if closed0 m && closed0 n then
                (* m: b -> c , n : a -> b , l : a *)
                let a = Retyping.get_type_of env' sigma l in
                let b =
                  lift (-1)
                    (Util.pi3 (destProd (Retyping.get_type_of env' sigma n)))
                in
                let c =
                  lift (-1)
                    (Util.pi3 (destProd (Retyping.get_type_of env' sigma m)))
                in
                let km = mkLambda(na,a,m) in(* no lift because m is closed *)
                mkLambda(na,ta,
                  mkApp (s , [| a ; b ; c ; km ; n ; l |])
                )
              else
                c
          | _ -> c
          end
      | _ -> c
      end
  | _ -> c

(** λx.MNL ↝ λx.SM(λx.L)N (M,L closed). Note that λx.M = KM, however,
    it may be possible to optimise using the {!close_kid} rule.*)
let yank_dapp env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda(na,ta,b) ->
      let env' = Environ.push_rel (na,None,ta) env in
      begin match kind_of_term b with
      | App(h,ha) when Array.length ha >= 2 ->
          let m = mkApp (h , Array.sub ha 0 (Array.length ha - 2)) in
          let n = ha.(Array.length ha - 2) in
          let l = ha.(Array.length ha - 1) in
          if closed0 m && closed0 l then
            (* m:a->b->c  n:a  l:b *)
            let a = Retyping.get_type_of env' sigma n in
            let b = Retyping.get_type_of env' sigma l in
            let c =
              lift (-2)
                (Util.pi3 (destProd (Util.pi3 (destProd (
                  Retyping.get_type_of env' sigma m
                 )))))
            in
            let kl = mkLambda(na,a,l) in (* no lift because l is closed *)
            mkLambda (na,ta,
               mkApp (s , [| a ; b ; c ; m ; kl ; n |])
            )
          else
            c
      | _ -> c
      end
  | _ -> c

(** λx.ML(NL) ↝ λx.SMNL *)
let fold_s env sigma c =
  let open Term in
  match kind_of_term c with
  | Lambda (na,ta,b) ->
      let env' = Environ.push_rel (na,None,ta) env in
      begin match kind_of_term b with
      | App (h,ha) when Array.length ha >= 2 ->
          let m = mkApp (h , Array.sub ha 0 (Array.length ha - 2)) in
          let l = ha.(Array.length ha - 2) in
          let nl = ha.(Array.length ha - 1) in
          begin match kind_of_term nl with
          | App (h',ha') when Array.length ha >= 1 ->
              let n = mkApp (h , Array.sub ha 0 (Array.length ha - 1)) in
              let l' = ha.(Array.length ha - 1) in
              if eq_constr l l' then
                (* m:a->b->c n:a->b l:a *)
                let a = Retyping.get_type_of env' sigma l in
                let b =
                  lift (-1)
                    (Util.pi3 (destProd (Retyping.get_type_of env' sigma n)))
                in
                let c =
                  lift (-2)
                    (Util.pi3 (destProd (Util.pi3 (destProd (
                      Retyping.get_type_of env' sigma m
                     )))))
                in
                mkLambda (na,ta,
                          mkApp (s , [| a ; b ; c ; m ; n ; l |])
                )
              else
                c
          | _ -> c
          end
      | _ -> c
      end
  | _ -> c

(** To try and optimise the size of the term we use a variant of an
    algorithm due to John Tromp
    [http://homepages.cwi.nl/~tromp/cl/LC.pdf] *)

let tromp_strategy = [
  close_kid;
  close_constant;
  close_id;
  (fun _ _ c -> eta_reduce_head c);
  yank_dcomp;
  yank_dapp;
  fold_s;
  push_app;
]

let turner_simplification = [
  fold_comp;
  fold_swap;
]

(** Applies the first rule of [strat] which acts non trivially on
    [c]. *)
(* Implementation note: the rules are all set up such that they return
   exactly their input when they don't apply, so that we can use pointer
   equality to check for failure. *)
let rec head_reduce_once strat env sigma c =
  match strat with
  | [] -> c
  | r::strat' ->
      let c' = r env sigma c in
      if c' == c then head_reduce_once strat' env sigma c
      else c'

(** Applies {!head_reduce_once strat} repeatedly until no rules can
    act on [c]. *)
let rec head_reduce strat env sigma c =
  let c' = head_reduce_once strat env sigma c in
  if c' == c then c'
  else head_reduce strat env sigma c'

let combinatorize_head env sigma c =
  head_reduce tromp_strategy env sigma c

let combinatorize_first_pass env sigma c =
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

let combinatorize_second_pass env sigma c =
  Reductionops.strong
    (fun env sigma c -> head_reduce turner_simplification env sigma c) env sigma c

let combinatorize env sigma c =
  combinatorize_second_pass env sigma (
    combinatorize_first_pass env sigma c
  )



(** Declares the reduction function, so that it can be used as [eval
    combinatorize in t]. *)
let _ = Redexpr.declare_reduction "combinatorize" combinatorize

(* debugging:
let _ = Redexpr.declare_reduction "debugeta" (fun _ _ -> eta_reduce_head)
let _ = Redexpr.declare_reduction "debugk" close_constant
let _ = Redexpr.declare_reduction "debugid" close_id
let _ = Redexpr.declare_reduction "debugs" push_app
let _ = Redexpr.declare_reduction "debugcomp" yank_comp
let _ = Redexpr.declare_reduction "debugfcomp" (Reductionops.strong fold_comp)
*)

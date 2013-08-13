Require Import Cosa.Lib.Header.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Lib.Finite.

(* In a proof system or a rewriting system the applicability of a
   given inference rule is generally decidable. We give a
   characterisation of that property using a kind of pattern matching:
   if the [match_goal] field returns [None], then the rule does not
   apply, otherwise it returns the necessary decomposition of the goal
   to generate the next subgoals.

   The number of produces subgoals are also required to be finite, so
   that the proof can be checked. We impose that by giving a
   collection function on the [Shape] type. There could be a more
   general type for collect, but this simplified version will suffice
   for our purpose. *)
Record t {S T:Type} := {
  Pattern : Type ;
  match_goal: S -> option Pattern;
  subgoals: Pattern -> list T
}.
Arguments t S T : clear implicits.

Record rule_set {S T:Type} := {
  Rule: Type;
  action: Rule -> t S T
}.
Arguments rule_set S T : clear implicits.


(** A [rule_set S T] gives rise to two different interaction
    structures.  One of type [Interaction S T], and the other one of
    type [Interaction (option S) (option T)]. In the former the user
    who issues commands must provide a proof that the rule they mean
    to use is applicable to the current goal. It is useful to use in
    proofs. The latter has all the rules available at each state, and
    a dynamic check of the validity is issued. In case an invalid rule
    is issued, the output state is [None]. This is akin to automata
    completion: we transform a partial function into a total one by
    adding a junk state. It is meant to be used to check
    certificates. *)

Definition deductive {S T} (p:rule_set S T) : Interaction S T := {|
  Com s :=
    { r:p.(Rule) &
                 { a:(p.(action) r).(Pattern) | (p.(action) r).(match_goal) s = Some a }
    };
  Resp s c := fin (List.length ((p.(action) (projT1 c)).(subgoals) (proj1_sig (projT2 c))) );
  Output s c x := Finite.access ((p.(action) (projT1 c)).(subgoals) (proj1_sig (projT2 c))) x
|}.

Definition checker {S T} (p:rule_set S T) : Interaction (option S) (option T) := {|
  Com s := p.(Rule) ;
  Resp s c :=
    match s with
    | None => unit
    | Some s' =>
      match (p.(action) c).(match_goal) s' with
      | None => unit
      | Some a => fin (List.length ((p.(action) c).(subgoals) a))
      end
    end;
  Output s c x :=
    match s
          as s
          return
            match s with
            | None => unit
            | Some s' =>
              match (p.(action) c).(match_goal) s' with
              | None => unit
              | Some a => fin (List.length ((p.(action) c).(subgoals) a))
              end
            end
            -> option T
    with
    | None => fun _ => None
    | Some s' =>
        match (p.(action) c).(match_goal) s'
              as a
              return
                match a with
                | None => unit
                | Some a => fin (List.length ((p.(action) c).(subgoals) a))
                end
                -> option T
        with
        | None => fun _ => None
        | Some a => fun x => Some (Finite.access ((p.(action) c).(subgoals) a) x)
        end
    end x
|}.

(* Notice how there cannot be a proof of [None], as every rule act on
   it as the identity. Proofs of the checker can be used to build
   proof of the deductive system. And conversly, the checker is
   complete with respect to the deductive system. *)

Lemma proof_checker_proves :
   forall S (s:option S) p, Proof_of (checker p) s ->
                            { s':S & (s = Some s') * (Proof_of (deductive p) s') }%type.
Proof.
  intros * prf.
  induction prf as [ s r prf h ]; simpl in *.
  destruct s as [ s' | ]; [|intuition].
  exists s'.
  split.
  { reflexivity. }
  destruct ((p.(action) r).(match_goal) s') as [ a | ] eqn: h₁.
  - eexists.
    instantiate (1:= existT _ r (exist _ a h₁)).
    simpl.
    intros x.
    specialize (h x).
    destruct h as [ s'' [ val_s'' h ] ].
    injection val_s''; clear val_s''; intro val_s''.
    rewrite val_s''; trivial.
  - specialize (h tt).
    destruct h as [ ? [h _] ].
    discriminate h.
Defined.


Lemma proof_checker_proves_some :
   forall S (s:S) p, Proof_of (checker p) (Some s) -> Proof_of (deductive p) s.
Proof.
  intros * h.
  apply proof_checker_proves in h.
  destruct h as [ s' [ val_s' h ]].
  injection val_s'; clear val_s'; intro val_s'.
  rewrite val_s'; trivial.
Defined.

Lemma proof_checker_complete :
  forall S (s:S) p, Proof_of (deductive p) s -> Proof_of (checker p) (Some s).
Proof.
  intros * h.
  induction h as [ s [r [a ha]] prf h ]; simpl in *.
  exists r.
  simpl.
  rewrite ha.
  assumption.
Qed.  
  

(* The Name [proof_checker] comes from the fact that we can take an
   appropriate notion of proof certificate and use it to build a proof
   in the proof checker. 

   The [Certificate] type doesn't extract too well in OCaml, so if we
   want to generate certificate in ocaml, we will need to duplicate
   the type into a more explicit form. *)

Inductive Certificate {S} {p:rule_set S S} : Type :=
  | apply_rule
      (r:p.(Rule))
      (k:forall a, fin (List.length ((p.(action) r).(subgoals) a)) -> Certificate)
.
Arguments Certificate {S} p : clear implicits.

Require Coq.Program.Program.

Fixpoint check_certificate {S} (p:rule_set S S) (s:S) (c:Certificate p) : option (Proof_of (checker p) (Some s)).
Proof.
  destruct c as [r k].
  destruct ((p.(action) r).(match_goal) s) as [ a | ] eqn:h₁.
  - (* Some a *)
    set (check_sub := fun (n:fin (List.length ((p.(action) r).(subgoals) a))) =>
          check_certificate _ p (Finite.access ((p.(action) r).(subgoals) a) n) (k a n)).
    destruct (Finite.collectn Option _ check_sub) as [ k' | ].
    + (* Some k' *)
      refine (Some _).
      exists r.
      simpl; rewrite h₁.
      exact k'.
    + (* None *)
      exact None.
  - (* None *)
    exact None.
Defined.
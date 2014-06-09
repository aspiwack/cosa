(** Extra generic tactics. *)

Require Import Maps.
Require Coq.Classes.Morphisms.

Ltac simplify_transitivity1 :=
  etransitivity; eauto; [idtac]
.

Ltac simplify_transitivity :=
  repeat simplify_transitivity1
.
Ltac solve_transitivity :=
  solve [etransitivity;eauto]
.


Ltac decompose_conj :=
  lazymatch goal with
  | |- _ /\ _ => split; decompose_conj
  | |- _ <-> _ => split; decompose_conj
  | _ => idtac
  end
.
Ltac decompose_ex :=
  lazymatch goal with
  | |- ex _ => eexists; decompose_ex
  | _ => idtac
  end
.

Ltac decompose_concl :=
  repeat progress (decompose_ex;decompose_conj)
.


Ltac decompose_hyp h :=
  match type of h with
  | ex _ => 
    let x := fresh "x" in
    let h' := fresh "h" in
    destruct h as [x h'];
    decompose_hyp h'
  | _ <-> _ =>
    let h₁ := fresh "h" in
    let h₂ := fresh "h" in
    destruct h as [h₁ h₂];
    decompose_hyp h₁;decompose_hyp h₂
  | _ /\ _ =>
    let h₁ := fresh "h" in
    let h₂ := fresh "h" in
    destruct h as [h₁ h₂];
    decompose_hyp h₁;decompose_hyp h₂
  | ?y = _ => is_var y; try rewrite h in *; clear h y
  | _ = ?y => is_var y; try rewrite <- h in *; clear h y
  | _ => idtac
  end
.

Ltac decompose_hyps :=
  repeat
    match goal with
    | h:ex _ |- _ => decompose_hyp h
    | h:_ <-> _ |- _ => decompose_hyp h
    | h:_ /\ _ |- _ => decompose_hyp h
    | h:_ = ?y |- _ => is_var y; decompose_hyp h
    | h:?y = _ |- _ => is_var y; decompose_hyp h
    end
.

Ltac decompose_goal :=
  intros **;decompose_hyps;decompose_concl
.

Ltac rewrite_defs :=
  repeat match goal with
  | H:?y =  _ |- _ => is_var y; try rewrite H in *; clear H y
  | H: _ = ?y |- _ => is_var y; try rewrite <- H in *; clear H y
  end
.

(** applies t if the conclusion doesn't have existential vars *)
Ltac ifnevar t :=
  first [(
      match goal with
      | |- ?c => ((has_evar c; fail 1) || fail 2)
      end
    || idtac)
  | t]
.


Ltac prove_hyp h :=
  lazymatch type of h with
  | ?A->?B =>
    let h' := fresh "h" in
    assert A as h' ; [ | specialize (h h');clear h' ]
  | _ => fail"Hypothesis must be an implication."
  end
.

(** Tries to unify [h] with the goal, generates equality proof
    obligation when it fails. *)
Ltac apply_eq h :=
  lazymatch goal with
  |- ?c => let c' := type of h in replace c with c' ; [exact h|]
  end; f_equal
.

(** Adds an new [Hint EResolve] command which forces the hints to be
    used with [eapply]. *)

Declare ML Module "eresolve" "g_eresolve".

(** Combinators for the combinatorize tactic. *)

Definition id {A} (x:A) : A := x.
Definition kc {A B} (x:A) : B->A := fun _ => x.
Definition sc {A B C} (x:A->B->C) (y:A->B) (σ:A) : C := x σ (y σ).
Definition compc {A B C} (f:B->C) (g:A->B) : A->C := fun x => f (g x).
Definition swapc {A B C} (f:A->B->C) (x:B) (y:A) : C := f y x.



(** Hints for auto* tactics **)
Hint Unfold Morphisms.Proper Morphisms.respectful.

(** A place holder for a by-file termination tactic. *)
Ltac crush := fail.

Tactic Notation "by" tactic(t) := (t;crush).
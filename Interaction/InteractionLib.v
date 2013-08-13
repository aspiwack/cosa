Require Import Cosa.Lib.Header.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Interaction.Simulation.


(** Useful interaction structures. *)

(** Ignores the input state, returns [s]. *)

Definition just {A B} (s:B) : Interaction A B :=
  functional_extension (fun _ => s)
.

(** Requires a proof of [p] and does nothing. *)

Definition assume_dep {A} (p:A->Prop) : Interaction A { x: A | p x } := {|
  Com a := p a ;
  Resp a pr := unit ;
  Output a pr x := exist _ a pr
|}.

Definition assume {A} (p:A->Prop) : Interaction A A := {|
  Com a := p a ;
  Resp a pr := unit ;
  Output a pr x := a
|}.

Lemma assume_spec S₁ S₂ T₁ T₂ (i:Interaction S₁ S₂) (j:Interaction T₁ T₂) (P:S₁->Prop) :
  forall (Q:S₂->T₂->Prop),
    forall s t, (P s -> RT i j Q s t) ->
    RT (seq (assume P) i) j Q s t.
Proof.
  intros * h; unfold RT,seq in *; simpl in *.
  intros [ P_s c₁ ]; specialize (h P_s (c₁ tt)); simpl.
  destruct h as [ c₂ h ].
  exists c₂.
  intros x₂; specialize (h x₂).
  destruct h as [ x₁ h ].
  exists (existT _ tt x₁); simpl.
  assumption.
Qed.

(** [with_new] take a predicate [p] as an initial state, and returns a
    pair of an element [a] which does not belong to [p] and an updated
    predicate [p'] which contains all the elements of [p] plus
    [a]. For simplicity, it assumes that the appropriate equality on
    the type [A] of [a] is [eq]. [with_new] expects the new element to
    be provided as a command. *)
Definition with_new {A} : Interaction (A->Prop) (A*(A->Prop)) := {|
  Com p := { a:A | ~p a } ;
  Resp p a := unit ;
  Output p a x := ( proj1_sig a , p ∪ singleton (proj1_sig a))
|}.

Lemma with_new_spec A (p:A->Prop) a x : ~p(fst (with_new.(@Output _ _) p a x)).
Proof.
  simpl.
  apply proj2_sig.
Qed.
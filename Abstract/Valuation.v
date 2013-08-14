Require Import Cosa.Lib.Header.
Require Import Coq.Classes.EquivDec.

(** In this file we give useful functions and properties valuations,
    which are used both in the concretisation of the numerical domain
    and of the shape domain. Here we just assume valuations are
    functions whose domain has decidable equality. *)

Section Valuation.

  Context {A:Type} {e:EqDec A eq} {B:Type}.

  (** Composition with a partial renaming *)
  Definition partial_comp (f:A->option A) (g:A -> B) (x:A) : B :=
    match f x with
    | Some x' => g x'
    | None => g x
    end
  .

  (* arnaud: bouger vers Extra ? *)
  Lemma if_eq_refl C : forall (x:A) (e₁ e₂:C), (if x==x then e₁ else e₂) = e₁.
  Proof.
    intros *.
    destruct (x==x) as [ _ | neq_x_x ].
    { easy. }
    congruence.
  Qed.


  (** Swapping two arguments. *)
  Definition swap (α β:A) (f:A->B) (x:A) : B :=
    if x == α then f β
    else if x == β then f α
    else f x
  .

  (** Sanity checks. *)
  Remark swap_self_id α f : forall x, swap α α f x = f x.
  Proof.
    intros x; unfold swap.
    now destruct (x==α) as [ <- | _ ].
  Qed.

  Remark swap_idempotent α β f : forall x, swap α β (swap α β f) x = f x.
  Proof.
    intros x; unfold swap.
    destruct (x==α) as [ <- | neq_x_α ].
    - destruct (β==x) as [ <- | neq_β_x ].
      { easy. }
      apply if_eq_refl.
    - destruct (x==β) as [ <- | neq_β_x ]; [|easy].
      apply if_eq_refl.
  Qed.

  Remark swap_commutative α β f : forall x, swap α β f x = swap β α f x.
  Proof.
    intros x; unfold swap.
    destruct (x==α) as [ <- | neq_x_α ]; [|easy].
    destruct (x==β) as [ <- | neq_x_β ]; easy.
  Qed.


  (** A set [H] of [A] is central in a set [P] of valuation when we
      can freely swap arguments outside of [H] without exiting
      [P]. Central sets of nodes are used to pick fresh nodes to
      unfold summaries in graph. *)
  Definition central (H:℘ A) (P:℘(A->B)) : Prop :=
    forall α β, α ∉ H -> β ∉ H ->
    forall ν, ν ∈ P -> swap α β ν ∈ P
  .

  (* Finite permutations presented as lists of swap *)
  Definition permutation : Type := list (A*A).

  Definition apply_permutation (p:permutation) (f:A->B) : A->B :=
    List.fold_right (fun αβ g => swap (fst αβ) (snd αβ) g) f p
  .
  Local Coercion apply_permutation : permutation >-> Funclass.

  Definition permutation_not_in (p:permutation) (H:℘ A) : Prop :=
    List.Forall (fun αβ => fst αβ ∉ H /\ snd αβ ∉ H) p
  .

  Lemma permutation_not_in_decreasing p H₁ H₂ :
    sub (Γ:=[A]) H₁ H₂ -> permutation_not_in p H₂ -> permutation_not_in p H₁.
  Proof.
    intros h; simpl in h.
    apply List.Forall_impl.
    firstorder.
  Qed.

  Lemma central_permutation H P : central H P ->
    forall (p:permutation) (f:A->B), f ∈ P -> permutation_not_in p H ->
    p f ∈ P.
  Proof.
    intros h₁ p f h₂ h₃.
    induction p as [ | [α β] p hp ].
    - easy.
    - simpl.
      apply h₁.
      * unfold permutation_not_in in h₃.
        apply List.Forall_inv in h₃; simpl in h₃.
        firstorder.
      * unfold permutation_not_in in h₃.
        apply List.Forall_inv in h₃; simpl in h₃.
        firstorder.
      * apply hp.
        unfold permutation_not_in in h₃ |- *.
        now inversion h₃.
  Qed.

End Valuation.

(** Notations *)
Require compcert.common.Values.

Instance positive_eqdec : EqDec positive eq.
Proof. exact Pos.eq_dec. Qed.

Notation "p '@' ν" := (apply_permutation p ν) (at level 5).

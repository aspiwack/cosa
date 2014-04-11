Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Coq.Setoids.Setoid.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Cosa.Lib.Axioms.
Require Import Cosa.Lib.Algebra.
Require Import Cosa.Lib.Tactics.
Require Import Cosa.Lib.Finite.
Require Import Cosa.Lib.MapReduce.

Open Scope list_scope.

Local Ltac crush ::=
  simpl in *;
  solve [
      reflexivity |
      intuition eauto |
      firstorder eauto
    ]
.

(** n-ary relations as complete lattices. *)

Definition rel (Γ:list Type) : Type :=
  List.fold_right (fun A T => A -> T) Prop Γ
.

(** pointwise impliciation (aka sub-relation). *)
Fixpoint sub {Γ:list Type} : rel Γ -> rel Γ -> Prop :=
  match Γ with
  | [] => fun p q => p -> q
  | A::Γ => fun p q => forall x:A, sub (p x) (q x)
  end
.

Instance sub_preorder Γ : PreOrder (@sub Γ).
Proof.
  split; unfold Reflexive,Transitive.
  - by induction Γ.
  - by induction Γ.
Qed.

Lemma sub_cons {A Γ} : forall p q, sub (Γ:=A::Γ) p q = forall x, sub (p x) (q x).
Proof. reflexivity. Qed.

Lemma sub_one {A} : forall p q, sub (Γ:=[A]) p q = forall x, p x -> q x.
Proof. reflexivity. Qed.

(** Pointwise logical equivalence. *)
Fixpoint equiv {Γ:list Type} : rel Γ -> rel Γ -> Prop :=
  match Γ with
  | [] => fun p q => p <-> q
  | A::Γ => fun p q => forall x:A, equiv (p x) (q x)
  end
.

Instance equiv_equivalence Γ : Equivalence (@equiv Γ).
Proof.
  split; unfold Reflexive, Symmetric, Transitive.
  - by induction Γ.
  - by induction Γ.
  - by induction Γ.
Qed.

Instance sub_antisymmetric_equiv Γ : Antisymmetric (rel Γ) equiv sub.
Proof.
  unfold Antisymmetric.
  by induction Γ.
Qed.

(** equivalence is, in fact, equality thanks to the extensionality
    axioms of [Coq.Lib.Axioms]. *)
Lemma equiv_eq Γ (p q:rel Γ) : equiv p q -> p=q.
Proof.
  induction Γ as [ | A Γ hΓ ]; simpl in *.
  - apply prop_extensionality.
  - intros h₁.
    by extensionality x.
Qed.

Instance sub_antisymmetric_eq Γ : Antisymmetric (rel Γ) eq sub.
Proof.
  unfold Antisymmetric.
  intros **.
  apply equiv_eq.
  by apply sub_antisymmetric_equiv.
Qed.

Lemma eq_equiv Γ (p q:rel Γ) : p=q -> equiv p q.
Proof.
  intros <-.
  reflexivity.
Qed.


(** Tactics to convert betwwen [eq] and [equiv]. From there on, we
    prefer refering to equalitity rather than equivalence. *)

Ltac cast_to_type A :=
  lazymatch type of A with
  | Type => constr:(A)
  | _ => constr:(A:Type)
  end
.

Ltac push_rel A Γ k :=
  let A := cast_to_type A in
  k (A::Γ)
.

Ltac reify c k:=
  lazymatch c with
  | Prop => k (@nil Type)
  | ?A -> ?T =>
      let k' T' := push_rel A T' k in
      reify T k'
  | rel ?Γ => k Γ
  | _ => fail "Not a relation"
  end
.

Ltac equiv_eq_concl :=
  lazymatch goal with
  | |- ?l = _ =>
      let k Γ := (apply (equiv_eq Γ)) in
      let T := type of l in
      reify T k; simpl
  end
.

Ltac equiv_eq_hyp h :=
  lazymatch type of h with
  | ?l = _ =>
    let k Γ := (apply (eq_equiv Γ) in h) in
      let T := type of l in
      reify T k; simpl in h
  end
.

Ltac equiv_eq_hyps :=
  rewrite_defs;
  repeat match goal with
  | h:_ = _ |- _ => equiv_eq_hyp h
  end
.

Ltac equiv_eq := equiv_eq_hyps; try equiv_eq_concl.


Lemma double_sub Γ (p q:rel Γ) : sub p q -> sub q p -> p=q.
Proof.
  intros **.
  equiv_eq.
  by induction Γ.
Qed.

Ltac double_sub :=
  lazymatch goal with
  | |- ?l = _ =>
      let k Γ := (apply (double_sub Γ)) in
      let T := type of l in
      reify T k; simpl
  end
.


(** Top. *)
Fixpoint top {Γ} : rel Γ :=
  match Γ with
  | [] => True
  | A::Γ => fun _ => top
end.

Lemma top_is_top Γ : forall p:rel Γ, sub p top.
Proof.
  by induction Γ.
Qed.

(** Empty relation *)
Fixpoint bottom {Γ} : rel Γ :=
  match Γ with
  | [] => False
  | A::Γ => fun _ => bottom
  end
.

Lemma bottom_is_bottom Γ : forall p:rel Γ, sub bottom p.
Proof.
  by induction Γ.
Qed.

(** Binary join *)
Fixpoint join {Γ} : rel Γ -> rel Γ -> rel Γ :=
  match Γ with
  | [] => fun p q => p \/ q
  | A::Γ => fun p q x => join (p x) (q x)
  end
.

Instance join_associative Γ : Associative (@eq (rel Γ)) join.
Proof.
  unfold Associative; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance join_commutative Γ : Commutative (@eq (rel Γ)) join.
Proof.
  unfold Commutative; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance join_bottom_neutral Γ : LeftNeutral (@eq (rel Γ)) join bottom.
Proof.
  unfold LeftNeutral; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance join_monotone Γ : Proper (sub ==> sub ==> sub) (@join Γ).
Proof.
  autounfold; intros **.
  by induction Γ.
Qed.

(** Arbitrary join *)

Fixpoint Join {Γ I} : (I->rel Γ) -> rel Γ :=
  match Γ with
  | [] => fun p => exists i, p i
  | A::Γ => fun p x => Join (fun i => p i x)
  end
.

Lemma Join_supremum Γ I (p:I->rel Γ) (q:rel Γ) : (forall i, sub (p i) q) <-> sub (Join p) q.
Proof.
  by induction Γ.
Qed.

Lemma Join_sup Γ I (p:I->rel Γ) : forall i, sub (p i) (Join p).
Proof.
  by rewrite Join_supremum.
Qed.
Lemma Join_sup_sig Γ (P:rel Γ->Prop) p : P p -> sub p (Join (fun q:{q|P q} => proj1_sig q)).
Proof.
  intros h.
  change p with ((fun q:{q|P q} => proj1_sig q) (exist _ p h)).
  apply Join_sup.
Qed.

Lemma Join_intro {Γ I} {p:I->rel Γ} {q} : forall i, sub q (p i) -> sub q (Join p).
Proof.
  intros **.
  simplify_transitivity.
  apply Join_sup.
Qed.

Lemma Join_unique Γ I (p:I->rel Γ) (q:rel Γ) :
  (forall (r:rel Γ), (forall i, sub (p i) r) <-> sub q r) -> q = Join p.
Proof.
  intros h.
  double_sub.
  - apply h.
    apply Join_sup.
  - rewrite <- Join_supremum.
    by apply h.
Qed.

Lemma Join_member Γ I (p:I->rel Γ) i : (forall j, sub (p j) (p i)) -> p i = Join p.
Proof.
  intro h.
  apply Join_unique.
  intro r.
  split.
  - crush.
  - intros **.
    solve_transitivity.
Qed.

Lemma Join_increasing Γ I : Proper (@sub (I::Γ) ==> sub) Join.
Proof.
  autounfold; simpl.
  intros p q p_sub_q.
  rewrite <- Join_supremum.
  intros i.
  by apply Join_intro with i.
Qed.

Lemma Join_associative Γ I J (f:I->J->rel Γ) :
  Join (fun i:I => Join (fun j:J => f i j)) = Join (fun α:I*J => f (fst α) (snd α)).
Proof.
  double_sub.
  - rewrite <- Join_supremum; intros i.
    rewrite <- Join_supremum; intros j.
    set (α := (i,j)).
    change i with (fst α).
    change j with (snd α).
    generalize α; clear i j α.
    by rewrite Join_supremum.
  - rewrite <- Join_supremum; intros [ i j ].
    revert j; rewrite Join_supremum.
    revert i; rewrite Join_supremum.
    reflexivity.
Qed.

Lemma Join_empty_set Γ (f:Empty_set -> rel Γ) : Join f = bottom.
Proof.
  double_sub.
  - induction Γ as [ | A Γ hΓ ]; simpl in *.
    + (* Γ = [] *)
      intros [ [] _ ].
    + (* Γ = A::Γ *)
      eauto.
  - apply bottom_is_bottom.
Qed.

Lemma bottom_is_Join Γ : bottom = Join (fun i:Empty_set => match i return rel Γ with end).
Proof.
  symmetry; apply Join_empty_set.
Qed.

Lemma Join_unit Γ (f:unit -> rel Γ) : Join f = f tt.
Proof.
  equiv_eq.
  induction Γ as [ | A Γ hΓ ]; simpl in *.
  - (* Γ = [] *)
    split.
    + intros [ [] ? ]; eauto.
    + decompose_goal; eauto.
  - (* Γ = A::Γ *)
    intros x.
    by specialize (hΓ (fun i => f i x)).
Qed.

Lemma Join_of_option Γ A (f:option A -> rel Γ) :
  Join f = join (f None) (Join (fun i => f (Some i))).
Proof.
  equiv_eq; revert f.
  induction Γ as [ | B Γ hΓ ]; simpl in *.
  - (* Γ = [] *)
    intros f.
    split.
    + intros [ [ x | ] ? ].
      * by right.
      * by left.
    + intros [ h | [ x h ]].
      * by exists None.
      * by exists (Some x).
  - (* Γ = B::Γ *)
    intros f x.
    apply hΓ.
Qed.

Lemma Join_of_finite Γ n (f:fin n -> rel Γ) : Join f = list_reduce join bottom (listify f).
Proof.
  induction n as [ | n hn ].
  - (* n = 0 *)
    apply Join_empty_set.
  - (* n = S n *)
    change (listify f) with (f None::listify (fun i => f (Some i))).
    rewrite list_reduce_cons; [ | typeclasses eauto ..].
    simpl in *.
    rewrite (Join_of_option Γ _ f).
    by rewrite hn.
Qed.

Lemma Join_of_list Γ (l:list (rel Γ)) :
  list_reduce join bottom l = Join (access l).
  rewrite Join_of_finite.
  rewrite listify_access.
  reflexivity.
Qed.
    
(** Binary meet. *)
Fixpoint meet {Γ} : rel Γ -> rel Γ -> rel Γ :=
  match Γ with
  | [] => fun p q => p /\ q
  | A::Γ => fun p q x => meet (p x) (q x)
  end
.

Instance meet_associative Γ : Associative (@eq (rel Γ)) meet.
Proof.
  unfold Associative; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance meet_commutative Γ : Commutative (@eq (rel Γ)) meet.
Proof.
  unfold Commutative; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance meet_top_neutral Γ : LeftNeutral (@eq (rel Γ)) meet top.
Proof.
  unfold LeftNeutral; intros **.
  equiv_eq.
  by induction Γ.
Qed.

Instance meet_monotone Γ : Proper (sub ==> sub ==> sub) (@meet Γ).
Proof.
  autounfold; intros **.
  by induction Γ.
Qed.

Lemma meet_infimum_intro Γ (p q r:rel Γ) : sub r p -> sub r q -> sub r (meet p q).
Proof.
  by induction Γ.
Qed.

Lemma meet_infimum_elim_left Γ (p q r:rel Γ) : sub r (meet p q) -> sub r p.
Proof.
  by induction Γ.
Qed.

Lemma meet_infimum_elim_right Γ (p q r:rel Γ) : sub r (meet p q) -> sub r q.
Proof.
  by induction Γ.
Qed.

Lemma meet_sub_left Γ (p q:rel Γ) : sub (meet p q) p.
Proof.
  by induction Γ.
Qed.

Lemma meet_sub_right Γ (p q:rel Γ) : sub (meet p q) q.
Proof.
  by induction Γ.
Qed.

(** Arbitrary meet. *)

Fixpoint Meet {Γ I} : (I->rel Γ) -> rel Γ :=
  match Γ with
  | [] => fun p => forall i, p i
  | A::Γ => fun p x => Meet (fun i => p i x)
  end
.

Lemma Meet_infimum Γ I (p:I->rel Γ) (q:rel Γ) : (forall i, sub q (p i)) <-> sub q (Meet p).
Proof.
  by induction Γ.
Qed.

Lemma Meet_sub Γ I (p:I->rel Γ) : forall i, sub (Meet p) (p i).
Proof.
  by rewrite Meet_infimum.
Qed.
Lemma Meet_sub_sig Γ (P:rel Γ->Prop) p : P p -> sub (Meet (fun q:{q|P q} => proj1_sig q)) p.
Proof.
  intros h.
  change p with ((fun q:{q|P q} => proj1_sig q) (exist _ p h)).
  apply Meet_sub.
Qed.

Lemma Meet_intro_left Γ I (p:I->rel Γ) q : forall i, sub (p i) q -> sub (Meet p) q.
Proof.
  intros **.
  simplify_transitivity.
  apply Meet_sub.
Qed.

Lemma Meet_unique Γ I (p:I->rel Γ) (q:rel Γ) :
  (forall (r:rel Γ), (forall i, sub r (p i)) <-> sub r q) -> q = Meet p.
Proof.
  intros h.
  double_sub.
  - rewrite <- Meet_infimum.
    by apply h.
  - apply h.
    apply Meet_sub.
Qed.

Lemma Meet_member Γ I (p:I->rel Γ) i : (forall j, sub (p i) (p j)) -> p i = Meet p.
Proof.
  intro h.
  apply Meet_unique.
  intro r.
  split.
  - crush.
  - intros **.
    solve_transitivity.
Qed.

Lemma Meet_increasing Γ I : Proper (@sub (I::Γ) ==> sub) Meet.
Proof.
  autounfold; simpl.
  intros p q p_sub_q.
  rewrite <- Meet_infimum.
  intros i.
  by apply Meet_intro_left with i.
Qed.

Lemma Meet_associative Γ I J (f:I->J->rel Γ) :
  Meet (fun i:I => Meet (fun j:J => f i j)) = Meet (fun α:I*J => f (fst α) (snd α)).
Proof.
  double_sub.
  - rewrite <- Meet_infimum; intros [ i j ].
    revert j; rewrite Meet_infimum.
    revert i; rewrite Meet_infimum.
    reflexivity.
  - rewrite <- Meet_infimum; intros i.
    rewrite <- Meet_infimum; intros j.
    set (α := (i,j)).
    change i with (fst α).
    change j with (snd α).
    generalize α; clear i j α.
    by rewrite Meet_infimum.
Qed.

Lemma Meet_empty_set Γ (f:Empty_set -> rel Γ) : Meet f = top.
Proof.
  double_sub.
  - apply top_is_top.
  - induction Γ as [ | A Γ hΓ ]; simpl in *.
    + (* Γ = [] *)
      intros [ [] _ ].
    + (* Γ = A::Γ *)
      eauto.
Qed.

Lemma top_is_Meet Γ : top = Meet (fun i:Empty_set => match i return rel Γ with end).
Proof.
  symmetry; apply Meet_empty_set.
Qed.

Lemma Meet_unit Γ (f:unit -> rel Γ) : Meet f = f tt.
Proof.
  equiv_eq.
  induction Γ as [ | A Γ hΓ ]; simpl in *.
  - (* Γ = [] *)
    split.
    + eauto.
    + intros ? []; eauto.
  - (* Γ = A::Γ *)
    intros x.
    by specialize (hΓ (fun i => f i x)).
Qed.

Lemma Meet_of_option Γ A (f:option A -> rel Γ) :
  Meet f = meet (f None) (Meet (fun i => f (Some i))).
Proof.
  equiv_eq; revert f.
  induction Γ as [ | B Γ hΓ ]; simpl in *.
  - (* Γ = [] *)
    intros f.
    split.
    + intros h.
      split; eauto.
    + intros [ h₁ h₂ ].
      intros [ x | ]; eauto.
  - (* Γ = B::Γ *)
    intros f x.
    apply hΓ.
Qed.

Lemma Meet_of_finite Γ n (f:fin n -> rel Γ) : Meet f = list_reduce meet top (listify f).
Proof.
  induction n as [ | n hn ].
  - (* n = 0 *)
    apply Meet_empty_set.
  - (* n = S n *)
    change (listify f) with (f None::listify (fun i => f (Some i))).
    rewrite list_reduce_cons; [ | typeclasses eauto ..].
    simpl in *.
    rewrite (Meet_of_option Γ _ f).
    by rewrite hn.
Qed.

Lemma Meet_of_list Γ (l:list (rel Γ)) :
  list_reduce meet top l = Meet (access l).
  rewrite Meet_of_finite.
  rewrite listify_access.
  reflexivity.
Qed.

(** Pointwise application (right adjoint to binary [meet]). *)
Fixpoint arrow {Γ} : rel Γ -> rel Γ -> rel Γ :=
  match Γ with
  | [] => fun p q => p -> q
  | A::Γ => fun p q x => arrow (p x) (q x)
  end
.

Lemma meet_arrow_adjunction Γ :
  forall (p q r:rel Γ), sub (meet p q) r <-> sub p (arrow q r).
Proof.
  induction Γ as [|A Γ h].
  - simpl.
    firstorder.
  - simpl.
    firstorder.
Qed.

(** Least fixed point of increasing functions. *)

Definition postfixed_points {Γ} (F:rel Γ->rel Γ) (p:rel Γ) : Prop := sub (F p) p.

Lemma postfixed_points_apply Γ (F:rel Γ->rel Γ) (p:rel Γ) :
  Proper (sub==>sub) F -> postfixed_points F p -> postfixed_points F (F p).
Proof.
  autounfold; unfold postfixed_points.
  crush.
Qed.

Definition lfp {Γ} (F:rel Γ->rel Γ) : rel Γ :=
  Meet (fun p : { p | postfixed_points F p } => proj1_sig p)
.


Lemma lfp_sub_postfixed_point Γ (F:rel Γ->rel Γ) :
  forall p, postfixed_points F p -> sub (lfp F) p.
Proof.
  intros **; unfold lfp.
  by apply Meet_sub_sig.
Qed.

Lemma lfp_postfixed_point Γ (F:rel Γ->rel Γ) {incr:Proper (sub==>sub) F} :
  postfixed_points F (lfp F).
Proof.
  unfold postfixed_points.
  apply -> Meet_infimum.
  intros [ p pfp ]; simpl.
  transitivity (F p).
  - apply incr.
    now apply lfp_sub_postfixed_point.
  - apply pfp.
Qed.

Lemma lfp_fixed_point Γ (F:rel Γ->rel Γ) {incr:Proper (sub==>sub) F} :
  F (lfp F) = lfp F.
Proof.
  double_sub.
  - now eapply lfp_postfixed_point.
  - apply lfp_sub_postfixed_point.
    apply postfixed_points_apply, lfp_postfixed_point; eauto.
Qed.

Section InductionPrinciple.

  Context Γ (F:rel Γ->rel Γ) {incr:Proper (sub==>sub) F}.

  Local Notation inductive P := (forall (p:rel Γ), sub p (lfp F) -> sub p P -> sub (F p) P).

  Lemma inductive_meet (P Q:rel Γ) : inductive P -> inductive Q -> inductive (meet P Q).
  Proof.
    intros ind_P ind_Q p sub_lfp sub_PQ.
    apply meet_infimum_intro.
    - apply ind_P.
      + assumption.
      + apply meet_infimum_elim_left in sub_PQ.
        assumption.
    - apply ind_Q.
      + assumption.
      + apply meet_infimum_elim_right in sub_PQ.
        assumption.
  Qed.

  Lemma inductive_lfp : inductive (lfp F).
  Proof.
    intros p h _.
    apply incr in h.
    rewrite lfp_fixed_point in h; [|typeclasses eauto].
    apply h.
  Qed.

  Lemma inductive_postfixed_point (P:rel Γ) :
    sub P (lfp F) -> inductive P -> postfixed_points F P.
  Proof.
    unfold postfixed_points; firstorder.
  Qed.

  Lemma lfp_ind (P:rel Γ) : inductive P -> sub (lfp F) P.
  Proof.
    intros ind.
    assert (inductive (meet P (lfp F))) as ind'.
    { apply inductive_meet.
      - assumption.
      - apply inductive_lfp. }
    apply inductive_postfixed_point in ind'; [|apply meet_sub_right].
    transitivity (meet P (lfp F)).
    - now apply lfp_sub_postfixed_point.
    - apply meet_sub_left.
  Qed.

End InductionPrinciple.
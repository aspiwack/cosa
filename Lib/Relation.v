(*** A small library of relations ***)
Require Import Cosa.Lib.Axioms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Cosa.Lib.CompleteLattice.
Require Import Cosa.Lib.Predicate.
Require Import Cosa.Lib.Algebra.
Require Import Cosa.Lib.Tactics.
Import List.ListNotations.


(** Binary relations *)

(** Equality for relations. *)
Definition equiv {A B:Type} (R Q:A->B->Prop) := forall a b, R a b <-> Q a b.
Notation "R ⇔ Q" := (equiv R Q) (at level 70).

Instance equiv_equivalence A B : Equivalence (@equiv A B).
Proof.
  split; unfold Reflexive,Symmetric,Transitive,equiv.
  - intros **.
    reflexivity.
  - intros **.
    symmetry; auto.
  - intros **.
    etransitivity; eauto.
Qed.

Lemma equiv_eq A B : forall (R Q:A->B->Prop), R⇔Q -> R=Q.
Proof.
  intros R Q h.
  extensionality x.
  extensionality y.
  apply prop_extensionality.
  easy.
Qed.

(** Composition of relations. Same as monadic extension+functional
    composition*)
Definition comp (A B C:Type) (R:A->B->Prop) (Q:B->C->Prop) : A->C->Prop :=
  fun a c => exists b, R a b /\ Q b c
.
Notation "R • Q" := (comp _ _ _ R Q) (at level 5,right associativity).

Lemma comp_associative A B C D (R:A->B->Prop) (Q:B->C->Prop) (P:C->D->Prop) :
                    (R•Q)•P ⇔ R•(Q•P).
Proof.
  unfold comp,equiv.
  firstorder.
Qed.

Lemma comp_eq_neutral A B (R:A->B->Prop) : eq•R ⇔ R /\ R•eq ⇔ R.
Proof.
  unfold comp,equiv.
  firstorder subst; easy.
Qed.


(** ternary relations *)


(** Binary monadic extension.  It cannot be defined in term of unary
    extension alone: it would require functional action or unit, and
    these involve equality. It would be a simple generalisation to
    define variadic extension taking a list of types as arguments. *)
Definition extension2 {A B C} (R:A->B->℘ C) : ℘ A -> ℘ B -> ℘ C :=
  fun pa pb z => exists x y, x∈pa /\ y∈pb /\ R x y z
.

(** By a general property of complete lattices, extension2 is actually
    continuous. In particular it is increasing *)
Instance extension2_increasing A B C (R:A->B->℘ C) :
  Proper (Subset==>Subset==>Subset) (extension2 R).
Proof.
  unfold Proper, respectful.
  intros p₁ p₂ p₁_sub_p₂ q₁ q₂ q₁_sub_q₂.
  unfold extension2.
  intros x; simpl.
  unfold Subset,sub in *.
  decompose_goal; eauto.
Qed.

(* [extension2] is also continuous in its second argument. *)
Lemma extension2_continuous_2 A B C I (R:A->B->℘ C) x (f:I->℘ B) :
  extension2 R x (Join (Γ:=[B]) f) = Join (Γ:=[C]) (fun i => extension2 R x (f i)).
Proof.
  double_sub.
  - intros c.
    unfold extension2.
    decompose_goal; eauto.
  - intros c.
    unfold extension2.
    decompose_goal; eauto.
Qed.

(** On associativity and commutativity of binary extension. *)
Section ACFacts.

  Context {A} (r:A->A->A->Prop).
  Context (e:A->Prop).

  Lemma associative_rel : Associative eq (extension2 r) <-> (forall a₁ a₂ a₃ x,
      (exists a₁₂, r a₁ a₂ a₁₂ /\ r a₁₂ a₃ x) <-> (exists a₂₃, r a₁ a₂₃ x /\ r a₂ a₃ a₂₃)).
  Proof.
    split.
    - intro assoc.
      intros *.
      specialize (assoc (singleton a₁) (singleton a₂) (singleton a₃)).
      apply Predicate.predicate_equality in assoc.
      unfold Predicate.equiv,extension2, singleton in assoc.
      specialize (assoc x).
      split.
      + intros [ a₁₂ [ rl rr ]].
        destruct assoc as [ assoc _ ].
        prove_hyp assoc.
        { decompose_concl; eauto. }
        decompose_hyp assoc.
        decompose_concl;eauto.
      + intros [ a₂₃ [ rl rr ]].
        destruct assoc as [ _ assoc ].
        prove_hyp assoc.
        { decompose_concl; eauto. }
        decompose_hyp assoc.
        decompose_concl;eauto.
    - intros h.
      unfold Associative, extension2.
      intros p₁ p₂ p₃.
      apply Predicate.equiv_eq; intros x.
      split.
      + intros [ a₁ [ a₂ [ [ a₃ [ a₄ [ ? [ ? ? ]]]] [ ? ? ]]]].
        specialize (h a₃ a₄ a₂ x).
        destruct h as [ h _ ].
        prove_hyp h.
        { decompose_concl; eauto. }
        decompose_hyp h.
        decompose_concl; eauto.
      + intros [ a₁ [ a₂ [ ? [ [ a₃ [ a₄ [ ? [ ? ? ]]]] ? ]]]].
        specialize (h a₁ a₃ a₄ x).
        destruct h as [ _ h ].
        prove_hyp h.
        { decompose_concl; eauto. }
        decompose_hyp h.
        decompose_concl; eauto.
  Qed.

  Lemma commutative_rel : Commutative eq (extension2 r) <->
                          (forall a₁ a₂ x, r a₁ a₂ x -> r a₂ a₁ x).
  Proof.
    split.
    - intros comm.
      intros a₁ a₂ x h.
      specialize (comm (singleton a₁) (singleton a₂)).
      apply Predicate.predicate_equality in comm.
      unfold Predicate.equiv, extension2, singleton in comm.
      specialize (comm x).
      destruct comm as [ comm _ ].
      prove_hyp comm.
      { decompose_concl; eauto. }
      decompose_hyp comm.
      assumption.
    - intros h.
      unfold Commutative,extension2.
      intros p₁ p₂.
      apply Predicate.equiv_eq; intro x.
      split; intro h₁; decompose_hyp h₁; decompose_concl; eauto.
  Qed.

  (** spiwack: I don't have a good characterisation of neutrality
      though.  There are useful consequences though. However, I'm not
      sure whether their conjunction implies neutrality. *)
  Lemma left_neutral_rel_eq : LeftNeutral eq (extension2 r) e ->
                                  forall n a a', n∈e -> r n a a' -> a=a'.
  Proof.
    unfold LeftNeutral, extension2.
    intros neutral.
    intros n a a' h₁ h₂.
    specialize (neutral (singleton a)).
    apply Predicate.predicate_equality in neutral;
      unfold Predicate.equiv, singleton in neutral.
    specialize (neutral a').
    symmetry.
    apply neutral.
    { decompose_concl; eauto. }
  Qed.

  Corollary left_neutral_rel_compat : LeftNeutral eq (extension2 r) e ->
                                  forall n a a', n∈e -> r n a a' -> r n a a.
  Proof.
    intros neutral.
    intros n a a' h₁ h₂.
    eapply left_neutral_rel_eq in neutral; eauto.
    now destruct neutral.
  Qed.


  Lemma left_neutral_rel_exists : LeftNeutral eq (extension2 r) e ->
                              forall a, exists n, n∈e /\ r n a a.
  Proof.
    unfold LeftNeutral, extension2.
    intros neutral.
    intros a.
    specialize (neutral (singleton a)).
    apply Predicate.predicate_equality in neutral;
      unfold Predicate.equiv, singleton in neutral.
    specialize (neutral a).
    destruct neutral as [ _ neutral ].
    prove_hyp neutral.
    { trivial. }
    decompose_hyp neutral; decompose_concl;eauto.
  Qed.

End ACFacts.


(* Ternary equality, equivalent to the pair of two (binary) equalities. *)
Inductive teq {A} (x:A) : A -> A -> Prop :=
| teq_refl : teq x x x
.

Lemma teq_spec A (x y z:A) : teq x y z <-> x=y /\ x=z.
Proof.
  split.
  - intros [].
    easy.
  - intros [ <- <- ].
    constructor.
Qed.

Instance teq_assoc A : Associative eq (extension2 (@teq A)).
Proof.
  apply associative_rel.
  intros a₁ a₂ a₃ x.
  split.
  - intros [ a₁₂ [ [] [] ] ]; clear.
    decompose_concl; constructor.
  - intros [ a₂₃ [ [] [] ] ]; clear.
    decompose_concl; constructor.
Qed.

Instance teq_comm A : Commutative eq (extension2 (@teq A)).
Proof.
  apply commutative_rel.
  intros a₁ a₂ x [].
  constructor.
Qed.

Instance teq_top_neutral A : LeftNeutral eq (extension2 (@teq A)) (fun _ => True).
Proof.
  unfold LeftNeutral, extension2.
  intros p.
  apply Predicate.equiv_eq; intro x.
  split.
  - intros [ ? [ ? [ _ [ ? h ]]]].
    now destruct h.
  - intros h; decompose_concl; eauto.
    constructor.
Qed.

(** On pairing up associative and commutative relations. *)
Section PairUp.

  Context {A B:Type}.
  Context (r₁:A->A->A->Prop).
  Context{r₁_assoc:Associative eq (extension2 r₁)}{r₁_comm:Commutative eq (extension2 r₁)}.
  Context (e₁:A->Prop) {e₁_neutral:LeftNeutral eq (extension2 r₁) e₁}.
  Context (r₂:B->B->B->Prop).
  Context{r₂_assoc:Associative eq (extension2 r₂)}{r₂_comm:Commutative eq (extension2 r₂)}.
  Context (e₂:B->Prop) {e₂_neutral:LeftNeutral eq (extension2 r₂) e₂}.


  Definition pair (x y z:A*B) : Prop :=
    r₁ (fst x) (fst y) (fst z) /\ r₂ (snd x) (snd y) (snd z).

  Global Instance pair_assoc : Associative eq (extension2 pair).
  Proof.
    apply associative_rel.
    generalize r₁_assoc; intro r₁_assoc'.
    generalize r₂_assoc; intro r₂_assoc'.
    rewrite associative_rel in r₁_assoc'; rewrite associative_rel in r₂_assoc'.
    intros [a₁ b₁] [a₂ b₂] [a₃ b₃] [x y].
    specialize (r₁_assoc' a₁ a₂ a₃ x).
    specialize (r₂_assoc' b₁ b₂ b₃ y).
    split.
    - intros [ [a₁₂ b₁₂] h ]; unfold pair in h; simpl in h; decompose_hyp h.
      destruct r₁_assoc' as [ r₁_assoc' _ ].
      prove_hyp r₁_assoc'.
      { decompose_concl; eauto. }
      decompose_hyp r₁_assoc'.
      destruct r₂_assoc' as [ r₂_assoc' _ ].
      prove_hyp r₂_assoc'.
      { decompose_concl; eauto. }
      decompose_hyp r₂_assoc'.
      eexists. instantiate (1:=(_,_)).
      unfold pair; simpl.
      decompose_concl; eauto.
    - intros [ [a₂₃ b₂₃] h ]; unfold pair in h; simpl in h; decompose_hyp h.
      destruct r₁_assoc' as [ _ r₁_assoc' ].
      prove_hyp r₁_assoc'.
      { decompose_concl; eauto. }
      decompose_hyp r₁_assoc'.
      destruct r₂_assoc' as [ _ r₂_assoc' ].
      prove_hyp r₂_assoc'.
      { decompose_concl; eauto. }
      decompose_hyp r₂_assoc'.
      eexists. instantiate (1:=(_,_)).
      unfold pair; simpl.
      decompose_concl; eauto.
  Qed.

  Global Instance pair_comm : Commutative eq (extension2 pair).
  Proof.
    generalize r₁_comm; intro r₁_comm'.
    generalize r₂_comm; intro r₂_comm'.
    rewrite commutative_rel in r₁_comm'.
    rewrite commutative_rel in r₂_comm'.
    apply commutative_rel.
    intros [a₁ b₁] [a₂ b₂] [x y]; unfold pair; simpl.
    intros [h₁ h₂].
    split; eauto.
  Qed.

  Global Instance pair_left_neutral : LeftNeutral eq (extension2 pair) (Predicate.pair e₁ e₂).
  Proof.
    unfold LeftNeutral, extension2, pair, Predicate.pair.
    intros p.
    apply Predicate.equiv_eq; intros [a₁ b₁]; simpl.
    split.
    - intros [ [n m] [ [a₂ b₂]  h ]]; decompose_hyp h; simpl in *.
      generalize (left_neutral_rel_eq _ _ e₁_neutral); intro e₁_neutral'.
      generalize (left_neutral_rel_eq _ _ e₂_neutral); intro e₂_neutral'.
      rewrite <- (e₁_neutral' n a₂ a₁);trivial.
      rewrite <- (e₂_neutral' m b₂ b₁);trivial.
    - intros h.
      generalize (left_neutral_rel_exists _ _ e₁_neutral a₁); intros [n e₁_neutral'].
      generalize (left_neutral_rel_exists _ _ e₂_neutral b₁); intros [m e₂_neutral'].
      decompose_hyp e₁_neutral'; decompose_hyp e₂_neutral'.
      exists (n,m). exists (a₁,b₁).
      decompose_concl; eauto.
  Qed.

End PairUp.


(** Associativity and commutativity of disjoint union of predicates *)
Instance disjoint_union_assoc A : Associative eq (extension2 (@disjoint_union A)).
Proof.
  apply associative_rel.
  unfold disjoint_union.
  intros a₁ a₂ a₃ x.
  split.
  - intros h; decompose_hyp h.
    repeat match goal with
    | H:_ = _ |- _ => apply predicate_equality in H; unfold Predicate.equiv in H
    end.
    exists (a₂∪a₃).
    decompose_concl; apply Predicate.equiv_eq; intro; firstorder.
  - intros h; decompose_hyp h.
    predicate_equality_hyps.
    exists (a₁∪a₂).
    decompose_concl; apply Predicate.equiv_eq; intro; firstorder.
Qed.

Instance disjoint_union_comm A : Commutative eq (extension2 (@disjoint_union A)).
Proof.
  apply commutative_rel.
  unfold disjoint_union.
  intros a₁ a₂ x.
  intros [h₁ h₂].
  predicate_equality_hyps.
  decompose_concl; apply Predicate.equiv_eq; intro; firstorder.
Qed.

Instance disjoint_union_empty_neutral A : LeftNeutral eq (extension2 (@disjoint_union A)) (eq ∅).
Proof.
  unfold LeftNeutral, extension2, disjoint_union.
  intro P.
  apply Predicate.equiv_eq; intro q.
  split.
  - intros h; decompose_hyp h; predicate_equality_hyps.
    now rewrite left_neutrality.
  - intros h.
    decompose_concl; eauto.
    + reflexivity.
    + apply Predicate.equiv_eq; intro x.
      firstorder.
    + apply Predicate.equiv_eq; intro x.
      firstorder.
Qed.

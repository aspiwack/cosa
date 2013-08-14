Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Cosa.Lib.Axioms.
Require Import Cosa.Lib.Algebra.
Require Import Cosa.Lib.CompleteLattice.
Import List.ListNotations.

Reserved Notation "P1 ⊆ P2" (at level 20).
Notation "x ∈ P" := (P x) (at level 19, only parsing).
Notation "x ∉ P" := (~x∈P) (at level 19, only parsing).
Notation "'℘' A" := (A -> Prop) (at level 0).
Reserved Notation "X ∩ Y" (at level 19).
Reserved Notation "X ∪ Y" (at level 19).
Notation "∅" := (fun _ => False).

Definition equiv {A} : ℘ A -> ℘ A -> Prop := @CompleteLattice.equiv [A].

Instance equiv_equivalence A : Equivalence (@equiv A).
Proof. exact (CompleteLattice.equiv_equivalence [A]). Qed.


Lemma equiv_eq A : forall (P Q:℘A), equiv P Q -> P=Q.
Proof. exact (CompleteLattice.equiv_eq [A]). Qed.


Lemma predicate_equality A : forall (P Q:℘ A), P=Q -> equiv P Q.
Proof. exact (CompleteLattice.eq_equiv [A]). Qed.

(*arnaud: supprimer cette tactique et les lemmes précédents, à terme. *)
Ltac predicate_equality_hyps :=
  repeat match goal with
  | H:_ = _ |- _ => apply predicate_equality in H; unfold equiv in H
  end
.


(** Inclusion ordering. *)
Definition Subset {A} : ℘ A -> ℘ A ->Prop := @CompleteLattice.sub [A].
Notation "p ⊆ q" := (Subset p q).

Instance subset_preorder {A} : PreOrder (@Subset A).
Proof. exact (CompleteLattice.sub_preorder [A]). Qed.
Instance subset_antisymmetric {A} : Antisymmetric _ eq (@Subset A).
Proof. exact (CompleteLattice.sub_antisymmetric_eq [A]). Qed.

Definition double_subset {A} (p q:℘ A) : p ⊆ q -> q ⊆ p -> p = q.
Proof. exact (CompleteLattice.double_sub [A] p q). Qed.

(** singleton with respect to [eq] *)
Definition singleton {A} (x:A) : ℘ A := fun x' => x' = x.

(** Pairing up predicates. *)
Definition pair {A B} (p:℘ A) (q:℘ B) : ℘(A*B) :=
  fun x => p (fst x) /\ q (snd x)
.


(** Binary union. *)
Definition union {A} : ℘ A -> ℘ A -> ℘ A := @CompleteLattice.join [A].
Notation "p ∪ q" := (union p q).

Instance union_assoc A : Associative eq (@union A).
Proof. exact (CompleteLattice.join_associative [A]). Qed.
Instance union_comm A : Commutative eq (@union A).
Proof. exact (CompleteLattice.join_commutative [A]). Qed.
Instance union_empty_neutral A : LeftNeutral eq (@union A) ∅.
Proof. exact (CompleteLattice.join_bottom_neutral [A]). Qed.

Instance union_increasing A : Proper (Subset==>Subset==>Subset) (@union A).
Proof. exact (CompleteLattice.join_monotone [A]). Qed.


(** Binary intersection. *)
Definition intersection {A} : ℘ A -> ℘ A -> ℘ A := @CompleteLattice.meet [A].
Notation "p ∩ q" := (intersection p q).

Instance intersection_assoc A : Associative eq (@intersection A).
Proof. exact (CompleteLattice.meet_associative [A]). Qed.
Instance intersection_comm A : Commutative eq (@intersection A).
Proof. exact (CompleteLattice.meet_commutative [A]). Qed.
Instance intersection_top_neutral A : LeftNeutral eq (@intersection A) (fun _ => True).
Proof. exact (CompleteLattice.meet_top_neutral [A]). Qed.

Instance intersection_increasing A : Proper (Subset==>Subset==>Subset) (@intersection A).
Proof. exact (CompleteLattice.meet_monotone [A]). Qed.



(** Disjoint union. *)
Definition disjoint_union {A} (p q:℘ A) : ℘ (℘ A) :=
  fun r => p∩q = ∅ /\ p∪q=r
.
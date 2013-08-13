Require Import Cosa.Lib.Header.
Require Import AST.
Require Import Memory.
Require Import Values.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Cosa.Lib.Predicate.
Require Import Cosa.Lib.Relation.

(** Concrete heap fragment are used as the concrete memory
    representation in the Cosa shape domain. A fragment is a Compcert
    C heap together with a predicate representing the memory currently
    accessible. It allows to reason separately on different fragment
    of the same heap, as in separation logic. *)

Definition fragment := (mem*℘ (block*Z.t))%type.

Definition star : fragment->fragment->fragment->Prop := Relation.pair teq disjoint_union.
Notation "h₁ ⋆ h₂ 'is' s" := (star h₁ h₂ s) (at level 15).

Definition estar := extension2 star.
Notation "h₁ ★ h₂" := (estar h₁ h₂) (at level 15).

Definition empty (h:fragment) : Prop := snd h = ∅.
Arguments empty h /.

Lemma empty_spec : empty = Predicate.pair (fun _ => True) (eq ∅).
Proof.
  apply Predicate.equiv_eq; intro h.
  unfold empty, Predicate.pair.
  firstorder.
Qed.

Instance star_assoc : Associative eq estar.
Proof.
  unfold estar,star; typeclasses eauto.
Qed.

Instance star_comm : Commutative eq estar.
Proof.
  unfold estar,star; typeclasses eauto.
Qed.

Corollary star_commutative_rel : forall h₁ h₂ s, h₁ ⋆ h₂ is s -> h₂ ⋆ h₁ is s.
Proof.
  intros h₁ h₂ s.
  apply commutative_rel.
  typeclasses eauto.
Qed.

Instance star_empty_neutral : LeftNeutral eq estar empty.
Proof.
  rewrite empty_spec.
  unfold estar,star; typeclasses eauto.
Qed.


Import ZArith. (* arnaud: y a-t-il un autre moyen de récupérer les notations de Z.t ? *)

(** [memory_range b off size] represents a contiguous zone of memory
    in block [b], starting at offset int and of size [size]. *)
Definition memory_range (b:block) (off:int) (chunk:memory_chunk) : (block*Z.t) -> Prop :=
  fun loc =>
    let '(b',off') := loc in
   (b' = b /\ Int.unsigned off <= off' /\ off' <= (Int.unsigned off)+(Memdata.size_chunk chunk))%Z
.

Definition valid (b:block) (off:int) (chunk:memory_chunk) (h:fragment) : Prop :=
  memory_range b off chunk ⊆ snd h
.


(** Lifts [Mem.loadv] to [fragment]. (spiwack:) I chose the semantics
    of [reads] to fail when accessling a zone of memory which isn't
    included in the accessible zone. I'm not sure whether it is the
    correct semantics. *)
Inductive reads (h:fragment) (chunk:memory_chunk) (b:block) (offs:int) (v:val) : Prop :=
| reads_intro :
    valid b offs chunk h ->
    Mem.loadv chunk (fst h) (Vptr b offs) = Some v ->
    reads h chunk b offs v
.

(** Variant of [read] taking the address as a value. *)
Definition readsv (h:fragment) (chunk: memory_chunk) (addr: val) (v:val) : Prop :=
  match addr with
  | Vptr b offs => reads h chunk b offs v
  | _ => False
  end
.


Lemma star_read_left h₁ h₂ s : h₁ ⋆ h₂ is s -> forall chunk b offs v,
                    reads h₁ chunk b offs v -> reads s chunk b offs v.
Proof.
  destruct h₁ as [ h₁ a₁ ].
  destruct h₂ as [ h₂ a₂ ].
  destruct s  as [ h_s a_s ].
  intros [ h₁h₂ disjoint ] c b offs v [ p₁ p₂ ].
  simpl in *.
  destruct h₁h₂.
  constructor.
  - unfold valid; simpl.
    intros x rnge.
    unfold disjoint_union in disjoint.
    destruct disjoint as [ disjoint union ].
    apply predicate_equality in union; unfold Predicate.equiv in union.
    apply union.
    left.
    now apply p₁.
  - easy.
Qed.

Corollary star_readv_left h₁ h₂ s : h₁ ⋆ h₂ is s -> forall chunk vaddr v,
                    readsv h₁ chunk vaddr v -> readsv s chunk vaddr v.
Proof.
  intros h *.
  destruct vaddr; simpl; trivial.
  eapply star_read_left; eauto.
Qed.

Lemma star_read_right h₁ h₂ s : h₁ ⋆ h₂ is s -> forall chunk b offs v,
                    reads h₂ chunk b offs v -> reads s chunk b offs v.
Proof.
  intros s_star **.
  apply star_commutative_rel in s_star.
  eapply star_read_left; eauto.
Qed.

Corollary star_readv_right h₁ h₂ s : h₁ ⋆ h₂ is s -> forall chunk vaddr v,
                    readsv h₂ chunk vaddr v -> readsv s chunk vaddr v.
Proof.
  intros h *.
  destruct vaddr; simpl; trivial.
  eapply star_read_right; eauto.
Qed.

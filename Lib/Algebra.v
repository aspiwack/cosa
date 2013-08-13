Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Coq.Lists.List.

(** Typeclasses for algebraic laws. *)

Class Associative {A} (E:A->A->Prop) (f:A->A->A) :=
  associativity : forall x y z, E (f (f x y) z) (f x (f y z))
.

Class LeftNeutral {A} (E:A->A->Prop) (f:A->A->A) (e:A) :=
  left_neutrality : forall x, E (f e x) x
.

Class RightNeutral {A} (E:A->A->Prop) (f:A->A->A) (e:A) :=
  right_neutrality : forall x, E (f x e) x
.

Class Commutative {A} (E:A->A->Prop) (f:A->A->A) :=
  commutativity : forall x y, E (f x y) (f y x)
.

Instance commutative_neutral {A} E {_:Transitive E} f {_:Commutative E f} (e:A) {_:LeftNeutral E f e} :
             RightNeutral E f e.
Proof.
  unfold RightNeutral.
  intros **.
  rewrite commutativity.
  apply left_neutrality.
Qed.
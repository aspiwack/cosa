(** Transition structures are an intensional version of relations,
    they can be used to represent transition systems while leaving the
    name of the transition accessible.

    While relation can be implemented as [A->B->Prop], transition
    structures correspond to [A->Fam B], where
    [Fam B = { I:Type & I -> B }]. *)

Record Transition {S T:Type} := {
  trans : S -> Type;
  next : forall s, (trans s) -> T
}.
Arguments Transition S T : clear implicits.


Definition seq {S T U:Type} (t:Transition S T) (s:Transition T U) : Transition S U := {|
  trans x := { τ₁:t.(trans) x & s.(trans) (t.(next) x τ₁) } ;
  next x τ := s.(next) _ (projT2 τ)
|}.
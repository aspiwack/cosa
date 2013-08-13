(** A datatype to coerce from [Type] to [Prop]. The essence is that
    [squash {x:A|P x}] is equivalent to [exists x:A, P x], however,
    for instance, [squash (forall x:A, {y:B|P x y})] isn't equivalent
    to [forall x:A, exists y:B, P x y] (the former is stronger than
    the latter). In fact [(forall x:A, squash P x) -> squash (forall
    x:A,P x)] is an equivalent for of the axiom of choice [(forall
    x:A, exists y:B, P x y) -> (exists f:A->B, forall x:A, P x (f x))]. *)


Inductive squash (A:Type) : Prop :=
| squash_intro (a:A) : squash A
.

Lemma squash_map {A B} : (A->B) -> squash A -> squash B.
Proof.
  intros ? [?]; constructor; eauto.
Qed.

Lemma squash_unit {A} : A -> squash A.
Proof.
  intros ?; constructor; assumption.
Qed.

Lemma squash_join {A} : squash (squash A) -> squash A.
Proof.
  intros [?]; assumption.
Qed.

Lemma squash_counit {P:Prop} : squash P -> P.
Proof.
  intros [?]; assumption.
Qed.

Lemma squash_and {A B} : squash (A*B) -> (squash A) /\ (squash B).
Proof.
  intros [[h₁ h₂]].
  split; constructor; assumption.
Qed.

(** The binary case of finite choice. *)
Lemma and_squash {A B} : (squash A) /\ (squash B) -> squash (A*B).
Proof.
  intros [[h₁][h₂]].
  constructor;split;assumption.
Qed.

(** The zero-ary case of finite choice. *)
Lemma squash_top : squash unit.
Proof. do 2 constructor. Qed.

(** In the general case, of dependent product, only this direction is available. *)
Lemma squash_forall {A B} : squash (forall x:A, B x) -> forall x, squash (B x).
Proof.
  intros h x.
  destruct h as [h].
  constructor; eauto.
Qed.

(** Index types [A] where the converse of [squash_forall] is true are
    said to support choice. The property can be read in a familiar
    way: products over A of inhabited types is inhabited. Types
    supporting choice consist essentially of types for which a list of
    the element exist. It cannot be proved though, as some forms of
    choice are consistent. *)
Definition has_choice A :=
  forall B:A->Type, (forall x,squash (B x)) -> squash (forall x:A, B x)
.

(** Types supporting choice can hoist existentials out. *)
Lemma choice_exists A : has_choice A ->
  forall (B:A->Type) (P:forall x:A, B x -> Prop),
  (forall x:A, exists y:B x, P x y) ->
  exists f:(forall x:A,B x), forall x:A, P x (f x).
Proof.
  intros choice * h.
  assert (forall x:A, squash { y:B x & P x y }) as h'.
  { intros x; specialize (h x).
    destruct h as [ y h ].
    repeat econstructor; eauto. }
  apply choice in h'.
  destruct h' as [h'].
  exists (fun x => projT1 (h' x)).
  intros x.
  apply (projT2 (h' x)).
Qed.

(** A few type supporting choice from the standard library. *)
(** Equivalent to Lemma [squash_top]. *)
Lemma empty_has_choice : has_choice Empty_set.
Proof.
  unfold has_choice.
  intros B f.
  constructor; intros [].
Qed.

Lemma unit_has_choice : has_choice unit.
Proof.
  unfold has_choice.
  intros B f.
  specialize (f tt); destruct f as [f].
  constructor; intros [].
  assumption.
Qed.

(** Equivalent to Lemma [and_squash] *)
Lemma bool_has_choice : has_choice bool.
Proof.
  unfold has_choice.
  intros B f.
  generalize (f true); intros [h₁].
  generalize (f false); intros [h₂].
  constructor; intros [|]; assumption.
Qed.
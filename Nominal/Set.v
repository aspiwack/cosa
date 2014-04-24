Require Import Cosa.Lib.Header.
Require Export Cosa.Nominal.Atom.
Require Export Cosa.Lib.CMaps.

Reserved Notation "π · x" (at level 40).
Reserved Notation "⟨ a₁ a₂ ⟩" (at level 0, a₁ at level 0, a₂ at level 0).
Reserved Notation "A '-fs->' B" (at level 99, right associativity, B at level 200).

(** This notation for permutation should probably be in Atom.v. *)
Notation "⟨ a₁ a₂ ⟩" := ([{| tfst:=a₁ ; tsnd:=a₂ |}]).

(** Definitions for nominal sets. As we want to pretend that we are
    working only with nominal sets, it makes more sense to use
    typeclasses than records as a definition of nominal sets. The
    basic object in the nominal-set technology is a group action by
    finite permutation. *)

Class Action (A:Type) := {
  act : Permutation -> A -> A
  where "π · x" := (act π x) ;
  act_proper : Proper (eq_p ==> eq ==> eq) act ;
  act_id : forall x, []·x = x ;
  act_comp : forall π₁ π₂ x, (π₁++π₂)·x = π₁·(π₂·x)
}.
Notation "π · x" := (act π x).
Existing Instance act_proper.

(** Properties about actions *)

Lemma act_op_act A `(Action A) : forall π (x:A), (op_p π)·(π·x) = x.
Proof.
  intros.
  now rewrite <- act_comp, op_p_spec_l, act_id.
Qed.

Lemma act_act_op A `(Action A) : forall π (x:A), π·((op_p π)·x) = x.
Proof.
  intros.
  now rewrite <- act_comp, op_p_spec_r, act_id.
Qed.

Hint Rewrite @act_id @act_comp @act_op_act @act_act_op : actions.
Hint Rewrite @op_p_involutive @op_p_comp : actions.

Ltac simplify_act := autorewrite with actions in *.
Ltac eager_ext :=
  try lazymatch goal with
  | |- @eq (_ -> _) _ _ => let x:=fresh in extensionality x
  end
.
Ltac narrow_act := repeat (simplify_act;eager_ext).
Ltac solve_act := intros **;narrow_act;solve[crush|easy|congruence].

Lemma act_injective π A `(Action A) : forall x y, π·x=π·y -> x=y.
Proof.
  intros x y h.
  apply (f_equal (act (op_p π))) in h.
  solve_act.
Qed.

Lemma act_float_l π A `(Action A) : forall x y, (op_p π)·x = y <-> x = π·y.
Proof.
  assert (forall π' x y, (op_p π')·x = y -> x = π'·y) as h.
  { intros π' x y h.
    eapply (act_injective (op_p π')).
    solve_act. }
  intros x y.
  split.
  + auto.
  + intros hx.
    symmetry.
    apply h.
    solve_act.
Qed.

Lemma act_float_r π A `(Action A) : forall x y, x = (op_p π)·y <-> π·x = y.
Proof.
  intros **.
  split.
  + intros **.
    symmetry.
    apply act_float_l.
    congruence.
  + intros **.
    symmetry.
    apply act_float_l.
    congruence.
Qed.

(** Comon actions *)
Program Instance perm_action : Action Atom := {|
  act := perm
|}.
Next Obligation.
  erewrite perm_comp; solve[eauto].
Qed.

(** For any type [A] we can define the discrete action (the action is
    the identity). We don't declare it as generic instance to avoid
    polluting the search space. Instead we give a generic definition
    which can be use to declare instances. *)
Program Definition discrete_action {A} : Action A := {|
  act := fun _ x => x
|}.

Instance prop_discrete : Action Prop := discrete_action.
Instance bool_discrete : Action bool := discrete_action.

(** Functions can be equipped with an action: [π·f] is [λx, π(f(π⁻¹x))]. *)
Program Instance function_action A B `(Action A) `(Action B): Action (A->B) := {|
  act := fun π f => fun x => act π (f (act (op_p π) x))
|}.
Next Obligation.
  autounfold.
  intros π₁ π₂ hπ f g <-.
  extensionality x.
  now rewrite <- hπ.
Qed.
Next Obligation.
  revert x. (* should not be introduced *)
  intros f.
  extensionality x.
  now rewrite !act_id.
Qed.
Next Obligation.
  solve_act.
Qed.

(** The particular case of predicate has a simple characterisation. *)
Remark predicate_action_spec A {_:Action A} (P:A->Prop) π :
                             forall x, (π·P) (π·x) <-> P x.
Proof.
  simpl. intros x.
  rewrite <-act_comp, op_p_spec_l, act_id.
  reflexivity.
Qed.

(** The action on predicates extends naturally to decidable finite
    sets of atom: [π·w := AtomSet.map (perm π w)]. This is not,
    however, an action in the above sense, because we would need
    quotients, and we decided to avoid quotients in this
    developpement. *)

Module AtomTree := CPTree.
Module AtomTree_Properties := CPTree_Properties.

(** Finite maps are a special kind of (finite) partial
    functions. Partial function can be equipped with an action. *)
Definition map_action_f A `(Action A) π (m:AtomTree.t A) : AtomTree.t A :=
  AtomTree.fold
     (fun m' a x => AtomTree.set (π·a) (π·x) m')
     m (AtomTree.empty _)
.

Lemma map_action_f_alt A `(Action A) π (m:AtomTree.t A) :
  forall a v, (map_action_f _ _ π m) ! a = Some v <->
              m ! ((op_p π)·a) = Some ((op_p π)·v).
Proof.
  unfold map_action_f.
  apply AtomTree_Properties.fold_rec.
  { intros m₁ m₂ m₃ h₁ h₂ a v.
    apply AtomTree.unicity in h₁.
    now rewrite <- h₁. }
  + intros **.
    AtomTree.simplify.
    firstorder congruence.
  + intros m₁ m₂ a v h₁ h₂ h₃ a' v'.
    destruct (Pos.eq_dec a' (π·a)) as [ -> | ha ].
    * rewrite <- !act_comp, !op_p_spec_l, !act_id.
      AtomTree.simplify.
      split.
      - intros hv; injection hv; clear hv; intros <-.
        solve_act.
      - intros hv; injection hv; clear hv; intros ->.
        solve_act.
    * rewrite !AtomTree.gso.
      { easy. }
      - intros <-.
        solve_act.
      - easy.
Qed.

Program Instance map_action A `(Action A) : Action (AtomTree.t A) := {|
  act π m := map_action_f _ _ π m
|}.
Next Obligation.
  autounfold. unfold map_action_f.
  intros π₁ π₂ e m m' <-.
  f_equal.
  extensionality m'; extensionality a; extensionality x.
  now rewrite e.
Qed.
Next Obligation.
  unfold map_action_f.
  rewrite <- AtomTree_Properties.fold_add_self.
  f_equal.
  solve_act.
Qed.
Next Obligation.
  apply AtomTree.unicity. intros a.
  assert (forall o₁ o₂, (forall v:A, o₁=Some v <-> o₂=Some v) -> o₁=o₂) as rem.
  { clear.
    destruct o₁; destruct o₂; try firstorder congruence.
    (* no idea why the last case isn't solved by [firstorder congruence] *)
    intros h. symmetry. rewrite <- h.
    easy. }
  apply rem. intros v.
  rewrite !map_action_f_alt.
  solve_act.
Qed.

Corollary map_action_alt A `(Action A) π (m:AtomTree.t A) :
  forall a v, (π·m)!a = Some v <->
              m!((op_p π)·a) = Some ((op_p π)·v).
Proof.
  apply map_action_f_alt.
Qed.

Corollary map_action_alt_float A `(Action A) π (m:AtomTree.t A) :
  forall a v, (π·m)!a = Some (π·v) <->
              m!((op_p π)·a) = Some v.
Proof.
  intros **.
  rewrite map_action_alt.
  solve_act.
Qed.

(** Actions can be extended to products and sums by acting
    independently on the components. *)
Program Instance prod_action A B `(Action A) `(Action B): Action (A*B) := {|
  act π xy := ( π·(fst xy) , π·(snd xy))
|}.
Next Obligation.
  autounfold.
  intros π₁ π₂ h xy ? <-.
  rewrite <- !h.
  reflexivity.
Qed.
Next Obligation.
  solve_act.
Qed.
Next Obligation.
  solve_act.
Qed.

Program Instance sum_action A B `(Action A) `(Action B): Action (A+B) := {|
  act π x := match x return _ with inl a => inl (π·a) | inr b => inr (π·b) end
|}.
Next Obligation.
  autounfold.
  intros π₁ π₂ h [a|b] ? <-; rewrite <- h; easy.
Qed.
Next Obligation.
  revert x. (* should not have been introduced *)
  intros [a|b]; solve_act.
Qed.
Next Obligation.
  revert x. (* should not have been introduced *)
  intros [a|b]; solve_act.
Qed.

(** These actions form sum and product generalise to arbitrary
    (including infinite) sums and products (beware, the action for
    arbitrary product does not coincide with that for functions). They
    do not play well with the instance inference system however. We
    can still define particular cases. Lists, which are essentially an
    infinite sum of finite products, support such an action. *)
Program Instance list_action A `(Action A) : Action (list A) := {|
  act π l := List.map (act π) l
|}.
Next Obligation.
  autounfold. intros π₁ π₂ hπ l q <-.
  apply List.map_ext.
  intros x.
  now rewrite <- hπ.
Qed.
Next Obligation.
  (* x should not have been introduced *)
  revert x.
  (* / *)
  intros l.
  erewrite List.map_ext.
  { apply List.map_id. }
  apply act_id.
Qed.
Next Obligation.
  (* x should not have been introduced *)
  revert x.
  (* / *)
  intros l.
  erewrite List.map_ext.
  { symmetry. apply Coqlib.list_map_compose. }
  apply act_comp.
Qed.

(** It may be convienient to use isomoprhims with a Perm-Set to define
    an action. *)
Program Definition action_of_iso {A} {B} `{Action B} (f:A->B) (g:B->A)
    (h₁:forall x, g (f x) = x) (h₂:forall x, f (g x) = x) : Action A := {|
  act π x := g ( π·(f x) )
|}.
Next Obligation.
  autounfold. intros π₁ π₂ hπ x y <-.
  now rewrite <- hπ.
Qed.
Next Obligation.
  solve_act.
Qed.
Next Obligation.
  solve_act.
Qed.

(** Support *)

(** We define (finite, decidable) supports for elements of types
    equipped with an action. A support of [x] can be seen as superset
    of the free variables of [x]. *)

Definition support {A} `{Action A} (w:AtomSet.t) (x:A) :=
  forall π, (forall a, AtomSet.mem a w = true -> π·a = a) -> π·x = x
.

(* arnaud: a deplacer a l'endroit adequate *)
Lemma list_forall_inv_r : forall A (l:list A) a P, List.Forall P (l++[a]) -> P a.
Proof.
  intros * h.
  rewrite List.Forall_forall in h.
  specialize (h a).
  rewrite List.in_app_iff in h.
  apply h.
  right.
  unfold List.In.
  tauto.
Qed.

(** Equivalently, a support can be defined with respect to
    names which don't belong to the support. *)
Lemma support_alt : forall A `(Action A) (w:AtomSet.t) (x:A),
   support w x <-> forall a₁ a₂, AtomSet.mem a₁ w = false -> AtomSet.mem a₂ w = false -> ⟨a₁ a₂⟩ · x = x.
Proof.
  intros *.
  split.
  + intros h. unfold support in h.
    intros a₁ a₂ ha₁ ha₂.
    apply h.
    intros a ha.
    simpl. unfold swap. simpl.
    generalize (fun x y => proj2 (Pos.eqb_neq x y)); intros eqb_neq.
    rewrite !eqb_neq; congruence.
  + intros h. unfold support.
    intros π. generalize (canonical_perm π). intros [ π' [ hπ'_def hπ'_canon ]].
    assert ((forall a : positive, AtomSet.mem a w = true -> π' · a = a) -> π' · x = x) as h₀.
    { clear π hπ'_def.
      intros hsupp.
      assert (forall π₁, (exists π₂, π₂++π₁ = π') -> π₁·x = x) as hgen.
      { induction π₁ as [ | τ π₁ hπ₁ ].
        + intros _.
          apply act_id.
        + intros [ π₂ hπ₂ ].
          change (τ::π₁) with ([τ]++π₁).
          rewrite act_comp.
          rewrite hπ₁; [|now (exists (π₂++[τ]); rewrite <-List.app_assoc)].
          assert (Relevant π' τ) as hτ.
          { unfold Canonical in hπ'_canon.
            rewrite List.Forall_forall in hπ'_canon.
            apply hπ'_canon.
            rewrite <- hπ₂.
            rewrite List.in_app_iff. right. simpl.
            now left. }
          destruct τ as [a₁ a₂].
          destruct hτ as [ ha₁ [ ha₂ ha ]]. simpl in *.
          apply h.
          * specialize (hsupp a₁).
            destruct (AtomSet.mem a₁ w); firstorder.
          * specialize (hsupp a₂).
            destruct (AtomSet.mem a₂ w); firstorder.
      }
      apply hgen.
      now exists []. }
    intros h_supp.
    rewrite hπ'_def.
    apply h₀.
    intros a h_supp'.
    rewrite <- hπ'_def.
    auto.
Qed.

(** Equivariant functions *)

(** Functions with empty support turn out to be of prime importance
    indeed they are the functions which preserve the group action
    (they are called equivariant functions). They are the morphism of
    the category of Perm-sets (sets equipped with an action as above)
    and of the category of nominal sets which is defined below. *)

(** We define [Equivariant] at every type, instead than just
    functions, it's more uniform and will help for automated
    proofs. *)
Definition Equivariant {A} `{Action A} (x:A) :=
  support AtomSet.empty x
.

Lemma equivariant_alt₁ A `(Action A) B `(Action B) (f:A->B) : Equivariant f <-> forall π x, f (π·x) = π·(f x).
Proof.
  unfold Equivariant, support. simpl.
  split.
  + intros h π a.
    apply act_float_l.
    pattern f at 2.
    rewrite <- (h (op_p π)); [| intros **; AtomSet.fsetdec'].
    solve_act.
  + intros h π _.
    extensionality a.
    rewrite h.
    solve_act.
Qed.

Corollary equivariant_rew A `(Action A) B `(Action B) (f:A->B) : Equivariant f -> forall π x, f (π·x) = π·(f x).
Proof.
  apply equivariant_alt₁.
Qed.

Lemma equivariant_alt₂ A `(Action A) B `(Action B) C `(Action C) (f:A->B->C) :
  Equivariant f <-> forall π x y, f (π·x) (π·y) = π·(f x y).
Proof.
  split.
  + rewrite equivariant_alt₁.
    intros h **.
    rewrite h. simpl.
    solve_act.
  + unfold Equivariant,support.
    intros h π _.
    extensionality x; extensionality y. simpl.
    rewrite h.
    solve_act.
Qed.

Lemma equivariant_alt₃ A `(Action A) B `(Action B) C `(Action C) D `(Action D) (f:A->B->C->D) :
  Equivariant f <-> forall π x y z, f (π·x) (π·y) (π·z) = π·(f x y z).
Proof.
  split.
  + rewrite equivariant_alt₁.
    intros h **.
    rewrite h. simpl.
    solve_act.
  + unfold Equivariant,support.
    intros h π _.
    extensionality x; extensionality y; extensionality z. simpl.
    rewrite h.
    solve_act.
Qed.

(** The very important property of equivariant functions is that they
    preserve supports. *)
Theorem equivariant_preserve_support A `(Action A) B `(Action B) (f:A->B) :
  Equivariant f -> forall x w, support w x -> support w (f x)
.
Proof.
  rewrite equivariant_alt₁. unfold support.
  intros h x w hsupp π hfix.
  now rewrite <- h, hsupp.
Qed.

(** A dual property on injective equivariant functions. Useful to
    prove that a set is nominal (see below) by embedding it into a
    nominal set. *)
Theorem equivariant_inj_reflect_support A `(Action A) B `(Action B) (f:A->B) :
  Equivariant f -> (forall x y, f x = f y -> x =y) ->
  forall x w, support w (f x) -> support w x.
Proof.
  rewrite equivariant_alt₁. unfold support.
  intros h inj x w hsupp π hfix.
  apply inj.
  rewrite h.
  auto.
Qed.

(** Combinators and applications for automated propagation of the
    equivariant property. *)
Create HintDb equivariant discriminated.

Lemma equivariant_app A `(Action A) B `(Action B) (f:A->B) (x:A) :
  Equivariant f -> Equivariant x -> Equivariant (f x).
Proof.
  intros hf hx.
  unfold Equivariant in hx|-*.
  eapply equivariant_preserve_support; assumption.
Qed.


Lemma equivariant_id A `(Action A) : Equivariant (@Tactics.id A).
Proof.
  unfold Equivariant,support,Tactics.id. simpl.
  solve_act.
Qed.
Hint EResolve equivariant_id : equivariant.

Lemma equivariant_comp A `(Action A) B `(Action B) C `(Action C) :
  Equivariant (@compc A B C).
Proof.
  apply equivariant_alt₂. unfold compc.
  intros π f g.
  extensionality x. unfold comp. simpl.
  solve_act.
Qed.
Hint EResolve equivariant_comp : equivariant.

Lemma equivariant_k A `(Action A) B `(Action B) : Equivariant (@kc A B).
Proof.
  unfold Equivariant,support,kc. simpl.
  solve_act.
Qed.
Hint EResolve equivariant_k : equivariant.

Lemma equivariant_s A `(Action A) B `(Action B) C `(Action C) : Equivariant (@sc A B C).
Proof.
  unfold Equivariant,support,sc. simpl.
  solve_act.
Qed.
Hint EResolve equivariant_s : equivariant.

(* prepare_narrow_equivariant is set later to avoid bad interaction
   with the typeclass inference mechanism. Maybe a better way would be
   using [Hint Unfold] but I haven't figured a way to succeed with
   that. *)
Ltac prepare_narrow_equivariant := idtac.
(* spiwack: is there a way to just make a call to eauto? *)
Ltac narrow_equivariant :=
  repeat (solve[prepare_narrow_equivariant;eauto with equivariant]||eapply equivariant_app)
.

Lemma equivariant_pair A `(Action A) B `(Action B) : Equivariant (@Datatypes.pair A B).
Proof.
  apply equivariant_alt₂. simpl.
  easy.
Qed.
Hint EResolve equivariant_pair : equivariant.

Lemma equivariant_fst A `(Action A) B `(Action B) : Equivariant (@fst A B).
Proof.
  apply equivariant_alt₁. simpl.
  easy.
Qed.
Hint EResolve equivariant_fst : equivariant.

Lemma equivariant_snd A `(Action A) B `(Action B) : Equivariant (@snd A B).
Proof.
  apply equivariant_alt₁. simpl.
  easy.
Qed.
Hint EResolve equivariant_snd : equivariant.

(* spiwack: there is a duplicate of [comp] for some reason. I should
   probably clean this up.  *)
Lemma equivariant_comp' A `(Action A) B `(Action B) C `(Action C) :
  Equivariant (@comp A B C).
Proof.
  apply equivariant_alt₂.
  intros π f g.
  extensionality x. unfold comp. simpl.
  solve_act.
Qed.
Hint EResolve equivariant_comp' : equivariant.

Lemma equivariant_map A `(Action A) B `(Action B) : Equivariant (@List.map A B).
Proof.
  apply equivariant_alt₂.
  intros π f l.
  induction l as [ | x l h ].
  + easy.
  + change (π·(x::l)) with ((π·x)::(π·l)).
    rewrite !list_map_cons.
    rewrite h.
    simpl.
    solve_act.
Qed.
Hint EResolve equivariant_map : equivariant.

Definition swap_args {A B C:Type} (f:A->B->C) : B->A->C :=
  fun y x => f x y
.

Lemma swap_args_equivariant A `(Action A) B `(Action B) C `(Action C) :
  Equivariant (@swap_args A B C).
Proof.
  apply equivariant_alt₃.
  intros π f x y. unfold swap_args. simpl.
  solve_act.
Qed.
Hint EResolve swap_args_equivariant : equivariant.

(** Nominal sets *)

(** The nominal sets are the Perm-sets of which each elements is
    finitely supported. *)

Class Nominal (A:Type) := {
  has_action :> Action A ;
  supported : forall x:A, exists w, support w x
}.

Ltac prepare_narrow_equivariant ::= simpl has_action.

(** Common nominal sets *)

Program Instance perm_nominal : Nominal Atom.
Next Obligation.
  exists (AtomSet.singleton x).
  unfold support. simpl.
  intuition.
Qed.

Program Definition discrete_nominal {A} : Nominal A := {|
  has_action := discrete_action
|}.
Next Obligation.
  exists AtomSet.empty.
  unfold support. simpl.
  easy.
Qed.

Instance prop_discrete' : Nominal Prop := discrete_nominal.
Instance bool_discrete' : Nominal bool := discrete_nominal.


Program Instance prod_nominal A B `(Nominal A) `(Nominal B): Nominal (A*B).
Next Obligation.
  (* [a] and [b] are automatically introduced (as the result of an
     automatic [destruct]) by [Program]. *)
  destruct (supported a) as [ wa hwa ].
  destruct (supported b) as [ wb hwb ].
  exists (AtomSet.union wa wb).
  unfold support.
  intros π hπ. simpl. unfold support in *.
  rewrite hwa,hwb; [ easy | .. ].
  + intros a₁ ha₁.
    apply hπ.
    AtomSet.fsetdec'.
  + intros a₂ ha₂.
    apply hπ.
    AtomSet.fsetdec'.
Qed.

Program Instance sum_nominal A B `(Nominal A) `(Nominal B): Nominal (A+B).
Next Obligation.
  (* [x] should not have been introduced. *)
  revert x.
  (* / *)
  intros [ x | y ].
  + destruct (supported x) as [ w hw ].
    exists w. unfold support in *.
    intros **. simpl.
    now rewrite hw.
  + destruct (supported y) as [ w hw ].
    exists w. unfold support in *.
    intros **. simpl.
    now rewrite hw.
Qed.

(** The nominal set on sum extends to arbitrary sums, but the product
    does not.  Lists are sums of final product, they are indeed lifted
    to nominal set. *)
Program Instance list_nominal A `(Nominal A) : Nominal (list A).
Next Obligation.
  (* [x] should not have been introduced. *)
  revert x.
  (* / *)
  intros l.
  induction l as [|x l [w hw]].
  + exists AtomSet.empty.
    now unfold support.
  + destruct (supported x) as [w' hw'].
    exists (AtomSet.union w w').
    unfold support in *. simpl.
    intros π hπ. change (List.map (act π) l) with (π·l).
    rewrite hw, hw'.
    - easy.
    - intros a. specialize (hπ a).
      AtomSet.fsetdec'.
    - intros a. specialize (hπ a).
      AtomSet.fsetdec'.
Qed.

(** Isomorphism, of course, lift to nominal sets. *)
Program Definition nominal_of_iso {A} {B} `{Nominal B} (f:A->B) (g:B->A)
    (h₁:forall x, g (f x) = x) (h₂:forall x, f (g x) = x) : Nominal A := {|
  has_action := action_of_iso f g h₁ h₂
|}.
Next Obligation.
  destruct (supported (f x)) as [w hw].
  exists w.
  unfold support in *. simpl.
  intros π hπ.
  rewrite hw,h₁; [reflexivity|].
  easy.
Qed.

(** Functions are not all finitely supported (a finitely supported
    function preserves all the permutations which fix all the elements
    of their support). Finitely supported functions, however, are by
    definition a nominal set, and form the exponential objects of the
    category of nominal sets. We start by defining the generic
    restriction of an Perm-set to a nominal set by taking its finitely
    supported elements. *)
Definition FSElt (A:Type) `{Action A} := { x:A | exists w, support w x }.

(** This axiom is necessary to define avoid quotients. Since
    propositional extensionality implies proof irrelevance, it is
    actually provable in our context. But it is cleaner to show the
    assumptions precisely. *)
Axiom fs_extensionality : forall A `(Action A) (x y:FSElt A),
                            proj1_sig x = proj1_sig y -> x = y.

Program Instance fs_action (A:Type) `(Action A) : Action (FSElt A) := {|
  act π x := π·(x:A)
|}.
Next Obligation.
  destruct x as [x [w hw]]. simpl.
  set (w' := AtomSet.map (act π) w).
  exists w'.
  unfold support in *. intros π' h.
  apply act_float_l. rewrite <-!act_comp.
  apply hw.
  intros a ha.
  rewrite ->!act_comp.
  rewrite h.
  + now rewrite <-act_comp, op_p_spec_l,act_id.
  + unfold w'.
    rewrite AtomSet.map_spec_inj.
    * easy.
    * apply act_injective.
Qed.
Next Obligation.
  autounfold.
  intros π₁ π₂ hπ x y <-.
  apply fs_extensionality. simpl.
  now rewrite hπ.
Qed.
Next Obligation.
  apply fs_extensionality. simpl.
  apply act_id.
Qed.
Next Obligation.
  apply fs_extensionality. simpl.
  apply act_comp.
Qed.

Program Instance fs_nominal (A:Type) `(Action A) : Nominal (FSElt A).
Next Obligation.
  destruct x as [x [w hw]].
  exists w.
  unfold support. intros π hπ. simpl.
  apply fs_extensionality. simpl.
  now apply hw.
Qed.

(** We give a special alias in the case of functions to define a
    coercion *)
Definition FSFun A `{Action A} B `{Action B} : Type := FSElt (A->B).
Notation "A '-fs->' B" := (FSFun A B).

Program Definition fun_of_fs_fun A `{Action A} B `{Action B} (f:A-fs->B) : A-> B := f.
Coercion fun_of_fs_fun : FSFun >-> Funclass.


Program Instance fsfun_nominal A `(Action A) B `(Action B) : Nominal (FSFun A B) := fs_nominal _ _.

(** An example of finitely supported function is the predicate
    generated by the elements in a list: [List.In], since [List.In] is
    equivariant. *)
Lemma In_equivariant A `(Action A) : Equivariant (@List.In A).
Proof.
  apply equivariant_alt₂.
  intros π x l.
  simpl.
  induction l as [ | y l hl ].
  + easy.
  + simpl.
    apply prop_extensionality.
    rewrite hl.
    firstorder (eauto using act_injective;congruence).
Qed.
Hint EResolve In_equivariant.

Program Definition In_fs {A} `{Nominal A} (l:list A) : A-fs->Prop :=
  fun x => List.In x l
.
Next Obligation.
  destruct (supported l) as [w hw].
  exists w.
  apply (equivariant_preserve_support _ _ _ _ (swap_args (@List.In A))).
  { narrow_equivariant. }
  assumption.
Qed.

Lemma In_fs_equivariant A `(Nominal A) : Equivariant In_fs.
Proof.
  apply equivariant_alt₁.
  intros π l.
  apply fs_extensionality. simpl.
  extensionality x.
  erewrite equivariant_rew; [|narrow_equivariant]. simpl.
  solve_act.
Qed.

(** Finite maps are, by definition, finitely supported. *)

Definition tree_get_fs {A} `{Nominal A} (m:AtomTree.t A) : (Atom*A)-fs->Prop :=
   In_fs (AtomTree.elements m)
.

Lemma tree_get_fs_equivariant A `(Nominal A) : Equivariant (@tree_get_fs A _).
Proof.
  assert (forall m a (v:A), m!a = Some v <->
                            List.In (a,v) (AtomTree.elements m)) as def.
    { intros **.
      split; (apply AtomTree.elements_correct ||
              apply AtomTree.elements_complete). }
  rewrite equivariant_alt₁.
  unfold tree_get_fs.
  intros π m. apply fs_extensionality. simpl.
  extensionality ax. destruct ax as [a x]. simpl.
  apply prop_extensionality.
  rewrite <- !def.
  apply map_action_alt.
Qed.

Program Instance map_nominal A `(Nominal A) : Nominal (AtomTree.t A).
Next Obligation.
  (* [x] should not have been introduced. *)
  revert x.
  (* / *)
  intros m.
  destruct (supported (tree_get_fs m)) as [w hw].
  exists w.
  eapply equivariant_inj_reflect_support in hw.
  { eauto. }
  { apply tree_get_fs_equivariant. }
  clear.
  intros m₁ m₂ h. apply (f_equal (@proj1_sig _ _)) in h. simpl in h.
  apply AtomTree.unicity.
  intros.
  assert (forall (o₁ o₂:option A), (forall v, o₁=Some v<->o₂=Some v) -> o₁=o₂) as L.
  { clear.
    destruct o₁; destruct o₂; try firstorder congruence.
    (* no idea why the last case isn't solved by [firstorder congruence] *)
    intros h. symmetry. rewrite <- h.
    easy. }
  apply L. intros v.
  assert (forall m a (v:A), m!a = Some v <->
                            List.In (a,v) (AtomTree.elements m)) as def.
  { intros **.
    split; (apply AtomTree.elements_correct ||
            apply AtomTree.elements_complete). }
  rewrite !def.
  apply (f_equal (fun f => f (a,v))) in h.
  (* unification bug? no rewriting with h *)
  assert (forall p q:Prop, p=q -> (p<->q)) as L'.
  { now intros ? ? <-. }
  apply L'.
  exact h.
Qed.

(** Freshness *)

Definition Fresh {A} `{Action A} (a:Atom) (x:A) :=
  exists w, support w x /\ ~AtomSet.In a w
.

Remark equivariant_preserve_fresh A `(Action A) (a:Atom) (x:A) B `(Action B):
  forall f:A->B, Equivariant f -> Fresh a x -> Fresh a (f x).
Proof.
  intros f hf [w [hw ha]].
  exists w.
  split; [|assumption].
  now eapply equivariant_preserve_support.
Qed.

(** Freshness quantifier: "for all atom except a finite
    set". Typically equivalent to "for all fresh atom" or "there exists
    a fresh atom". *)
Definition fq (Q:Atom->Prop) : Prop :=
  exists w, forall a, ~AtomSet.In a w -> Q a
.

(* For some reason, fails as a reserved notation. *)
Notation "'fresh' a .. b , p" := (fq (fun a => .. (fq (fun b => p)) .. )) (at level 200, a binder, right associativity, format "'[' 'fresh'  '/  ' a  ..  b ,  '/  ' p ']'").

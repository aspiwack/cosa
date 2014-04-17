Require Import Cosa.Lib.Header.
Require Export Cosa.Nominal.Atom.

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

Lemma act_injective π A `(Action A) : forall x y, π·x=π·y -> x=y.
Proof.
  intros x y h.
  apply (f_equal (act (op_p π))) in h.
  now rewrite <-!act_comp, !op_p_spec_l,!act_id in h.
Qed.

Lemma act_float_l π A `(Action A) : forall x y, (op_p π)·x = y <-> x = π·y.
Proof.
  assert (forall π' x y, (op_p π')·x = y -> x = π'·y) as h.
  { intros π' x y h.
    eapply (act_injective (op_p π')).
    now rewrite <-!act_comp, !op_p_spec_l,!act_id. }
  intros x y.
  split.
  + auto.
  + intros hx.
    symmetry.
    apply h.
    rewrite op_p_involutive.
    congruence.
Qed.

Lemma act_float_r π A `(Action A) : forall x y, x = (op_p π)·y -> π·x = y.
Proof.
  intros **.
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
  revert x. (* should not be introduced *)
  intros f.
  extensionality x.
  now rewrite <-!act_comp, op_p_comp.
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
  now rewrite !act_id.
Qed.
Next Obligation.
  now rewrite !act_comp.
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
  intros [a|b]; rewrite act_id; easy.
Qed.
Next Obligation.
  revert x. (* should not have been introduced *)
  intros [a|b]; rewrite act_comp; easy.
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
  now rewrite act_id.
Qed.
Next Obligation.
  now rewrite act_comp, h₂.
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

(** Function with empty support turn out to be of prime importance
    indeed they are the functions which preserve the group action
    (they are called equivariant functions). They are the morphism of
    the category of Perm-sets (sets equipped with an action as above)
    and of the category of nominal sets which is defined below. *)
Definition Equivariant {A} `{Action A} {B} `{Action B} (f:A->B) :=
  forall π x, f(π·x) = π·(f x)
.

Lemma equivariant_alt A `(Action A) B `(Action B) (f:A->B) : Equivariant f <-> support AtomSet.empty f.
Proof.
  unfold Equivariant, support. simpl.
  split.
  + intros h π _.
    extensionality x.
    rewrite h.
    now rewrite <- act_comp, op_p_spec_r, act_id.
  + intros h π x.
    pattern f at 1. rewrite <- (h π).
    * now rewrite <- act_comp, op_p_spec_l, act_id.
    * intros a c.
      AtomSet.fsetdec'.
Qed.

(** The very important property of equivariant functions is that they
    preserve supports. *)
Theorem equivariant_preserve_support A `(Action A) B `(Action B) (f:A->B) :
  Equivariant f -> forall x w, support w x -> support w (f x)
.
Proof.
  unfold Equivariant,support.
  intros h x w hsupp π hfix.
  now rewrite <- h, hsupp.
Qed.

(** Nominal sets *)

(** The nominal sets are the Perm-sets of which each elements is
    finitely supported. *)

Class Nominal (A:Type) := {
  has_action :> Action A ;
  supported : forall x:A, exists w, support w x
}.

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
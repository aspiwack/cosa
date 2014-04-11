Require Import Cosa.Lib.Header.
Require Import Coq.PArith.BinPos.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetPositive.

Local Open Scope positive_scope.

(** Atoms for the nominal-set technology.  Atoms need to support a
   type of finite decidable subsets. The existence of singleton sets
   among the finite decidable sets (which are needed) implies
   decidability of equality. This, in turns implies the existence of
   transpositions needed to define finite permutations. We could
   define an abstraction over suitable types of atoms but we will just
   settle with [positive] instead. For the type of sets we use the
   tries on [positive] from Coq's [MSet] library. *)

Definition Atom := positive.

Record Transposition := { tfst : Atom ; tsnd : Atom }.

Definition swap (τ:Transposition) (a:Atom) : Atom :=
  if      a =? tfst τ then tsnd τ
  else if a =? tsnd τ then tfst τ
  else                    a
.

(** Finite permutations. All permutations considered are finite, so
    we simply refer to them as permutations. *)
Definition Permutation := list Transposition.

Definition perm (π:Permutation) (a:Atom) : Atom :=
  List.fold_right swap a π
.

Definition eq_p (π₁ π₂:Permutation) : Prop :=
  (eq ==> eq)%signature (perm π₁) (perm π₂)
.

Instance eq_p_equiv : Equivalence eq_p.
Proof.
  split.
  + unfold Reflexive, eq_p. autounfold.
    congruence.
  + unfold Symmetric, eq_p. autounfold.
    intros **.
    symmetry.
    auto.
  + unfold Transitive, eq_p. autounfold.
    intros ** h₁ h₂ ? ? <-.
    etransitivity.
    * eapply h₁; easy.
    * eapply h₂; easy.
Qed.

Instance perm_proper : Proper (eq_p ==> eq ==> eq) perm.
Proof.
  autounfold.
  intros π₁ π₂ h a b hab.
  now apply h.
Qed.

Remark perm_comp (π₁ π₂:Permutation) :
  (eq==>eq)%signature (perm (π₁++π₂)) (fun a => (perm π₁) ((perm π₂) a)).
Proof.
  autounfold. intros x y <-.
  unfold perm.
  apply List.fold_right_app.
Qed.

Corollary perm_comp' (π₁ π₂:Permutation) :
  forall a, perm (π₁++π₂) a = perm π₁ (perm π₂ a).
Proof.
  intros a.
  now apply perm_comp.
Qed.

Instance comp_proper : Proper (eq_p ==> eq_p ==> eq_p) (@List.app _).
Proof.
  autounfold.
  intros π₁ π₂ h₁ π₃ π₄ h₂.
  unfold eq_p in *.
  rewrite !perm_comp.
  autounfold in *.
  intros **.
  auto.
Qed.

(** The inverse permutation *)
Definition op_p (π:Permutation) : Permutation :=
  List.rev π
.

Lemma transposition_inverse : forall τ, eq_p [τ;τ] [].
Proof.
  intros *. unfold eq_p. autounfold.
  intros a b <-. simpl.
  unfold swap.
  generalize (Pos.eqb_spec a (tfst τ)); intros [ <- | h₁ ].
  + generalize (Pos.eqb_spec (tsnd τ) a); intros [ -> | h₂ ].
    * easy.
    * now rewrite Pos.eqb_refl.
  + generalize (Pos.eqb_spec a (tsnd τ)); intros [ <- | h₂ ].
    * now rewrite Pos.eqb_refl.
    * apply Pos.eqb_neq in h₁. rewrite h₁.
      apply Pos.eqb_neq in h₂. rewrite h₂.
      easy.
Qed.

Lemma op_p_involutive : forall π, op_p (op_p π) = π.
Proof @List.rev_involutive _.

Lemma op_p_spec_l : forall π, eq_p ((op_p π)++π) [].
Proof.
  induction π as [ | τ π h ]; simpl.
  + reflexivity.
  + rewrite <- List.app_assoc.
    change ([τ]++τ::π) with ([τ;τ]++π).
    rewrite transposition_inverse. simpl.
    easy.
Qed.

Corollary op_p_spec_r : forall π, eq_p (π++(op_p π)) [].
Proof.
  intros π.
  set (π' := op_p π).
  replace π with (op_p π').
  + apply op_p_spec_l.
  + unfold π'. unfold op_p.
    apply op_p_involutive.
Qed.

Lemma op_p_comp : forall π₁ π₂, eq_p (op_p (π₁++π₂)) ((op_p π₂)++(op_p π₁)).
Proof.
  intros *.
  unfold op_p.
  rewrite List.rev_app_distr.
  reflexivity.
Qed.

Lemma op_float_rl : forall π₁ π₂ π₃, eq_p π₁ (π₂++π₃) <-> eq_p (π₁++op_p π₃) π₂.
Proof.
  intros *. split.
  + intros h.
    rewrite h. rewrite <- List.app_assoc.
    rewrite op_p_spec_r.
    autorewrite with list.
    reflexivity.
  + intros h.
    rewrite <- h. rewrite <- List.app_assoc.
    rewrite op_p_spec_l.
    autorewrite with list.
    reflexivity.
Qed.

Corollary op_float_rr : forall π₁ π₂ π₃, eq_p (π₁++π₃) π₂ <-> eq_p π₁ (π₂++op_p π₃).
Proof.
  intros *.
  rewrite op_float_rl.
  rewrite op_p_involutive.
  reflexivity.
Qed.

Lemma op_float_lr : forall π₁ π₂ π₃, eq_p (π₁++π₂) π₃ <-> eq_p π₂ (op_p π₁ ++ π₃).
Proof.
  intros *. split.
  + intros h.
    rewrite <- h. rewrite List.app_assoc.
    rewrite op_p_spec_l.
    reflexivity.
  + intros h.
    rewrite h. rewrite List.app_assoc.
    rewrite op_p_spec_r.
    reflexivity.
Qed.

Corollary op_float_ll : forall π₁ π₂ π₃, eq_p π₂ (π₁ ++ π₃) <-> eq_p (op_p π₁++π₂) π₃.
Proof.
  intros *.
  rewrite op_float_lr.
  rewrite op_p_involutive.
  reflexivity.
Qed.

Corollary eq_is_null : forall π₁ π₂, eq_p π₁ π₂ <-> eq_p (π₁ ++ op_p π₂) [].
Proof.
  intros *.
  rewrite <- op_float_rl.
  reflexivity.
Qed.

Instance op_p_proper : Proper (eq_p ==> eq_p) op_p.
Proof.
  autounfold.
  intros π₁ π₂ h₁.
  rewrite eq_is_null in h₁.
  replace (op_p π₂) with (op_p π₂++[]); [|now autorewrite with list].
  rewrite op_float_ll.
  rewrite <- op_p_comp.
  lazymatch goal with
  | |- eq_p ?X _ => change X with ([]++X)
  end.
  rewrite <- op_float_rl. simpl.
  now symmetry.
Qed.


(** Decidable finite sets of atoms *)

Module AtomOrdered <: UsualOrderedType := PositiveOrderedTypeBits.
Module AtomSet <: S with Module E:=AtomOrdered.
  Include PositiveSet <+ OrdProperties <+ Decide.

  (** Some extra oomph in fsetdec to cope with the usage of [mem]
      instead of [In]. Maybe it's already been done somewhere in the
      [MSet] library, but I'm not aware of it. *)
  Ltac prep_mem :=
  repeat match goal with
  | |- mem _ _ = true => apply <- mem_spec
  | h:mem _ _ = true |- _ => apply -> mem_spec in h
  end
  .
  Ltac fsetdec' := prep_mem; fsetdec.


End AtomSet.


(** Finite permutation have a finite support. More precisely, there is
    a (finnite, decidable as above) set of all the atoms which are not
    fixed by the permutation. *)

Definition tpresupport (τ:Transposition) : AtomSet.t :=
  AtomSet.add τ.(tfst) (AtomSet.singleton τ.(tsnd))
.

Lemma tpresupport_spec τ : forall a, swap τ a <> a -> AtomSet.In a (tpresupport τ).
Proof.
  intros * h. unfold swap in h.
  generalize (fun x y => proj2 (Pos.eqb_neq x y)); intros eqb_neq.
  generalize (Pos.eqb_spec a (tfst τ)). intros [ -> | hfst ].
  { unfold tpresupport. AtomSet.fsetdec. }
  rewrite eqb_neq in h; [ | easy ].
  generalize (Pos.eqb_spec a (tsnd τ)). intros [ -> | hsnd ].
  { unfold tpresupport. AtomSet.fsetdec. }
  rewrite eqb_neq in h; [ | easy ].
  now contradiction h.
Qed.

Definition presupport (π:Permutation) : AtomSet.t :=
  List.fold_right (fun τ ρ => AtomSet.union (tpresupport τ) ρ) AtomSet.empty π
.

Lemma presupport_spec π : forall a, perm π a <> a -> AtomSet.In a (presupport π).
Proof.
  induction π as [ | τ π h ].
  + simpl.
    AtomSet.fsetdec.
  + simpl. intros a.
    generalize (Pos.eq_dec (perm π a) a). intros [ -> | ha ].
    * intros ha.
      apply tpresupport_spec in ha.
      AtomSet.fsetdec.
    * apply h in ha. intros _.
      AtomSet.fsetdec.
Qed.

Definition support (π:Permutation) : AtomSet.t :=
  AtomSet.filter (fun a => negb (perm π a =? a)) (presupport π)
.

Lemma support_spec π : forall a, perm π a <> a <-> AtomSet.In a (support π).
Proof.
  intros *.
  split.
  + intros h.
    unfold support.
    rewrite AtomSet.filter_spec; [|unfold compat_bool; autounfold; congruence].
    split.
    * now apply presupport_spec.
    * rewrite negb_true_iff.
      now rewrite Pos.eqb_neq.
  + unfold support.
    rewrite AtomSet.filter_spec; [|unfold compat_bool; autounfold; congruence].
    intros [ _ h ].
    rewrite negb_true_iff in h.
    now rewrite Pos.eqb_neq in h.
Qed.


(** Finite permutation have a more canonical form. *)

Definition Relevant (π:Permutation) (τ:Transposition) :=
  perm π τ.(tfst) <> τ.(tfst) /\
  perm π τ.(tsnd) <> τ.(tsnd) /\
  τ.(tfst) <> τ.(tsnd)
.

Definition Canonical (π:Permutation) := List.Forall (fun τ => Relevant π τ) π.

(* (** spiwack: I don't find this lemma obvious. As far as I can tell *)
(*     though, it is missing in Pitts's lecture notes. *) *)
(* Lemma canonical_monotonic_r (π:Permutation) (τ:Transposition) : *)
(*   Canonical (π++[τ]) -> Canonical π. *)
(* Proof. *)
(*   unfold Canonical. rewrite !List.Forall_forall. *)
(*   intros h τ' hτ'. *)
(*   specialize (h τ'). *)
(*   rewrite in_app_iff in h. *)
(*   prove_hyp h. *)
(*   { now left. } *)
(*   unfold Relevant in *. *)
(*   destruct h as [ hfst [ hsnd hboth ]]. *)
(*   decompose_conj. *)
(*   +  *)

(** Proof adapted from lectures notes by Andrew Pitts (2011).  We only
    need the "pre-support" here, rather than the more precise
    support. *)
Theorem canonical_perm : forall π, exists π', eq_p π π' /\ Canonical π'.
Proof.
  (* Preparing the goal. *)
  intros π.
  assert (exists π', eq_p π π' /\ List.Forall (fun τ => Relevant π τ) π') as h.
  Focus 2. {
    destruct h as [ π' [ h_eq_π' h_canonical_π' ]].
    exists π'.
    split.
    + easy.
    + unfold Canonical in *.
      rewrite !List.Forall_forall in *.
      intros x hx.
      apply h_canonical_π' in hx.
      unfold Relevant in *.
      rewrite <- !h_eq_π'.
      tauto. } Unfocus.
  generalize (presupport_spec π).
  set (ρ := presupport π). clearbody ρ.
  revert π.
  (* /Preparing the goal. *)
  induction ρ  as [ ρ hρ | ρ' ρ h a ha hρ ] using AtomSet.P.set_induction.
  + intros π hπ.
    exists [].
    split.
    * unfold eq_p. autounfold.
      intros a b <-. simpl.
      generalize (Pos.eq_dec (perm π a) a); intros [ h | h ].
      - easy.
      - apply hπ in h.
        elimtype False.
        AtomSet.fsetdec.
    * easy.
  + intros π hπ.
    (* If [perm π a = a] then we do the induction with [π].
       In effect, this case is vacuous. *)
    generalize (Pos.eq_dec (perm π a) a). intros [ ha' | ha' ].
    { apply h.
      intros b hb.
      generalize hb; intros hb'.
      unfold AtomSet.P.Add in hρ.
      specialize (hρ b).
      apply hπ,hρ in hb.
      now destruct hb as [ <- | hb ]. }
    (* Introducing the permutation for the induction step *)
    pose (τ:={| tfst:=a ; tsnd:=perm (op_p π) a |}).
    pose (π':= π ++ [τ]).
    assert (perm π' a = a) as π'_spec_a.
    { unfold π'.
      rewrite perm_comp'. simpl.
      unfold swap. simpl.
      rewrite Pos.eqb_refl.
      rewrite <- perm_comp'.
      rewrite op_p_spec_r.
      easy. }
    (* use [impl] because we will use it as a rewriting lemma *)
    assert (forall b, a<>b -> impl (perm π b = b) (perm π' b = b)) as π'_spec_na.
    { intros b hb. unfold impl, π'.
      rewrite perm_comp'. simpl.
      unfold swap. simpl.
      generalize (fun x y => proj2 (Pos.eqb_neq x y)); intros eqb_neq.
      rewrite eqb_neq; [| congruence].
      intros hb'.
      generalize (Pos.eqb_spec b (perm (op_p π) a)). intros [ -> | hok ].
      * rewrite <- perm_comp', op_p_spec_r in hb'. simpl in hb'.
        congruence.
      * easy. }
    assert (forall τ, Relevant π' τ -> Relevant π τ) as Relevant_monotonic.
    { intros τ'.
      unfold Relevant.
      intros [ hfst [ hsnd hboth ]].
      decompose_conj.
      + rewrite π'_spec_na.
        * easy.
        * congruence.
      + rewrite π'_spec_na.
        * easy.
        * congruence.
      + easy. }
    (* Use [π']. *)
    specialize (h π').
    prove_hyp h.
    { intros b.
      generalize (Pos.eq_dec a b). intros [ <- | hb ].
      + rewrite π'_spec_a.
        tauto.
      + rewrite <- π'_spec_na; [|easy].
        intros hb₂.
        apply hπ in hb₂.
        unfold AtomSet.P.Add in hρ.
        apply hρ in hb₂.
        now destruct hb₂. }
    destruct h as [ π'' [ h_eq_π'' h_canonical_π'' ]].
    exists (π''++[τ]).
    split.
    * rewrite <- h_eq_π''.
      unfold π'.
      rewrite <- List.app_assoc.
      change [τ] with (op_p [τ]) at 2.
      rewrite op_p_spec_r.
      autorewrite with list.
      reflexivity.
    * rewrite List.Forall_forall in h_canonical_π'' |- *.
      intros τ'.
      rewrite List.in_app_iff.
      intros [ hτ' | hτ' ].
      - auto.
      - simpl in hτ'. destruct hτ' as [ <- | [] ].
        unfold Relevant, τ. simpl.
        { assert (perm (op_p π) a <> a) as ha''.
          { clear -ha'.
            intros hop. apply ha'.
            rewrite <- hop at 1.
            rewrite <- perm_comp', op_p_spec_r.
            easy.
          }
          decompose_conj.
          + easy.
          + rewrite <- perm_comp', op_p_spec_r. simpl.
            congruence.
          + congruence.
        }
Qed.

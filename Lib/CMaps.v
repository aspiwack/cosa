Require Import Coq.Bool.Bool.
Require Coq.Logic.Eqdep_dec.
Require Import compcert.lib.Maps.
Require Import Coq.PArith.PArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Cosa.Lib.Extra.

Set Implicit Arguments.

(** In this file we define a wrapper over [PTrees] ensuring that trees
    representing the same map have the same representation. This
    prevents us from needing to rely on equivalence relation for
    quotients in order to define an Perm-action (see the [Nominal]
    directory) on finite maps over atoms. *)

Local Open Scope positive_scope.

Module CPTree <: TREE.

  
  Definition elt := Pos.t.
  Definition elt_eq := Pos.eq_dec.
  
  (** Canonical trees: empty sub-trees are Leaf *)
  Fixpoint canonical {A} (m:PTree.t A) : bool :=
    match m with
    | PTree.Leaf => true
    | PTree.Node l (Some _) r => canonical l && canonical r
    | PTree.Node l None r =>
      canonical l && canonical r &&
      (negb (PTree.bempty l) || negb (PTree.bempty r))
    end
  .

  Definition t A := { m:PTree.t A | canonical m = true }.

  Remark extensionality : forall A (m₁ m₂:t A),
                            proj1_sig m₁ = proj1_sig m₂ -> m₁ = m₂.
  Proof.
    intros a [ m₁ c₁ ] [ m₂ c₂ ] h. simpl in *.
    revert c₂.
    rewrite <- h; clear h.
    intros c₂.
    f_equal.
    apply Eqdep_dec.UIP_dec.
    apply Bool.bool_dec.
  Qed.

  Program Definition empty A : t A := PTree.empty A.

  Program Definition get A (a:elt) (m:t A) : option A :=
    PTree.get a m
  .

  Lemma bempty_set : forall A a (x:A) m,
                       PTree.bempty (PTree.set a x m) = false.
  Proof.
    intros *.
    rewrite <- not_true_iff_false.
    rewrite PTree.bempty_correct.
    intros h.
    specialize (h a).
    rewrite PTree.gss in h.
    easy.
  Qed.
 
  (** Tactics for the proofs for [set] and [remove] *)
  Ltac advance_option t :=
    match goal with
    | |- context[match ?o with Some _ => _ | None => _ end] =>
      destruct o; simpl in *
    | o:option _ |- _ => t; destruct o; simpl in *
    | _ => idtac
    end
  .

  Ltac advance_tree t :=
    match goal with
    | |- context[match ?m with PTree.Leaf => _ | PTree.Node _ _ _ => _ end] =>
      first[is_var m|t];destruct m; simpl in *
    | _ => idtac
    end
  .

  Ltac forward_canonical_with h :=
    repeat match goal with
    | c:canonical (PTree.remove _ _) = true |- _ => fail 1
    | c:canonical _ = true |- _ => apply h in c
    end
  .

  Ltac forward_canonical :=
    match goal with
    | h:forall m:PTree.t _, _ |- _ =>
        progress forward_canonical_with h
    | _ => idtac
    end
  .

  (* a tactic dedicated to the proof of [set] *)
  Ltac set_tac :=
    simpl;intros;
    advance_tree idtac;
    advance_option fail;
    rewrite ?andb_true_iff , ?orb_true_iff , ?orb_false_r , ?bempty_set in *;
    solve[intuition|intuition (auto||solve[firstorder])|advance_option idtac;set_tac]
  .

  (* a tactic_dedicated to the proof of [remove] *)
  Ltac remove_tac :=
    simpl in *;intros;
    advance_tree fail;
    repeat advance_option fail;
    rewrite ?andb_true_iff , ?negb_andb, ?orb_true_iff in *;
    let p :=
        first [
            progress (advance_tree ltac:(idtac;forward_canonical))|
            progress (advance_option idtac)
          ]
    in
    solve[easy|tauto|intuition|intuition(p;remove_tac)]
  .

  (** Actual definitions of [set] and [remove] *)

  Program Definition set A (a:elt) (x:A) (m:t A) : t A :=
    PTree.set a x m
  .
  Next Obligation.
    destruct m as [ m c ]. simpl.
    revert m c.
    induction a as [ a' h | a' h | ]; set_tac.
  Qed.

  Program Definition remove A (a:elt) (m:t A) : t A :=
    PTree.remove a m
  .
  Next Obligation.
    destruct m as [ m c ]. simpl.
    revert m c.
    induction a as [ a' h | a' h | ]; remove_tac.
  Qed.

  Lemma gempty: forall (A: Type) (i: Pos.t), get i (empty A) = None.
  Proof.
    apply PTree.gempty.
  Qed.

  Lemma gss:
    forall (A: Type) (i: Pos.t) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros **.
    apply PTree.gss.
  Qed.

  
  Lemma gso:
    forall (A: Type) (i j: Pos.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros **.
    now apply PTree.gso.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: Pos.t) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros **.
    apply PTree.gsspec.
  Qed.

  Lemma gsident:
    forall (A: Type) (i: Pos.t) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros A i [m c] **. unfold set,get in *. simpl in *.
    apply extensionality. simpl.
    now apply PTree.gsident.
  Qed.

  Lemma grs:
    forall (A: Type) (i: Pos.t) (m: t A), get i (remove i m) = None.
  Proof.
    intros **.
    apply PTree.grs.
  Qed.

  Lemma gro:
    forall (A: Type) (i j: Pos.t) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros **.
    now apply PTree.gro.
  Qed.

  Lemma grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros **.
    apply PTree.grspec.
  Qed.


  (** Boolean equality *)

  Program Definition beq A (eqA:A->A->bool) (m₁ m₂:t A) : bool :=
    PTree.beq eqA m₁ m₂
  .

  Lemma beq_correct:
    forall A (eqA:A->A->bool) m1 m2,
      beq eqA m1 m2 = true <->
      (forall (x: elt),
         match get x m1, get x m2 with
         | None, None => True
         | Some y1, Some y2 => eqA y1 y2 = true
         | _, _ => False
         end).
  Proof.
    intros **.
    apply PTree.beq_correct.
  Qed.


  (** Map *)

  Program Definition map (A B : Type) (f : Pos.t -> A -> B) (m:t A) : t B :=
    PTree.map f m
  .
  Next Obligation.
    destruct m as [m c]. simpl.
    unfold PTree.map. generalize 1.
    induction m as [ | l hl o r hr ].
    + easy.
    + destruct o; simpl in *; intros;
        rewrite ?andb_true_iff , ?orb_true_iff in *.
      * intuition.
      * assert (forall m p, negb (PTree.bempty m) = true -> negb (PTree.bempty (PTree.xmap f m p)) = true).
        { clear.
          induction m as [ | l hl o r hr ].
          + easy.
          + simpl.
            destruct o; simpl in *; intros;
              rewrite ?negb_andb, ?orb_true_iff in *; intuition. }
        intuition.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: Pos.t -> A -> B) (i: Pos.t) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros **.
    apply PTree.gmap.
  Qed.

  Program Definition map1 (A B: Type) (f: A -> B) (m: t A) : t B :=
    PTree.map1 f m
  .
  Next Obligation.
    destruct m as [m c]. simpl.
    induction m as [ | l hl o r hr ].
    + easy.
    + destruct o; simpl in *;
        rewrite ?andb_true_iff , ?orb_true_iff in *.
      * intuition.
      * assert (forall m, negb (PTree.bempty m) = true -> negb (PTree.bempty (PTree.map1 f m)) = true).
        { clear.
          induction m as [ | l hl o r hr ].
          + easy.
          + destruct o; simpl in *;
            rewrite ?negb_andb , ?orb_true_iff in *; intuition. }
        intuition.
  Qed.

  Lemma gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros **.
    apply PTree.gmap1.
  Qed.


  (** Combine *)

  Program Definition combine A B C (f:option A -> option B -> option C) (m₁: t A) (m₂: t B) : t C :=
    PTree.combine f m₁ m₂
  .
  Next Obligation.
    assert (forall A (l:PTree.t A) o r, canonical l = true -> canonical r = true -> canonical (PTree.Node' l o r) = true) as hnode'.
    { clear. intros * h₁ h₂.
      unfold PTree.Node'.
      repeat (simpl;(advance_option fail||advance_tree fail));
        rewrite ?negb_andb, ?andb_true_iff, ?orb_true_iff in *;
        tauto. }
    destruct m₁ as [m₁ c₁]; destruct m₂ as [m₂ c₂]. simpl.
    revert m₂ c₂.
    induction m₁ as [ | l₁ hl₁ o₁ r₁ hr₁ ].
    + simpl.
      induction m₂ as [ | l₂ hl₂ o₂ r₂ hr₂ ].
      * easy.
      * destruct o₂; simpl; rewrite ?andb_true_iff , ?orb_true_iff; intuition.
    + destruct m₂ as [ | l₂ o₂ r₂ ].
      * simpl.
        assert (forall m, canonical m = true -> canonical (PTree.xcombine_l f m) = true).
        { clear - hnode'.
          induction m as [ | l hl o r hr ].
          + easy.
          + destruct o; simpl; rewrite ?andb_true_iff , ?orb_true_iff; intuition. }
        destruct o₁; simpl in c₁; rewrite ?andb_true_iff in c₁; intuition.
      * destruct o₁; simpl in c₁; destruct o₂; intros c₂; simpl in c₂; rewrite ?andb_true_iff in *; simpl; intuition.
  Qed.

  Lemma gcombine:
      forall A B C (f:option A->option B->option C),
      f None None = None ->
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros **.
    now apply PTree.gcombine.
  Qed.

  Lemma combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros **. unfold combine.
    apply extensionality. simpl.
    now apply PTree.combine_commut.
  Qed.

  (** Elements *)

  Program Definition elements (A: Type) (m : t A) :=
    PTree.elements m.

  Lemma elements_correct:
    forall (A: Type) (m: t A) (i: Pos.t) (v: A),
    get i m = Some v -> List.In (i, v) (elements m).
  Proof.
    intros **.
    now apply PTree.elements_correct.
  Qed.

  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: Pos.t) (v: A),
    List.In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros **.
    now apply PTree.elements_complete.
  Qed.

  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A), 
    Coqlib.list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros **.
    apply PTree.elements_keys_norepet.
  Qed.


  (** Fold *)

  Program Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
    PTree.fold f m v
  .

  Lemma fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros **.
    apply PTree.fold_spec.
  Qed.


  (** Unicity of representation of finite functions. *)
  Lemma empty_canonical_unique (A:Type) (m:PTree.t A) :
    canonical m = true -> (forall a, PTree.get a m = None) -> m = PTree.empty _.
  Proof.
    intros c h.
    induction m as [ | l hl [x|] r hr ].
    + easy.
    + specialize (h 1). simpl in h.
      easy.
    + simpl in c.
      rewrite <- PTree.bempty_correct in h. simpl in h.
      rewrite !andb_true_iff , !orb_true_iff , !negb_true_iff in *.
      firstorder congruence.
  Qed.

  Corollary empty_canonical_ext (A:Type) (m:PTree.t A) :
    canonical m = true -> (forall a, PTree.get a m = PTree.get a PTree.Leaf) ->
    m = PTree.empty _.
  Proof.
    intros ** h.
    apply empty_canonical_unique.
    + easy.
    + intros a.
      specialize (h a).
      rewrite PTree.gempty in h.
      easy.
  Qed.

  Corollary empty_unique (A:Type) (m:t A) :
    (forall a, get a m = None) -> m = empty _.
  Proof.
    destruct m as [m c]. unfold get. simpl.
    intros h.
    apply extensionality. simpl.
    now apply empty_canonical_unique.
  Qed.
 
  Theorem unicity (A:Type) (m₁ m₂:t A) :
    (forall a, get a m₁ = get a m₂) -> m₁ = m₂.
  Proof.
    destruct m₁ as [m₁ c₁] ; destruct m₂ as [m₂ c₂]. unfold get. simpl.
    intros h.
    apply extensionality. simpl.
    revert m₂ c₂ h.
    induction m₁ as [ | l₁ hl₁ o₁ r₁ hr₁ ]; intros m₂ c₂ h.
    + symmetry.
      now apply empty_canonical_ext.
    + destruct m₂ as [ | l₂ o₂ r₂ ].
      { now apply empty_canonical_ext in h. }
      destruct o₁ as [ x₁ | ]; simpl in c₁;
        rewrite ?andb_true_iff, ?orb_true_iff, ?negb_true_iff in c₁.
      * destruct o₂ as [ x₂ | ];[|now specialize (h 1)].
        simpl in c₂.
        rewrite !andb_true_iff in c₂.
        f_equal.
        - apply hl₁; [intuition ..|].
          intros a.
          now specialize (h (a~0)).
        - now specialize (h 1).
        - apply hr₁; [intuition ..|].
          intros a.
          now specialize (h (a~1)).
      * destruct o₂ as [ x₂ | ]; [now specialize (h 1)|].
        simpl in c₂.
        rewrite !andb_true_iff , !orb_true_iff, !negb_true_iff in c₂.
        f_equal.
        - apply hl₁; [intuition..|].
          intros a.
          now specialize (h (a~0)).
        - apply hr₁; [intuition ..|].
          intros a.
          now specialize (h (a~1)).
  Qed.

  Corollary elements_unicity (A:Type) (m₁ m₂:t A) :
    (elements m₁ = elements m₂) -> m₁ = m₂.
  Proof.
    intros h.
    apply unicity.
    assert (forall m a (v:A), get a m = Some v <-> List.In (a,v) (elements m)) as def.
    { intros **.
      split; (apply elements_correct || apply elements_complete). }
    assert (forall m a, get a m = None <-> forall (v:A), ~List.In (a,v) (elements m)) as def'.
    { intros **.
      split.
      + intros ha v.
        rewrite <- def.
        congruence.
      + intros ha.
        assert (forall v:A, ~(get a m = Some v)) as ha'.
        { intros v.
          now rewrite def. }
        destruct (get a m) as [ v | ].
        * specialize (ha' v).
          congruence.
        * easy. }
    intros a.
    destruct (get a m₁) as [v|] eqn:ht.
    + symmetry; rewrite def in *.
      congruence.
    + symmetry; rewrite def' in *.
      intros v. specialize (ht v).
      congruence.
  Qed.

  
(** Tactics to simplify CPTree expressions. *)

Ltac simplify_hyp h :=
  repeat match type of h with
  | appcontext[get ?n (set ?m _ _)] => constr_eq n m;rewrite gss in h
  | appcontext[get ?n (set ?m _ _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite gso in h; [| exact ne]
    | ne : m<>n |- _ => rewrite gso in h; [| exact (@not_eq_sym _ m n ne)]
    | |- _ => generalize (elt_eq n m); intros [ <- | ? ]
    end
  | appcontext[get ?n (remove ?m _)] =>
         constr_eq n m;rewrite grs in h
  | appcontext[get ?n (remove ?m _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite gro in h; [| exact ne]
    | ne : m<>n |- _ => rewrite gro in h; [| exact (@not_eq_sym _ m n ne)]
    | |- _ => generalize (elt_eq n m); intros [ <- | ? ]
    end
  | appcontext[get _ (empty _)] => rewrite gempty in h
  end
.

Ltac simplify_concl :=
  repeat match goal with
  | |- appcontext[get ?n (set ?m _ _)] => constr_eq n m;rewrite gss
  | |- appcontext[get ?n (set ?m _ _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite gso; [| exact ne]
    | ne : m<>n |- _ => rewrite gso; [| exact (@not_eq_sym _ m n ne)]
    | |- _ => generalize (elt_eq n m); intros [ <- | ? ]
    end
  | |- appcontext[get ?n (remove ?m _)] =>
         constr_eq n m;rewrite grs
  | |- appcontext[get ?n (remove ?m _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite gro; [| exact ne]
    | ne : m<>n |- _ => rewrite gro; [| exact (@not_eq_sym _ m n ne)]
    | |- _ => generalize (elt_eq n m); intros [ <- | ? ]
    end
  | |- appcontext[get _ (empty _)] => rewrite gempty
  end
.

Ltac simplify_hyps :=
  repeat match goal with
  | h : _ |- _ => progress simplify_hyp h
  end
.

Ltac simplify := simplify_hyps; simplify_concl.

End CPTree.

Module CPTree_Properties.

  Include Tree_Properties(CPTree).


  Lemma fold_add_self A (m:CPTree.t A) :
    CPTree.fold (fun m a x => CPTree.set a x m) m (CPTree.empty _) = m.
  Proof.
    apply fold_rec.
    { intros m₁ m₂ a h.
      apply CPTree.unicity in h.
      congruence. }
    + easy.
    + intros m₁ m₂ a v h₁ h₂ ->.
      easy.
  Qed.

  Lemma equal_eq_alt (A : Type) (m₁ m₂ : CPTree.t A) :
       Equal _ m₁ m₂ <-> (forall k : positive, CPTree.get k m₁ = CPTree.get k m₂).
  Proof.
    destruct m₁ as [m₁ c₁] ; destruct m₂ as [m₂ c₂].
    unfold CPTree.get. simpl.
    rewrite <- ptree_equal_eq_alt.
    unfold Equal, PTree_Properties.Equal, CPTree.get. simpl.
    reflexivity.
  Qed.

  Lemma equal_eq_alt' (A : Type) (m₁ m₂ : CPTree.t A) : Equal _ m₁ m₂ <-> m₁ = m₂.
  Proof.
    split; [| intros <-;apply Equal_refl].
    intros h.
    apply CPTree.unicity.
    now apply equal_eq_alt.
  Qed.

End CPTree_Properties.

(** Overrides a Compcert notation. *)
Notation "a ! b" := (CPTree.get b a) (at level 1).
Require Import Cosa.Lib.Tactics.
Require Import Coq.PArith.BinPos.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Cosa.Lib.Algebra.
Require Coq.Lists.List.
Require Import Coq.Lists.SetoidPermutation.
Import List.ListNotations.
Require Import Maps.
Require Import Cosa.Lib.Extra.

(** A toned down verion of map/fold for associative and commutative
    reductions. *)


Section MapReduce.

  Context {A B:Type} (E:B->B->Prop) {E_equiv: Equivalence E}.
  Context (f:BinPos.positive -> A -> B).
  Context (r:B->B->B) {r_proper : Proper (E==>E==>E) r}.
  Context {r_assoc : Associative E r} {r_commut : Commutative E r}.
  Context (n:B) {n_neutral : LeftNeutral E r n}.

  Local Notation "a ≡ b" := (E a b) (at level 70).
  Local Notation "a ⋆ b" := (r a b) (at level 40, left associativity).


  Definition list_reduce (l:list B) :=
    List.fold_left r l n
  .

  Instance list_fold_left_proper (l:list B) : Proper (E==>E) (List.fold_left r l).
  Proof.
    unfold Proper, respectful.
    induction l as [ | a l hl ].
    - (* l = [] *)
      easy.
    - (* l = a::l *)
      intros x y h.
      simpl.
      apply hl.
      rewrite h.
      reflexivity.
  Qed.

  Lemma list_reduce_nil : list_reduce [] ≡ n.
  Proof. reflexivity. Qed.
  Hint Rewrite list_reduce_nil : map_reduce.
    
  Lemma list_reduce_cons a l : list_reduce (a::l) ≡ a⋆(list_reduce l).
  Proof.
    revert a.
    induction l as [ | b l hl ]; intros a.
    - (* l = [] *)
      unfold list_reduce; simpl.
      apply commutativity.
    - (* l = b::l *)
      unfold list_reduce in *; simpl in *.
      rewrite associativity.
      rewrite !hl.
      rewrite associativity.
      reflexivity.
  Qed.
  Hint Rewrite list_reduce_cons : map_reduce.

  Lemma list_reduce_app l₁ l₂ : list_reduce (l₁++l₂) ≡ (list_reduce l₁)⋆(list_reduce l₂).
  Proof.
    induction l₁ as [ | a l₁ hl₁ ].
    - (* l₁ = [] *)
      autorewrite with map_reduce; simpl.
      now rewrite left_neutrality.
    - simpl.
      autorewrite with map_reduce.
      now rewrite hl₁.
  Qed.
  Hint Rewrite list_reduce_app : map_reduce.

  Lemma list_reduce_permutation l₁ l₂ :
    PermutationA E l₁ l₂ -> list_reduce l₁ ≡ list_reduce l₂.
  Proof.
    intros e.
    induction e as [ | x y l₁ l₂ eq e h | x y l | ].
    - (* e = permA_nil *)
      easy.
    - (* e = permA_skip _ *)
      autorewrite with map_reduce.
      rewrite eq,h.
      reflexivity.
    - (* e = permA_swap _ *)
      autorewrite with map_reduce.
      rewrite <- !associativity.
      rewrite (commutativity x y).
      reflexivity.
    - (* e = permA_trans _ *)
      solve_transitivity.
  Qed.

  Global Instance list_reduce_permutation_proper :
    Proper (PermutationA E ==> E) list_reduce.
  Proof.
    unfold Proper, respectful; intros **.
    now apply list_reduce_permutation.
  Qed.

  (** The following properties are proved over [PTree.t]. In the
      unlikely event where we would need trees over other indexes, we
      could design a functor in the spirit of
      [Maps.Tree_Properties]. *)
  Definition ptree_map_reduce (m:PTree.t A) : B :=
    PTree.fold (fun b k a => b ⋆ f k a) m n
  .

  Definition ptree_map_reduce_spec m :
    ptree_map_reduce m = list_reduce (List.map (fun x => f (fst x) (snd x)) (PTree.elements m)).
  Proof.
    unfold ptree_map_reduce.
    rewrite PTree.fold_spec.
    unfold list_reduce.
    generalize (PTree.elements m) n.
    clear.
    (* problem reduced to proving a general fusion lemma on fold_left and map *)
    intros l.
    induction l as [ | a l hl ]; intro n.
    - (* l = nil *)
      easy.
    - simpl.
      apply hl.
  Qed.

End MapReduce.



(** Left-biaised union. Meant to be used when trees are known to be disjoint. *)
Definition ptree_union {A} :=
  @PTree.combine A A A (fun a b =>
                          match a,b with
                          | Some x , _ => Some x
                          | _ , Some y => Some y
                          | _ , _ => None
                          end)
.

(** Disjointness for trees. *)
Definition ptree_disjoint {A} (m₁ m₂:PTree.t A) : Prop :=
  forall k a a', m₁!k = Some a -> m₂!k = Some a' -> False
.

Lemma ptree_disjoint_elements {A} (m₁ m₂:PTree.t A) :
  ptree_disjoint m₁ m₂ -> Coqlib.list_disjoint (PTree.elements m₁) (PTree.elements m₂).
Proof.
  intros h; unfold ptree_disjoint in h.
  unfold Coqlib.list_disjoint.
  intros [k₁ a₁] [k₂ a₂] h₁ h₂ hf.
  injection hf; clear hf; intros <- <-.
  eauto using PTree.elements_complete.
Qed.

(** Side lemmas to tie Coq's SetoidList/SetoidPermutation and Compcert's Coqlib. *)
Lemma In_InA : forall A (x:A) l, List.In x l <-> SetoidList.InA eq x l.
Proof.
  intros A x l.
  split.
  - induction l as [ | a l hl ].
    + easy.
    + simpl; intros [ -> | h ].
      * now constructor.
      * constructor (solve[eauto]).
  - induction 1 as [ ? ? <- | ? ? r hh ].
    + simpl.
      now left.
    + simpl.
      now right.
Qed.

Lemma no_repet_no_dup A (l:list A) : Coqlib.list_norepet l -> SetoidList.NoDupA eq l.
Proof.
  intros h.
  induction h as [ | a l h₁ h₂ hh ].
  - (* h = list_norepet_nil *)
    constructor.
  - (* h = list_norepet_cons a l h₁ h₂ *)
    constructor.
    + now rewrite <- In_InA.
    + easy.
Qed.

(** An extra generic lemma on list_norepet *)
Lemma list_norepet_map A B l (f:A->B) :
  Coqlib.list_norepet (List.map f l) -> Coqlib.list_norepet l.
Proof.
  induction l as [ | a l hl ].
  - (* l = [] *)
    simpl.
    intros _; constructor.
  - (* l = a::l *)
    simpl.
    intros h; inversion h as [ | ? ? h₁ h₂ ]; subst; clear h.
    constructor.
    { intro h.
      apply h₁.
      now apply List.in_map. }
    eauto.
Qed.

(** A corollary of [PTree.elements_keys_norepet] and [list_norepet_map] *)
Corollary ptree_elements_norepet A (m:PTree.t A) : Coqlib.list_norepet (PTree.elements m).
Proof.
  eapply list_norepet_map, PTree.elements_keys_norepet.
Qed.

Lemma ptree_permutation_equiv A (m₁ m₂:PTree.t A) :
  PTree_Properties.Equal (eqA:=eq) _ m₁ m₂->
  PermutationA eq (PTree.elements m₁) (PTree.elements m₂).
Proof.
  intros h.
  apply NoDupA_equivlistA_PermutationA.
  { typeclasses eauto. }
  - apply no_repet_no_dup.
    apply ptree_elements_norepet.
  - apply no_repet_no_dup.
    apply ptree_elements_norepet.
  - unfold SetoidList.equivlistA.
    intros [k a].
    assert (forall A m k (v: A), List.In (k, v) (PTree.elements m) <-> m!k = Some v)
      as elements_spec.
    { clear.
      intros **; split.
      - apply PTree.elements_complete.
      - apply PTree.elements_correct. }
    rewrite <- !In_InA, !elements_spec.
    specialize (h k).
    destruct (m₁!k); destruct (m₂!k); split;(congruence||contradiction).
Qed.

(* arnaud: j'aimerais bien partager un peu de la preuve d'au dessus, mais je n'y arrive pas… *)
Lemma element_of_disjoint_union A (m₁ m₂:PTree.t A) :
  ptree_disjoint m₁ m₂ ->
  PermutationA eq (PTree.elements (ptree_union m₁ m₂))
                  ((PTree.elements m₁)++(PTree.elements m₂)).
Proof.
  intros disj.
  apply NoDupA_equivlistA_PermutationA.
  - typeclasses eauto.
  - apply no_repet_no_dup.
    apply ptree_elements_norepet.
  - apply no_repet_no_dup.
    apply Coqlib.list_norepet_append.
    + apply ptree_elements_norepet.
    + apply ptree_elements_norepet.
    + now apply ptree_disjoint_elements.
  - unfold SetoidList.equivlistA.
    intros [k a].
    assert (forall A m k (v: A), List.In (k, v) (PTree.elements m) <-> m!k = Some v)
      as elements_spec.
    { clear.
      intros **; split.
      - apply PTree.elements_complete.
      - apply PTree.elements_correct. }
    rewrite <- ?In_InA.
    rewrite List.in_app_iff, ?elements_spec.
    unfold ptree_union.
    rewrite PTree.gcombine; [ | easy ].
    split.
    + destruct (m₁!k); destruct (m₂!k);  firstorder.
    + unfold ptree_disjoint in disj.
      specialize (disj k).
      intros [ -> | h ].
      * easy.
      * rewrite h in *. (* arnaud: apparemment le -> ne fait pas in * en v8.4 *)
        destruct (m₁!k).
        { exfalso.
          eapply disj; reflexivity. }
        { reflexivity. }
Qed.

Instance list_PermutationA_map
      A B eA {_:Equivalence eA} eB {_:Equivalence eB } (f:A->B) {_:Proper (eA ==> eB) f} :
  Proper (SetoidPermutation.PermutationA eA ==> SetoidPermutation.PermutationA eB)
         (List.map f).
Proof.
  unfold Proper, respectful.
  intros l₁ l₂ h.
  induction h as [ | x₁ x₂ l₁ l₂ e h hh | | ].
  - (* h = permA_nil *) 
    simpl.
    constructor.
  - (* h = permA_skip _ *)
    simpl.
    apply permA_skip.
    + now rewrite e.
    + assumption.
  - (* h = permA_swap _ *)
    simpl.
    apply permA_swap.
  - (* h = permA_trans _ *)
    eapply permA_trans; eauto.
Qed.

Lemma ptree_equiv_map_reduce
        A B m₁ m₂ (f:positive->A->B)
        r {_:Associative eq r} {_:Commutative eq r}
        e {_:LeftNeutral eq r e} :
  PTree_Properties.Equal (eqA:=eq) _ m₁ m₂->
  ptree_map_reduce f r e m₁ = ptree_map_reduce f r e m₂.
Proof.
  intros h.
  apply ptree_permutation_equiv in h.
  rewrite !ptree_map_reduce_spec.
  rewrite h.
  reflexivity.
Qed.


(** [PTree.t]-s map/reduce can be split. For
    the sake simplicity, we shall content ourselves with the version up to [eq]. *)
Theorem ptree_disjoint_map_reduce
        A B m₁ m₂ (f:positive->A->B)
        r {_:Associative eq r} {_:Commutative eq r}
        e {_:LeftNeutral eq r e} :
  ptree_disjoint m₁ m₂ ->
  ptree_map_reduce f r e (ptree_union m₁ m₂) =
                 r (ptree_map_reduce f r e m₁) (ptree_map_reduce f r e m₂).
Proof.
  intros h.
  rewrite !ptree_map_reduce_spec.
  rewrite element_of_disjoint_union; [ | easy ].
  rewrite List.map_app.
  rewrite list_reduce_app; try typeclasses eauto.
  reflexivity.
Qed.

Lemma ptree_map_reduce_singleton
        A B k x (f:positive->A->B)
        r {_:Associative eq r} {_:Commutative eq r}
        e {_:LeftNeutral eq r e} :
  ptree_map_reduce f r e (PTree.set k x (PTree.empty _)) = f k x.
Proof.
  rewrite ptree_map_reduce_spec.
  replace (PTree.elements (PTree.set k x (PTree.empty _))) with [(k,x)]%list.
  { simpl.
    now rewrite left_neutrality. }
  apply singleton_eq_norepet.
  + intros [ k' y ].
    split.
    * intros h.
      apply PTree.elements_complete in h.
      ptree_simplify; congruence.
    * intros ->.
      apply PTree.elements_correct.
      ptree_simplify; congruence.
  + apply ptree_elements_norepet.
Qed.

Corollary ptree_set_map_reduce
  A B m k x (f:positive->A->B)
        r {_:Associative eq r} {_:Commutative eq r}
        e {_:LeftNeutral eq r e} :
  m!k = None ->
  ptree_map_reduce f r e (PTree.set k x m) =
               r (f k x) (ptree_map_reduce f r e m).
Proof.
  intros h.
  transitivity
   (ptree_map_reduce f r e (ptree_union (PTree.set k x (PTree.empty _)) m)).
  { apply ptree_equiv_map_reduce; [typeclasses eauto .. | ].
    rewrite ptree_equal_eq_alt.
    intros k'.
    unfold ptree_union.
    rewrite PTree.gcombine; [|easy].
    ptree_simplify; try congruence.
    now destruct (m!k'). }
  transitivity
   (r (ptree_map_reduce f r e (PTree.set k x (PTree.empty _))) (ptree_map_reduce f r e m)).
  { apply ptree_disjoint_map_reduce; [typeclasses eauto..|].
    unfold ptree_disjoint.
    intros k' y z.
    ptree_simplify; congruence. }
  f_equal.
  now rewrite ptree_map_reduce_singleton; [|typeclasses eauto..].
Qed.

Corollary ptree_remove_map_reduce
  A B m k x (f:positive->A->B)
        r {_:Associative eq r} {_:Commutative eq r}
        e {_:LeftNeutral eq r e} :
  m!k = Some x ->
  ptree_map_reduce f r e m =
               r (f k x) (ptree_map_reduce f r e (PTree.remove k m)).
Proof.
  intros h.
  set (m' := PTree.remove k m).
  transitivity (ptree_map_reduce f r e (PTree.set k x m')).
  { apply ptree_equiv_map_reduce; [typeclasses eauto .. | ].
    rewrite ptree_equal_eq_alt.
    intros k'.
    unfold m'; clear m'.
    ptree_simplify; congruence. }
  apply ptree_set_map_reduce; [typeclasses eauto .. | ].
  unfold m'; clear m'.
  ptree_simplify; congruence.
Qed.



Import List.

Fixpoint plr {A B} (R:A->B->Prop) (l₁:list A) (l₂:list B) : Prop :=
  match l₁,l₂ with
  | [] , [] => True
  | a::l₁ , b::l₂ => R a b /\ plr R l₁ l₂
  | _ , _ => False
  end
.

Instance plr_transitive A (R:A->A->Prop) {_:Transitive R} : Transitive (plr R).
Proof.
  unfold Transitive.
  intros l₁.
  induction l₁ as [ | a l₁ hl ].
  - (* l₁ = [] *)
    intros [] []; easy.
  - (* l₁ = a::l₁ *)
    intros [| b l₂] [| c l₃ ]; try easy.
    simpl.
    intros [ ? ? ] [ ? ? ].
    split.
    { solve_transitivity. }
    eapply hl; eauto.
Qed.

Instance plr_reflexive A (R:A->A->Prop) {_:Reflexive R} : Reflexive (plr R).
Proof.
  unfold Reflexive.
  intros l.
  induction l as [ | a l hl ].
  - (* l = [] *)
    easy.
  - (* l = a::l *)
    simpl; intuition.
Qed.

Instance plr_symmetric A (R:A->A->Prop) {_:Symmetric R} : Symmetric (plr R).
Proof.
  unfold Symmetric.
  intros l₁.
  induction l₁ as [ | a l₁ hl ].
  - (* l₁ = [] *)
    intros []; easy.
  - (* l₁ = a::l₁ *)
    intros [ | b l₂]; [easy|].
    simpl.
    intuition.
Qed.

Instance plr_preorder A (R:A->A->Prop) {_:PreOrder R} : PreOrder (plr R).
Proof. split; typeclasses eauto. Qed.

Instance plr_equivalence A (R:A->A->Prop) {_:Equivalence R} : Equivalence (plr R).
Proof. split; typeclasses eauto. Qed.

(** spiwack: as per now I only use that lemma in the case where [r] is
    associative and commutative with respect to the equality. If we
    are to generalise this lemma, we could use something based on the
    [subrelation] typeclass. However, that would inlvolve a relation
    which is not mentionned in the goal. *)

Instance list_reduce_proper A (R:A->A->Prop) {_:Reflexive R} r {rp:Proper (R==>R==>R) r} :
  Proper (R==>plr R==>R) (list_reduce r).
Proof.
  unfold Proper, respectful.
  intros e₁ e₂ h l₁; revert e₁ e₂ h.
  induction l₁ as [ | a l₁ hl₁ ].
  - (* l₁ = [] *)
    intros e₁ e₂ h []; [ | easy].
    simpl; intros _.
    assumption.
  - (* l₁ = a::l₁ *)
    intros e₁ e₂ h₁ [| b l₂ ]; [ easy |].
    intros [ h₂ h₃ ].
    simpl.
    apply hl₁.
    + apply rp; assumption.
    + assumption.
Qed.

(* That would work for any relation on [A] not just [eq], but I fear
   it would confuse typeclass inference.*)
Instance list_map_plr A B (R:B->B->Prop) {_:Reflexive R} :
  Proper ((eq==>R)==>plr eq==>plr R) (@List.map A B).
Proof.
  unfold Proper, respectful.
  intros f g f_sub_g.
  intros l₁.
  induction l₁ as [ | a l₁ hl ].
  - (* l₁ = [] *)
    intros []; [|easy].
    easy.
  - intros [|b l₂]; [easy|].
    simpl.
    intros [ <- l₁_eq_l₂ ].
    split; eauto.
Qed.
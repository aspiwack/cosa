Require Import Cosa.Lib.Header.
Require Import Cosa.Lib.Relation.
Require Import Cosa.Lib.Predicate.
Require Import Cosa.Lib.MapReduce.
Require Import Cosa.Concrete.ConcreteFragment.
Import Values.
Import List.ListNotations.
Require Import Coq.Lists.SetoidPermutation.

(** The bare graphs consitute the memory model of the shape domain.
    They are to be paired with a numerical domain to make a complete
    abstract domain. *)

(** Basic types *)

(** Types of the nodes of the graph. *)
Definition node : Type := positive.
Definition node_eq_dec := Pos.eq_dec.

Instance node_eq_dec_inst : EquivDec.EqDec node eq.
Proof. exact node_eq_dec. Qed.

Module NodeTree := PTree.

(** In this version offsets are concrete [int], however, in more
    fine-grain world, they would be abstract expressions. *)
Definition offs := int.

(** Representation of pointers in the abstract graph. *)
Definition off_node := (node * int)%type.

Notation valuation := (node -> val).


(** Concrete states *)


(** A graph contretises to a pair of a valuation and a concrete heap
    fragment.  The valuation maps nodes to their addresses or their
    numerical value. *)
Definition conc := (valuation * ConcreteFragment.fragment)%type.

(** We extend the separating star on concrete heap fragments to
    concrete graph representations. *)
Definition star : conc -> conc -> conc -> Prop := Relation.pair teq ConcreteFragment.star.
Definition estar := extension2 star.

Definition empty (s:conc) : Prop := ConcreteFragment.empty (snd s).

Lemma empty_spec : empty = Predicate.pair (fun _ => True) ConcreteFragment.empty.
Proof.
  apply Predicate.equiv_eq; intro s.
  unfold empty, Predicate.pair.
  firstorder.
Qed.

Instance star_associative : Associative eq estar.
Proof.
  unfold estar; typeclasses eauto.
Qed.

Instance star_commutative : Commutative eq estar.
Proof.
  unfold estar; typeclasses eauto.
Qed.

Instance star_empty_neutral : LeftNeutral eq estar empty.
Proof.
  rewrite empty_spec; unfold estar; typeclasses eauto.
Qed.

Instance estar_increasing : Proper (Subset==>Subset==>Subset) estar.
Proof.
  unfold estar; typeclasses eauto.
Qed.

Lemma estar_continuous_2 I (x:℘ conc) (f:I->℘ conc):
  estar x (Join (Γ:=[conc]) f) = Join (Γ:=[conc]) (fun i => estar x (f i)).
Proof.
  unfold estar.
  apply extension2_continuous_2.
Qed.


(** Definition of the graph itself *)


(** Abstract representation for a block. The idea is that a node is
    either a numerical value or a block. Numerical values in a block
    will therefore be represented as an extra indirection. In pointers
    pointing to a value node, the offset must be 0.

    In Xisa, blocks have a number of meta data that we shall ignore in
    a first step. These meta data are not crucial for correction, and
    can be added easily later. *)
Record pt_edge := {
  destination : off_node;
  size : AST.memory_chunk
}.

Definition block := list (offs*pt_edge).

Inductive γ_point_to₀ (α:node) (o:offs) (c:AST.memory_chunk) (β:node) (o':offs) (f:fragment) (ν:valuation) : Prop :=
| γ_point_to_offs : forall b i b' i',
    ν α = Vptr b i ->
    snd f = memory_range b (Int.add i o) c ->
    ν β = Vptr b' i' ->
    ConcreteFragment.reads f c b o (Vptr b' (Int.add i' o')) ->
    γ_point_to₀ α o c β o' f ν
| γ_point_to_normal : forall b i,
    ν α = Vptr b i ->
    snd f = memory_range b (Int.add i o) c ->
    o' = Int.zero ->
    ConcreteFragment.reads f c b o (ν β) ->
    γ_point_to₀ α o c β o' f ν
.

Definition γ_point_to α o c β o' : ℘ conc :=
  fun s => γ_point_to₀ α o c β o' (snd s) (fst s)
.


Definition γ_block (α:node) (b:block) : ℘ conc :=
  list_reduce estar empty (
      List.map (fun edge =>
                  γ_point_to α 
                             (fst edge)
                             (snd edge).(size)
                             (fst (snd edge).(destination))
                             (snd (snd edge).(destination))
      ) b
  )
.

Section Graph.

  (** Graphs contain both "point to edges" representing individual
      memory cells, and summarised edges which stands for larger
      regions. Summarised edges are instantiated to inductive region
      and inductive segment in [Cosa.Shape.Inductive]. *)

  Context {summary:Type} (γ_summary : summary -> node -> ℘ conc).

  Inductive edge :=
  | Point_to (b:block)
  | Summarized (s:summary)
  .

  Definition γ_edge (α:node) (e:edge) :=
    match e with
    | Point_to b => γ_block α b
    | Summarized s => γ_summary s α
    end
  .

  Definition t := NodeTree.t edge.

  Definition equiv : t -> t -> Prop := PTree_Properties.Equal (eqA:=eq) _.

  Global Instance equiv_equivalence : Equivalence equiv.
  Proof.
    unfold equiv.
    apply PTree_Properties.Equal_Equivalence.
  Qed.

  Lemma equiv_alt g₁ g₂ : equiv g₁ g₂ <-> (forall α, g₁!α = g₂!α).
  Proof. apply ptree_equal_eq_alt. Qed.

  Definition γ := ptree_map_reduce γ_edge estar empty.

  Lemma γ_equiv g₁ g₂ : equiv g₁ g₂ -> γ g₁ = γ g₂.
  Proof.
    intros h.
    apply ptree_permutation_equiv in h.
    unfold γ.
    rewrite !ptree_map_reduce_spec.
    rewrite h.
    reflexivity.
  Qed.

  Lemma γ_disjoint_union (g₁ g₂:t) :
    ptree_disjoint g₁ g₂ ->
    γ (ptree_union g₁ g₂) = estar (γ g₁) (γ g₂).
  Proof.
    intros g₁_g₂_d.
    unfold γ.
    apply ptree_disjoint_map_reduce; (typeclasses eauto||assumption).
  Qed.

  (** This theorem (following from the continuity of [estar]) can be
      seen as the crux of edge unfolding. It is, however, unused. *)
  Theorem star_disjoint_union I (g₁ g₂:t) (g:I->t) :
    ptree_disjoint g₁ g₂ ->
    γ g₂ ⊆ Join (Γ:=[conc]) (fun i => γ (g i)) ->
    (forall i, ptree_disjoint g₁ (g i)) ->
    γ (ptree_union g₁ g₂) ⊆ Join (Γ:=[conc]) (fun i => γ (ptree_union g₁ (g i))).
  Proof.
    intros g₁_g₂_d g_spec g₁_g_d.
    rewrite γ_disjoint_union; [|assumption].
    rewrite g_spec.
    rewrite estar_continuous_2.
    apply Join_increasing; rewrite sub_cons; intro i.
    rewrite γ_disjoint_union; [|eauto].
    reflexivity.
  Qed.

  Lemma single_out_one_edge (g:t) α :
    forall e, g!α = Some e ->
    γ g = estar (γ (NodeTree.remove α g)) (γ_edge α e).
  Proof.
    intros * h.
    set (g' := NodeTree.remove α g).
    set (gα := NodeTree.set α e (NodeTree.empty _)).
    assert (ptree_disjoint g' gα) as g'_gα_d.
    { unfold ptree_disjoint.
      intros β e₁ e₂ hg' hgα.
      unfold g',gα in hg',hgα.
      ptree_simplify;congruence. }
    assert (Graph.equiv g (ptree_union g' gα)) as g_g'_gα.
    { unfold Graph.equiv,PTree_Properties.Equal.
      intros β.
      generalize (node_eq_dec α β).
      intros [ <- | α_neq_β ].
      + rewrite h.
        unfold ptree_union.
        rewrite NodeTree.gcombine; [|easy].
        unfold g',gα.
        ptree_simplify.
        reflexivity.
      + unfold ptree_union.
        rewrite NodeTree.gcombine; [|easy].
        unfold g',gα.
        ptree_simplify.
        now destruct (g!β). }
    transitivity (γ (ptree_union g' gα)).
    { now apply γ_equiv. }
    assert (γ_edge α e = γ gα) as ->.
    { unfold γ; rewrite ptree_map_reduce_spec.
      assert ([(α,e)] = PTree.elements gα) as <-.
      { clear.
        apply singleton_eq_norepet.
        { intros [β e']; split.
          - intros h.
            apply NodeTree.elements_complete in h.
            unfold gα in h.
            ptree_simplify; congruence.
          - intros h; simpl in h.
            rewrite h; clear β e' h.
            apply NodeTree.elements_correct.
            unfold gα.
            ptree_simplify; congruence. }
        apply ptree_elements_norepet. }
      simpl.
      now rewrite left_neutrality. }
    now apply γ_disjoint_union.
  Qed.

  Corollary single_out_one_edge_set (g:t) α e :
    g!α = None ->
    γ (NodeTree.set α e g) = estar (γ g) (γ_edge α e).
  Proof.
    intros h₁.
    set (g' := (NodeTree.set α e g)).
    rewrite (single_out_one_edge g' α e).
    { f_equal.
      apply γ_equiv,equiv_alt.
      intros β. unfold g'; clear g'.
      ptree_simplify; congruence. }
    unfold g'; clear g'.
    ptree_simplify; congruence.
  Qed.

  Theorem star_summarized_edge (g:t) α :
    forall sm, g!α = Some (Summarized sm) ->
    forall s:conc, s ∈ γ g ->
    exists (s₁ s₂:conc),
      s₁ ∈ γ (NodeTree.remove α g) /\ s₂ ∈ γ_summary sm α /\ star s₁ s₂ s.
  Proof.
    intros * h₁ * h₂.
    apply single_out_one_edge in h₁.
    rewrite h₁ in h₂; clear h₁.
    unfold estar,extension2 in h₂.
    destruct h₂ as [ s₁ [ s₂ [ h₁ [ h₂ h₃ ]]]].
    exists s₁; exists s₂.
    decompose_concl; eauto.
  Qed.

  Lemma γ_empty : γ (NodeTree.empty _) = empty.
  Proof.
    unfold γ; rewrite ptree_map_reduce_spec.
    replace (PTree.elements (NodeTree.empty edge)) with (@nil (positive*edge)).
    + easy.
    + assert (forall x, ~List.In x (PTree.elements (NodeTree.empty edge))) as h.
      { intros [α e] h.
        apply PTree.elements_complete in h.
        ptree_simplify; congruence. }
      destruct (PTree.elements (NodeTree.empty edge)) as [ | x l ].
      * reflexivity.
      * specialize (h x); simpl in h.
        contradiction h.
        now left.
  Qed.

  (** The valuation matters only on the node of the graph. *)

  Definition belongs_to_point_to α (o:offs) (c:AST.memory_chunk) β (o':offs) : ℘ node :=
    fun δ => δ = α \/ δ = β
  .

  Lemma valuation_not_fixed_point_to α o chunk β o' :
    forall ν f, (ν,f) ∈ γ_point_to α o chunk β o' ->
    forall ν', (forall δ, δ ∈ belongs_to_point_to α o chunk β o' -> ν' δ = ν δ) ->
    (ν',f) ∈ γ_point_to α o chunk β o'.
  Proof.
    intros * h * h₁.
    unfold belongs_to_point_to in *.
    destruct h; simpl in *.
    + eleft; eauto; simpl.
      * rewrite h₁.
        - assumption.
        - now left.
      * rewrite h₁.
        - assumption.
        - now right.
    + eright; eauto; simpl.
      * rewrite h₁.
        - assumption.
        - now left.
      * rewrite h₁.
        - assumption.
        - now right.
  Qed.

  Definition belongs_to_block α b : ℘ node :=
    (fun β => β = α) ∪ (* case where the block is empty *)
    list_reduce union ∅
                (List.map 
                   (fun oe =>
                      belongs_to_point_to
                        α (fst oe) (snd oe).(size) 
                        (fst (snd oe).(destination)) (snd (snd oe).(destination))
                   ) b
                )
  .

  Lemma valuation_not_fixed_block α b :
    forall ν f, (ν,f) ∈ γ_block α b ->
    forall ν', (forall δ, δ ∈ belongs_to_block α b -> ν' δ = ν δ) ->
    (ν',f) ∈ γ_block α b.
  Proof.
    intros * h * h₁.
    revert f h h₁.
    induction b as [ | p b hb ]; intros f h h₁.
    - (* b = [] *)
      unfold γ_block in *; simpl in *.
      unfold empty in *; simpl in *.
      assumption.
    - (* b = p::b *)
      unfold γ_block in h |- *.
      rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ].
      rewrite list_map_cons,(list_reduce_cons eq) in h; [ | typeclasses eauto .. ].
      destruct h as [ [ ν₁ f₁ ] [ [ ν₂ f₂ ] [ h₂ [ h₃ [ h₄ h₅ ]]]]]; simpl in h₄,h₅.
      destruct h₄.
      exists (ν',f₁); exists (ν',f₂).
      decompose_goal.
      + apply valuation_not_fixed_point_to with ν₁.
        * assumption.
        * intros δ hδ.
          apply h₁.
          unfold belongs_to_block;right.
          rewrite list_map_cons,(list_reduce_cons eq); [| typeclasses eauto..].
          now left.
      + apply hb.
        * assumption.
        * intros δ hδ.
          apply h₁.
          unfold belongs_to_block.
          destruct hδ; [ now left | right ].
          rewrite list_map_cons,(list_reduce_cons eq); [| typeclasses eauto..].
          now right.
      + split; simpl.
        * constructor.
        * assumption.
  Qed.

  (** spiwack: in a more general setting, summaries should control
      some nodes.  It would come as an extra piece of data of type
      [summary -> ℘ node], for instance. *)
  Definition belongs_to_summary α (sm:summary) : ℘ node :=
    fun δ => δ = α
  .

  Hypothesis valuation_not_fixed_summary : forall α sm,
    forall ν f, (ν,f) ∈ γ_summary sm α ->
    forall ν', (forall δ, δ ∈ belongs_to_summary α sm -> ν' δ = ν δ) ->
    (ν',f) ∈ γ_summary sm α.

  Definition belongs_to_edge α e : ℘ node :=
    match e with
    | Point_to b => belongs_to_block α b
    | Summarized sm => belongs_to_summary α sm
    end
  .

  Lemma valuation_not_fixed_edge α e :
    forall ν f, (ν,f) ∈ γ_edge α e ->
    forall ν', (forall δ, δ ∈ belongs_to_edge α e -> ν' δ = ν δ) ->
    (ν',f) ∈ γ_edge α e.
  Proof.
    intros * h * h₁.
    unfold γ_edge.
    destruct e as [ b | sm ].
    + (* e = Point_to b *)
      simpl in h,h₁.
      apply valuation_not_fixed_block with ν; eauto.
    + (* e = Summarized sm *)
      simpl in h,h₁.
      apply valuation_not_fixed_summary with ν; eauto.
  Qed.

  Definition belongs_to_graph (g:t) : ℘ node :=
    ptree_map_reduce belongs_to_edge union ∅ g
  .

  Global Instance belongs_to_graph_equiv : Proper (equiv ==> eq) belongs_to_graph.
  Proof.
    unfold Proper,respectful,belongs_to_graph.
    intros g₁ g₂ h.
    rewrite !ptree_map_reduce_spec.
    apply ptree_permutation_equiv in h.
    rewrite h.
    reflexivity.
  Qed.
  Global Instance belongs_to_graph_equiv' : Proper (equiv ==> eq ==> eq) belongs_to_graph.
  Proof.
    unfold Proper,respectful.
    intros g₁ g₂ h₁ α ? <-.
    apply equal_f.
    now rewrite h₁.
  Qed.

  Theorem valuation_not_fixed (g:t) :
    forall ν f, (ν,f) ∈ γ g ->
    forall ν', (forall β, β ∈ belongs_to_graph g -> ν' β = ν β) ->
    (ν',f) ∈ γ g.
  Proof.
    unfold γ at 2; unfold ptree_map_reduce.
    apply PTree_Properties.fold_rec.
    { intros g₁ g₂ P g₁_g₂ h₂ ν f h₃ ν' h₄.
      apply equiv_alt in g₁_g₂.
      eapply h₂; clear h₂.
      + apply γ_equiv in g₁_g₂; rewrite g₁_g₂.
        exact h₃.
      + intros β e.
        apply belongs_to_graph_equiv in g₁_g₂; rewrite g₁_g₂ in e.
        eauto. }
    { intros ν f h ν' h₁.
      unfold empty; simpl.
      rewrite γ_empty in h; unfold empty in h; simpl in h.
      assumption. }
    intros g' P α e h₁ h₂ h ν f h₃ ν' h₄.
    rewrite (single_out_one_edge _ α e) in h₃; [ | ptree_simplify;congruence ].
    assert (γ (NodeTree.remove α (NodeTree.set α e g')) = γ g') as r; [|rewrite r in *;clear r].
    { apply γ_equiv.
      unfold equiv,PTree_Properties.Equal. intros β.
      ptree_simplify.
      - now rewrite h₁.
      - now destruct (g'!β). }
    unfold estar,extension2 in h₃.
    destruct h₃ as [ [ ν₁ f₁ ] [ [ ν₂ f₂ ] [ h₃₁ [ h₃₂ [ h₃₃ h₃₄ ]]]]]; simpl in h₃₃,h₃₄.
    destruct h₃₃.
    unfold estar,extension2.
    exists (ν',f₁); exists (ν',f₂).
    decompose_concl.
    + eapply h; eauto.
      intros β h₅.
      apply h₄.
      unfold belongs_to_graph.
      rewrite ptree_set_map_reduce; [|typeclasses eauto..|assumption].
      now right.
    + apply valuation_not_fixed_edge with ν₁;eauto.
      intros β h₅.
      apply h₄.
      unfold belongs_to_graph.
      rewrite ptree_set_map_reduce; [|typeclasses eauto..|assumption].
      now left.
    + split; simpl.
      * constructor.
      * assumption.
  Qed.

  Lemma domain_belongs g :
    forall α e, g!α = Some e ->
    α ∈ belongs_to_graph g.
  Proof.
    unfold belongs_to_graph, belongs_to_graph, ptree_map_reduce.
    apply PTree_Properties.fold_rec.
    { intros g₁ g₂ P h₁ h₂ α e h₃.
      apply h₂ with e.
      now rewrite h₁. }
    { intros ** h.
      ptree_simplify; congruence. }
    intros g₁ P α e h₁ h₂ h₃ β e' h₄.
    ptree_simplify.
    - right.
      destruct e; simpl.
      + unfold belongs_to_block.
        now left.
      + unfold belongs_to_summary.
        reflexivity.
    - left ; eauto.
  Qed.

End Graph.

Arguments t summary : clear implicits.


(** the concretisation are increasing with respect to the concretisation of summarized
    edges. *)
Instance γ_edge_increasing s :
  Proper (sub (Γ:=[s;node;conc]) ==> eq ==> eq ==> sub (Γ:=[conc])) γ_edge.
Proof.
  unfold Proper, respectful.
  intros γ₁ γ₂ γ₁_sub_γ₂ α ? <- e ? <-.
  unfold γ_edge.
  destruct e as [ b | sm ].
  - (* e = point_to b *)
    reflexivity.
  - (* e = summarized sm *)
    simpl in *.
    eauto.
Qed.

Instance γ_increasing s :
  Proper (sub (Γ:=[s;node;conc]) ==> equiv ==> sub (Γ:=[conc])) γ.
Proof.
  unfold Proper, respectful.
  intros γ₁ γ₂ γ₁_sub_γ₂ g₁ g₂ g₁_eq_g₂.
  eapply γ_equiv in g₁_eq_g₂.
  rewrite <- g₁_eq_g₂; clear g₂ g₁_eq_g₂.
  unfold γ.
  rewrite !ptree_map_reduce_spec.
  apply list_reduce_proper.
  { typeclasses eauto. }
  { typeclasses eauto. }
  { reflexivity. }
  apply list_map_plr; [ typeclasses eauto | | reflexivity ].
  unfold respectful.
  intros e ? <-.
  rewrite γ₁_sub_γ₂.
  reflexivity.
Qed.
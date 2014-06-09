Require Import Cosa.Lib.Header.
Require Import Cosa.Lib.Relation.
Require Import Cosa.Lib.Predicate.
Require Import Cosa.Lib.MapReduce.
Require Import Cosa.Concrete.ConcreteFragment.
Require Import Cosa.Abstract.Valuation.
Import Coq.Classes.EquivDec.
Import Values.
Import List.ListNotations.
Require Import Coq.Lists.SetoidPermutation.
Require Import Cosa.Nominal.Set.
Require Import Cosa.Nominal.CompcertInstances.

(** The bare graphs consitute the memory model of the shape domain.
    They are to be paired with a numerical domain to make a complete
    abstract domain. *)

(** Basic types *)

(** Types of the nodes of the graph. *)
Definition node : Type := Atom.
Instance node_nominal : Nominal node := perm_nominal.

Definition node_eq_dec := Pos.eq_dec.

Instance node_eq_dec_inst : EquivDec.EqDec node eq.
Proof. exact node_eq_dec. Qed.

Module NodeTree := AtomTree.

(** In this version offsets are concrete [int], however, in more
    fine-grain world, they would be abstract expressions. *)
Definition offs := int.
Instance offs_nominal : Nominal offs := discrete_nominal.

(** Representation of pointers in the abstract graph. *)
Definition off_node := (node * offs)%type.

(** Spiwack: I'm really not sure it matters wether valuation are
    finitely supported or not.  Concretely a finitely supported
    valuation is constant except on a finite set of atoms. This is not
    unreasonable to ask, but it may prove harder to achieve than
    expected. And it may not be needed, after all, what really matter
    are sets of valuations. Truth be told: this file seems indifferent
    to whether valuations are finitely supported or not. Up to the
    fact, of course, that some [Nominal] instances would have to be
    changed into [Action]. So we'll see in further files which choice
    works best. *)
Notation valuation := (node -fs-> val).


(** Concrete states *)


(** A graph contretises to a pair of a valuation and a concrete heap
    fragment.  The valuation maps nodes to their addresses or their
    numerical value. *)
Definition conc := (valuation * ConcreteFragment.fragment)%type.
Hint Unfold conc : equivariant.

Instance fragment_nominal : Nominal ConcreteFragment.fragment :=
  Nominal.Set.discrete_nominal
.

Program Instance conc_nominal : Nominal conc := prod_nominal _ _ _ _ .

(** We extend the separating star on concrete heap fragments to
    concrete graph representations. *)
Definition star : conc -> conc -> conc -> Prop := Relation.pair teq ConcreteFragment.star.
Definition estar := extension2 star.

Lemma equivariant_teq (A:Type) `(Action A) : Equivariant teq.
Proof.
  apply equivariant_alt₃.
  intros π x y z. simpl. apply prop_extensionality.
  assert (forall π x y z, teq x y z -> teq (π·x) (π·y) (π·z)) as h.
  { clear. intros π x y z [].
    constructor. }
  split.
  + intros h'. eapply (h (op_p π)) in h'.
    solve_act.
  + eauto.
Qed.
Hint EResolve equivariant_teq : equivariant.

Lemma equivariant_fragment_star : Equivariant ConcreteFragment.star.
Proof. easy. Qed.
Hint EResolve equivariant_fragment_star : equivariant.

Lemma equivariant_relation_pair
      A `(Action A) (r₁:A->A->A->Prop) B `(Action B) :
      Equivariant r₁ -> Equivariant (Relation.pair r₁).
Proof.
  intros h.
  apply equivariant_alt₁. intros π r₂.
  unfold Relation.pair.
  extensionality x; extensionality y; extensionality z. simpl.
  eapply equivariant_alt₃ in h.
  erewrite h. simpl.
  reflexivity.
Qed.
Hint EResolve equivariant_relation_pair : equivariant.


(** Help the proof search when there is [conc] instead of an explicit product. *)
Corollary equivariant_relation_pair_conc (r₁:valuation->valuation->valuation->Prop) :
          Equivariant r₁ ->
          @Equivariant ((fragment->fragment->fragment->Prop)->conc->conc->conc->Prop) _
                       (@Relation.pair valuation r₁ ConcreteFragment.fragment).
Proof. refine (equivariant_relation_pair _ _ _ _ _). Qed.
Hint EResolve equivariant_relation_pair_conc : equivariant.

Lemma equivariant_star : Equivariant star.
Proof. unfold star. narrow_equivariant. Qed.
Hint EResolve equivariant_star : equivariant.

Lemma equivariant_extension2 A `(Action A) B `(Action B) C `(Action C) :
  Equivariant (@extension2 A B C).
Proof.
  apply equivariant_alt₁. intros π r.
  extensionality p; extensionality q; extensionality z. unfold extension2. simpl.
  apply prop_extensionality. simplify_act.
  firstorder (simplify_act; firstorder).
Qed.
Hint EResolve equivariant_extension2 : equivariant.

Corollary equivariant_estar : Equivariant estar.
Proof. narrow_equivariant. Qed.
Hint EResolve equivariant_estar : equivariant.

Definition empty (s:conc) : Prop := ConcreteFragment.empty (snd s).

Lemma empty_equivariant : Equivariant empty.
Proof. now unfold Equivariant. Qed.
Hint EResolve empty_equivariant : equivariant.

Lemma empty_spec : empty = Predicate.pair (fun _ => True) ConcreteFragment.empty.
Proof.
  apply Predicate.equiv_eq; intro s.
  unfold empty, Predicate.pair.
  firstorder.
Qed.

Instance star_associative : Associative eq estar.
Proof. unfold estar; typeclasses eauto. Qed.

Instance star_commutative : Commutative eq estar.
Proof. unfold estar; typeclasses eauto. Qed.

Instance star_empty_neutral : LeftNeutral eq estar empty.
Proof. rewrite empty_spec; unfold estar; typeclasses eauto. Qed.

Instance estar_increasing : Proper (Subset==>Subset==>Subset) estar.
Proof. unfold estar; typeclasses eauto. Qed.

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
    a first step. These meta data are not crucial for correctness, and
    can be added easily later. *)
Record pt_edge := {
  destination : off_node;
  size : AST.memory_chunk
}.

Program Instance pt_edge_nominal : Nominal pt_edge :=
  nominal_of_iso
    (fun e => (e.(destination),e.(size)))
    (fun e' => {| destination := fst e' ; size := snd e' |})
    _ _
.
Next Obligation.
  (* [x] should not have been introduced. *)
  revert x.
  (* / *)
  intros [].
  easy.
Qed.

Remark equivariant_destination : Equivariant destination.
Proof. now apply equivariant_alt₁. Qed.
Hint EResolve equivariant_destination : equivariant.

Remark equivariant_size : Equivariant size.
Proof. now apply equivariant_alt₁. Qed.
Hint EResolve equivariant_size : equivariant.

Definition block := list (offs*pt_edge).

Instance block_nominal : Nominal block := list_nominal _ _.

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
  Context {summary_nominal:Nominal summary} (equivariant_γ_summary : Equivariant γ_summary).
  Hint EResolve equivariant_γ_summary : equivariant.
  

  Inductive edge :=
  | Point_to (b:block)
  | Summarized (s:summary)
  .

  Program Instance edge_nominal : Nominal edge :=
    nominal_of_iso
      (fun e =>
         match e return _ with Point_to b => inl b | Summarized s => inr s end)
      (fun e =>
         match e return _ with inl b => Point_to b | inr s => Summarized s end)
      _ _
  .
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    intros [|]; easy.
  Qed.
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    intros [|]; easy.
  Qed.

  Definition γ_edge (α:node) (e:edge) :=
    match e with
    | Point_to b => γ_block α b
    | Summarized s => γ_summary s α
    end
  .

  Definition t := NodeTree.t edge.

  Global Instance graph_nominal : Nominal t := Nominal.Set.map_nominal _ _.

  Definition equiv : t -> t -> Prop := AtomTree_Properties.Equal (eqA:=eq) _.

  Global Instance equiv_equivalence : Equivalence equiv.
  Proof.
    unfold equiv.
    apply AtomTree_Properties.Equal_Equivalence.
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
      CPTree.simplify;congruence. }
    assert (Graph.equiv g (ptree_union g' gα)) as g_g'_gα.
    { unfold Graph.equiv,AtomTree_Properties.Equal.
      intros β.
      generalize (node_eq_dec α β).
      intros [ <- | α_neq_β ].
      + rewrite h.
        unfold ptree_union.
        rewrite NodeTree.gcombine; [|easy].
        unfold g',gα.
        CPTree.simplify.
        reflexivity.
      + unfold ptree_union.
        rewrite NodeTree.gcombine; [|easy].
        unfold g',gα.
        CPTree.simplify.
        now destruct (g!β). }
    transitivity (γ (ptree_union g' gα)).
    { now apply γ_equiv. }
    assert (γ_edge α e = γ gα) as ->.
    { unfold γ; rewrite ptree_map_reduce_spec.
      assert ([(α,e)] = AtomTree.elements gα) as <-.
      { clear.
        apply singleton_eq_norepet.
        { intros [β e']; split.
          - intros h.
            apply NodeTree.elements_complete in h.
            unfold gα in h.
            CPTree.simplify; congruence.
          - intros h; simpl in h.
            rewrite h; clear β e' h.
            apply NodeTree.elements_correct.
            unfold gα.
            CPTree.simplify; congruence. }
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
      CPTree.simplify; congruence. }
    unfold g'; clear g'.
    CPTree.simplify; congruence.
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
    replace (AtomTree.elements (NodeTree.empty edge)) with (@nil (positive*edge)).
    + easy.
    + assert (forall x, ~List.In x (AtomTree.elements (NodeTree.empty edge))) as h.
      { intros [α e] h.
        apply AtomTree.elements_complete in h.
        CPTree.simplify; congruence. }
      destruct (AtomTree.elements (NodeTree.empty edge)) as [ | x l ].
      * reflexivity.
      * specialize (h x); simpl in h.
        contradiction h.
        now left.
  Qed.

  (** The concretisation is equivariant. *)

  (* arnaud: Notation a deplacer *)
  Notation "`⟨ x ⟩" := (exist _ x _).

  Lemma γ_point_to_equivariant : Equivariant γ_point_to.
  Proof.
    rewrite equivariant_alt₁.
    intros π α.
    apply act_float_l. simpl.
    extensionality o;
      extensionality c; extensionality β; extensionality o'; extensionality νf.
    destruct νf as [ν f]. unfold γ_point_to. simpl.
    apply prop_extensionality.
    assert (forall π α o c β o' ν f,
              γ_point_to₀ (π·α) o c (π·β) o' f (π·ν) -> γ_point_to₀ α o c β o' f ν) as h.
    (* arnaud: voir `a utiliser solve_act dans cette sous-preuve *)
    { clear. intros * [ b i b' i' h₁ h₂ h₃ h₄ | b i h₁ h₂ h₃ h₄ ];
        econstructor (solve[
          simpl in *;
          rewrite <- ?perm_comp', ?op_p_spec_l in *|-; simpl in *;
          eassumption]). }
    split.
    + intros h₁.
      eapply h.
      apply_eq h₁.
      * solve_act.
      * reflexivity.
    + intros h₁.
      apply (h (op_p π)).
      (* arnaud: mettre fs_extensionality dans solve_act pour simplifier le reste de la preuve. *)
      apply_eq h₁.
      * simpl.
        now rewrite <- perm_comp', op_p_spec_l; simpl.
      * now rewrite <- perm_comp', op_p_spec_r; simpl.
      * apply fs_extensionality. extensionality δ. simpl.
        now rewrite <- perm_comp', op_p_spec_l; simpl.
  Qed.
  Hint EResolve γ_point_to_equivariant : equivariant.

  (* arnaud: peut-etre deplacer tout ca *)

  Lemma list_reduce_equivariant A `(Action A) : Equivariant (@list_reduce A).
  Proof.
    rewrite equivariant_alt₁.
    intros π f. extensionality s; extensionality l.
    revert s.
    induction l as [ | x l h ].
    + intros s. simpl.
      solve_act.
    + intros s. unfold list_reduce in *.
      simpl List.fold_left.
      rewrite h. simpl.
      solve_act.
  Qed.
  Hint EResolve list_reduce_equivariant : equivariant.

  Program Instance option_action A `(Action A) : Action (option A) := {|
    act π o := match o return _ with Some x => Some (π·x) | None => None end
  |}.
  Next Obligation.
    autounfold.
    intros π₁ π₂ hπ x y <-.
    now destruct x; rewrite ?hπ.
  Qed.
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    now intros [?|]; rewrite ?act_id.
  Qed.
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    now intros [?|]; rewrite ?act_comp.
  Qed.

  Lemma map_action_alt_eq A `(Action A) π (m:AtomTree.t A) :
    forall α, (π·m)!α = π·(m!((op_p π)·α)).
  Proof.
    assert (forall o₁ o₂:option A, (forall v, o₁ = Some v <-> o₂ = Some v) -> o₁ = o₂) as rem.
    { clear.
      destruct o₁; destruct o₂; try firstorder congruence.
      (* no idea why the last case isn't solved by [firstorder congruence] *)
      intros h. symmetry. rewrite <- h.
      easy. }
    intros α.
    apply rem. intros v.
    rewrite map_action_alt.
    rewrite <- act_float_r.
    reflexivity.
  Qed.


  Lemma equivariant_map_set A `(Action A) : Equivariant (@AtomTree.set A).
  Proof.
    apply equivariant_alt₃.
    intros π α x m.
    apply AtomTree.unicity. intros β.
    rewrite map_action_alt_eq.
    destruct (Pos.eq_dec (π·α) β) as [ <- | nβ ].
    { simplify_act.
      now AtomTree.simplify. }
    assert (α <> (op_p π)·β) as nβ'.
    { intros ?. apply nβ.
      now apply act_float_r. }
    AtomTree.simplify.
    apply map_action_alt_eq.
  Qed.
  Hint EResolve equivariant_map_set : equivariant.
    

  Lemma ptree_map_reduce_equivariant A `(Action A) B `(Action B)
    (f:node->A->B) (ef:Equivariant f)
    (r:B->B->B) (er:Equivariant r) `(Associative _ eq r) `(Commutative _ eq r)
    (n:B) (en:Equivariant n) `(LeftNeutral _ eq r n) :
    Equivariant (ptree_map_reduce f r n).
  Proof.
    unfold Equivariant, support. intros π _.
    unfold ptree_map_reduce at 2. extensionality m.
    apply AtomTree_Properties.fold_rec.
    + intros m₁ m₂ b h.
      apply AtomTree.unicity in h. rewrite <- h.
      easy.
    + apply en. intros **; AtomSet.fsetdec'.
    + intros m' b α a hk₁ hk₂ h.
      simpl. change (map_action_f A H (op_p π) (CPTree.set α a m')) with ((op_p π)·(CPTree.set α a m')).
      generalize equivariant_map_set. intros hset.
      eapply equivariant_alt₃ in hset. erewrite <- hset.
      rewrite ptree_set_map_reduce; [|typeclasses eauto ..|].
      * eapply equivariant_alt₂ in er. erewrite <- er.
        simpl in h|-*. rewrite h.
        eapply equivariant_alt₂ in ef. erewrite <- ef.
        solve_act.
      * rewrite map_action_alt_eq.
        simplify_act.
        now rewrite hk₁.
  Qed.
  Hint EResolve ptree_map_reduce_equivariant : equivariant.

(* arnaud: unused right now
  Lemma act_app_up A `(Action A) B `(Action B) π (f:A->B) (x:A) : (π·f) x = π·(f ((op_p π)·x)).
  Proof.
    reflexivity.
  Qed.

  Lemma act_app_down A `(Action A) B `(Action B) π (f:A->B) (x:A): π·(f x) = (π·f) (π·x).
  Proof.
    simpl.
    solve_act.
  Qed.

  Lemma equivariant_cancel {A} `{Action A} (f:A) :
    Equivariant f -> forall π, π·f = f.
  Proof.
    intros h π. apply h.
    intros **.
    AtomSet.fsetdec'.
  Qed.

  (* Doesn't handle the dependent product case gracefully. *)
  Ltac push_equivariant :=
    erewrite ?act_app_up; (* eliminates β-redexes *)
    erewrite ?act_app_down; (* pushes permutation as deeply as possible *)
    repeat match goal with
    | |- appcontext[?p·?f] =>
         erewrite (equivariant_cancel f);[|solve[narrow_equivariant]]
    end
  .
*)



  (* arnaud: /peut-etre deplacer tout ca *)

  Lemma γ_block_equivariant : Equivariant γ_block.
  Proof.
    unfold γ_block.
    combinatorize.
    narrow_equivariant.
  Qed.
  Hint EResolve γ_block_equivariant : equivariant.

  Lemma γ_edge_equivariant : Equivariant γ_edge.
  Proof.
    apply equivariant_alt₂.
    intros π α [e|e].
    + generalize γ_block_equivariant; intros h.
      eapply equivariant_alt₂ in h.
      eapply h.
    + eapply equivariant_alt₂ in equivariant_γ_summary.
      eapply equivariant_γ_summary.
  Qed.
  Hint EResolve γ_edge_equivariant : equivariant.

  Lemma γ_equivariant : Equivariant γ.
  Proof.
    unfold γ.
    typeclasses eauto with equivariant typeclass_instances.
  Qed.


  (* (** The valuation matters only on the node of the graph. *) *)

  (* Definition belongs_to_point_to α (o:offs) (c:AST.memory_chunk) β (o':offs) : ℘ node := *)
  (*   fun δ => δ = α \/ δ = β *)
  (* . *)

  (* (* Lemma valuation_not_fixed_point_to α o chunk β o' f: *) *)
  (* (*   central (belongs_to_point_to α o chunk β o') *) *)
  (* (*           (fun ν => (ν,f) ∈ γ_point_to α o chunk β o'). *) *)
  (* (* Proof. *) *)
  (* (*   unfold central. intros δ γ hδ hγ ν h₁. *) *)
  (* (*   unfold belongs_to_point_to in *. *) *)
  (* (*   destruct h₁; simpl in *. *) *)
  (* (*   + eleft; eauto; simpl. *) *)
  (* (*     * unfold Valuation.swap. *) *)
  (* (*       destruct (α == δ) as [ <- | _ ]. *) *)
  (* (*       { clear -hδ; firstorder. } *) *)
  (* (*       destruct (α == γ) as [ <- | _ ]. *) *)
  (* (*       { clear -hγ; firstorder. } *) *)
  (* (*       easy. *) *)
  (* (*     * unfold Valuation.swap. *) *)
  (* (*       destruct (β == δ) as [ <- | _ ]. *) *)
  (* (*       { clear -hδ; firstorder. } *) *)
  (* (*       destruct (β == γ) as [ <- | _ ]. *) *)
  (* (*       { clear -hγ; firstorder. } *) *)
  (* (*       easy. *) *)
  (* (*   + eright; eauto; simpl. *) *)
  (* (*     * unfold Valuation.swap. *) *)
  (* (*       destruct (α == δ) as [ <- | _ ]. *) *)
  (* (*       { clear -hδ; firstorder. } *) *)
  (* (*       destruct (α == γ) as [ <- | _ ]. *) *)
  (* (*       { clear -hγ; firstorder. } *) *)
  (* (*       easy. *) *)
  (* (*     * replace (Valuation.swap δ γ ν β) with (ν β). *) *)
  (* (*       { easy. } *) *)
  (* (*       unfold Valuation.swap. *) *)
  (* (*       destruct (β == δ) as [ <- | _ ]. *) *)
  (* (*       { clear -hδ; firstorder. } *) *)
  (* (*       destruct (β == γ) as [ <- | _ ]. *) *)
  (* (*       { clear -hγ; firstorder. } *) *)
  (* (*       easy. *) *)
  (* (* Qed. *) *)

  (* Definition belongs_to_block α b : ℘ node := *)
  (*   (fun β => β = α) ∪ (* case where the block is empty *) *)
  (*   list_reduce union ∅ *)
  (*               (List.map  *)
  (*                  (fun oe => *)
  (*                     belongs_to_point_to *)
  (*                       α (fst oe) (snd oe).(size)  *)
  (*                       (fst (snd oe).(destination)) (snd (snd oe).(destination)) *)
  (*                  ) b *)
  (*               ) *)
  (* . *)

  (* (* Lemma valuation_not_fixed_block α b f : *) *)
  (* (*   central (belongs_to_block α b) *) *)
  (* (*           (fun ν => (ν,f) ∈ γ_block α b). *) *)
  (* (* Proof. *) *)
  (* (*   unfold central. intros β δ hβ hδ ν. revert f. *) *)
  (* (*   induction b as [ | p b hb ]; intros f h₁. *) *)
  (* (*   - (* b = [] *) *) *)
  (* (*     unfold γ_block in *; simpl in *. *) *)
  (* (*     unfold empty in *; simpl in *. *) *)
  (* (*     assumption. *) *)
  (* (*   - (* b = p::b *) *) *)
  (* (*     unfold γ_block in h₁ |- *. *) *)
  (* (*     rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ]. *) *)
  (* (*     rewrite list_map_cons,(list_reduce_cons eq) in h₁; [ | typeclasses eauto .. ]. *) *)
  (* (*     destruct h₁ as [ [ ν₁ f₁ ] [ [ ν₂ f₂ ] [ h₂ [ h₃ [ h₄ h₅ ]]]]]; simpl in h₄,h₅. *) *)
  (* (*     destruct h₄. *) *)
  (* (*     exists (Valuation.swap β δ ν₁,f₁); exists (Valuation.swap β δ ν₁,f₂). *) *)
  (* (*     decompose_concl. *) *)
  (* (*     + apply valuation_not_fixed_point_to. *) *)
  (* (*       * clear -hβ; unfold belongs_to_block in hβ. *) *)
  (* (*         intros h. *) *)
  (* (*         apply hβ. *) *)
  (* (*         right. *) *)
  (* (*         rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ]. *) *)
  (* (*         now left. *) *)
  (* (*       * clear -hδ; unfold belongs_to_block in hδ. *) *)
  (* (*         intros h. *) *)
  (* (*         apply hδ. *) *)
  (* (*         right. *) *)
  (* (*         rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ]. *) *)
  (* (*         now left. *) *)
  (* (*       * assumption. *) *)
  (* (*     + apply hb. *) *)
  (* (*       * clear -hβ; unfold belongs_to_block in hβ. *) *)
  (* (*         intros h. *) *)
  (* (*         apply hβ. *) *)
  (* (*         destruct h. *) *)
  (* (*         { now left. } *) *)
  (* (*         right. *) *)
  (* (*         rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ]. *) *)
  (* (*         now right. *) *)
  (* (*       * clear -hδ; unfold belongs_to_block in hδ. *) *)
  (* (*         intros h. *) *)
  (* (*         apply hδ. *) *)
  (* (*         destruct h. *) *)
  (* (*         { now left. } *) *)
  (* (*         right. *) *)
  (* (*         rewrite list_map_cons,(list_reduce_cons eq); [ | typeclasses eauto .. ]. *) *)
  (* (*         now right. *) *)
  (* (*       * apply h₃. *) *)
  (* (*     + split; simpl. *) *)
  (* (*       { constructor. } *) *)
  (* (*       assumption. *) *)
  (* (* Qed. *) *)

  (* (** spiwack: in a more general setting, summaries should control *)
  (*     some nodes.  It would come as an extra piece of data of type *)
  (*     [summary -> ℘ node], for instance. *) *)
  (* Definition belongs_to_summary α (sm:summary) : ℘ node := *)
  (*   fun δ => δ = α *)
  (* . *)

  (* (* Hypothesis valuation_not_fixed_summary : forall α sm f, *) *)
  (* (*   central (belongs_to_summary α sm) *) *)
  (* (*           (fun ν => (ν,f) ∈ γ_summary sm α). *) *)

  (* Definition belongs_to_edge α e : ℘ node := *)
  (*   match e with *)
  (*   | Point_to b => belongs_to_block α b *)
  (*   | Summarized sm => belongs_to_summary α sm *)
  (*   end *)
  (* . *)
  
  (* (* Lemma valuation_not_fixed_edge α e f : *) *)
  (* (*   central (belongs_to_edge α e) *) *)
  (* (*           (fun ν => (ν,f) ∈ γ_edge α e). *) *)
  (* (* Proof. *) *)
  (* (*   unfold central. intros β δ hβ hδ ν h₁. *) *)
  (* (*   unfold γ_edge. *) *)
  (* (*   destruct e as [ b | sm ]. *) *)
  (* (*   + (* e = Point_to b *) *) *)
  (* (*     simpl in h₁. *) *)
  (* (*     apply valuation_not_fixed_block; eauto. *) *)
  (* (*   + (* e = Summarized sm *) *) *)
  (* (*     simpl in h₁. *) *)
  (* (*     apply valuation_not_fixed_summary; eauto. *) *)
  (* (* Qed. *) *)

  (* Definition belongs_to_graph (g:t) : ℘ node := *)
  (*   ptree_map_reduce belongs_to_edge union ∅ g *)
  (* . *)

  (* Global Instance belongs_to_graph_equiv : Proper (equiv ==> eq) belongs_to_graph. *)
  (* Proof. *)
  (*   unfold Proper,respectful,belongs_to_graph. *)
  (*   intros g₁ g₂ h. *)
  (*   rewrite !ptree_map_reduce_spec. *)
  (*   apply ptree_permutation_equiv in h. *)
  (*   rewrite h. *)
  (*   reflexivity. *)
  (* Qed. *)
  (* Global Instance belongs_to_graph_equiv' : Proper (equiv ==> eq ==> eq) belongs_to_graph. *)
  (* Proof. *)
  (*   unfold Proper,respectful. *)
  (*   intros g₁ g₂ h₁ α ? <-. *)
  (*   apply equal_f. *)
  (*   now rewrite h₁. *)
  (* Qed. *)

  (* Lemma belongs_to_graph_remove (g:t) α : *)
  (*   forall β,  β ∈ belongs_to_graph (NodeTree.remove α g) -> β ∈ belongs_to_graph g. *)
  (* Proof. *)
  (*   intros *. *)
  (*   destruct (g!α) as [ e | ] eqn:h₁. *)
  (*   + (* g!α = Some e *) *)
  (*     set (g' := NodeTree.remove α g). *)
  (*     assert (equiv g (NodeTree.set α e g')) as h₂. *)
  (*     { apply equiv_alt; intros δ. *)
  (*       unfold g'; clear g'. *)
  (*       CPTree.simplify; congruence. } *)
  (*     intros h₃. *)
  (*     erewrite belongs_to_graph_equiv'; [|eauto..]. *)
  (*     unfold belongs_to_graph in *. *)
  (*     rewrite ptree_set_map_reduce; [|typeclasses eauto..|]. *)
  (*     * now right. *)
  (*     * unfold g' in *; clear g'. *)
  (*       CPTree.simplify; congruence. *)
  (*   + (* g!α = None *) *)
  (*     rewrite belongs_to_graph_equiv'; eauto. *)
  (*     apply equiv_alt; intros δ. *)
  (*     CPTree.simplify; congruence. *)
  (* Qed. *)

  (* (* Theorem valuation_not_fixed (g:t) f : *) *)
  (* (*   central (belongs_to_graph g) *) *)
  (* (*           (fun ν => (ν,f) ∈ γ g). *) *)
  (* (* Proof. *) *)
  (* (*   revert f; unfold γ; unfold ptree_map_reduce. *) *)
  (* (*   apply AtomTree_Properties.fold_rec. *) *)
  (* (*   { intros g₁ g₂ P g₁_g₂ h₂ f α β h₃ h₄ ν' h₅. *) *)
  (* (*     apply equiv_alt in g₁_g₂. *) *)
  (* (*     eapply h₂; clear h₂. *) *)
  (* (*     + intros h; apply h₃. *) *)
  (* (*       now apply belongs_to_graph_equiv in g₁_g₂; rewrite <- g₁_g₂. *) *)
  (* (*     + intros h; apply h₄. *) *)
  (* (*       now apply belongs_to_graph_equiv in g₁_g₂; rewrite <- g₁_g₂. *) *)
  (* (*     + assumption. } *) *)
  (* (*   { intros f α β hα hβ ν h. *) *)
  (* (*     unfold empty; simpl. *) *)
  (* (*     unfold empty in h; simpl in h. *) *)
  (* (*     assumption. } *) *)
  (* (*   intros g' P α e h₁ h₂ h f β δ hβ hδ ν h₃. *) *)
  (* (*   destruct h₃ as [ [ ν₁ f₁ ] [ [ ν₂ f₂ ] [ h₃₁ [ h₃₂ [ h₃₃ h₃₄ ]]]]]; simpl in h₃₃,h₃₄. *) *)
  (* (*   destruct h₃₃. *) *)
  (* (*   exists (Valuation.swap β δ ν₁,f₁); exists (Valuation.swap β δ ν₁,f₂). *) *)
  (* (*   decompose_concl. *) *)
  (* (*   + apply h. *) *)
  (* (*     * clear -h₁ hβ. *) *)
  (* (*       intros h; apply hβ. *) *)
  (* (*       unfold belongs_to_graph. *) *)
  (* (*       rewrite ptree_set_map_reduce; [|typeclasses eauto..|easy]. *) *)
  (* (*       now right. *) *)
  (* (*     * clear -h₁ hδ. *) *)
  (* (*       intros h; apply hδ. *) *)
  (* (*       unfold belongs_to_graph. *) *)
  (* (*       rewrite ptree_set_map_reduce; [|typeclasses eauto..|easy]. *) *)
  (* (*       now right. *) *)
  (* (*     * assumption. *) *)
  (* (*   + apply valuation_not_fixed_edge. *) *)
  (* (*     * clear -h₁ hβ. *) *)
  (* (*       intros h; apply hβ. *) *)
  (* (*       unfold belongs_to_graph. *) *)
  (* (*       rewrite ptree_set_map_reduce; [|typeclasses eauto..|easy]. *) *)
  (* (*       now left. *) *)
  (* (*     * clear -h₁ hδ. *) *)
  (* (*       intros h; apply hδ. *) *)
  (* (*       unfold belongs_to_graph. *) *)
  (* (*       rewrite ptree_set_map_reduce; [|typeclasses eauto..|easy]. *) *)
  (* (*       now left. *) *)
  (* (*     * assumption. *) *)
  (* (*   + constructor; simpl. *) *)
  (* (*     * constructor. *) *)
  (* (*     * assumption. *) *)
  (* (* Qed. *) *)

  (* (* Corollary valuation_not_fixed_iter (g:t) : *) *)
  (* (*   forall (p:permutation), permutation_not_in p (belongs_to_graph g) -> *) *)
  (* (*   forall ν f, (ν,f) ∈ γ g -> (p@ν,f) ∈ γ g. *) *)
  (* (* Proof. *) *)
  (* (*   intros **. *) *)
  (* (*   apply central_permutation with (belongs_to_graph g). *) *)
  (* (*   + apply valuation_not_fixed. *) *)
  (* (*   + assumption. *) *)
  (* (*   + assumption. *) *)
  (* (* Qed. *) *)

  (* Lemma domain_belongs g : *)
  (*   forall α e, g!α = Some e -> *)
  (*   α ∈ belongs_to_graph g. *)
  (* Proof. *)
  (*   unfold belongs_to_graph, belongs_to_graph, ptree_map_reduce. *)
  (*   apply AtomTree_Properties.fold_rec. *)
  (*   { intros g₁ g₂ P h₁ h₂ α e h₃. *)
  (*     apply h₂ with e. *)
  (*     now rewrite h₁. } *)
  (*   { intros ** h. *)
  (*     CPTree.simplify; congruence. } *)
  (*   intros g₁ P α e h₁ h₂ h₃ β e' h₄. *)
  (*   CPTree.simplify. *)
  (*   - right. *)
  (*     destruct e; simpl. *)
  (*     + unfold belongs_to_block. *)
  (*       now left. *)
  (*     + unfold belongs_to_summary. *)
  (*       reflexivity. *)
  (*   - left ; eauto. *)
  (* Qed. *)

End Graph.

Arguments t summary : clear implicits.
Hint EResolve @γ_equivariant : equivariant.


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
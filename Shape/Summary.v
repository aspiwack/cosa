Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Shape.Graph.
Require Import Cosa.Lib.MapReduce.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Cosa.Interaction.Transition.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Interaction.Simulation.
Require Import Cosa.Interaction.InteractionLib.

(** Definition of inductive summaries for graphs. *)


Section Inductives.

  (** [indname] is a type which stands for the allowable inductive
      shapes in the graph.  The semantics of each name describes how
      it can be manipulated. The recursive knot is tied later in this
      file.

      Rules are parametrised by a set of nodes to avoid, which will be
      instanciated with the nodes of the graph where the unfolding
      takes place.  The graph part of the rules much not share a name
      with the ambiant graph, lest the star and the union fail to
      commute. *)

  Context {indname:Type} (γ_name:indname -> node -> ℘ Graph.conc).

  Definition rule := (Graph.t indname * expr Graph.node)%type.
  Definition avoids (P:℘ node) (B:℘ node) (r:rule) :=
    forall n:node, (exists a, (fst r)!n = Some a) -> B n \/ ~P n
  .

  Definition γ_rule (r:rule) : ℘ Graph.conc :=
    fun c =>
      let gr := Graph.γ γ_name (fst r) in
      c ∈ gr /\
      Lang.valid_pure_expr (fst c) (snd r) true
  .


  (** The idea is that un unfolding [u α] is a finite product (i.e. a
      list) of purely angelic processes where the commands are
      requests for fresh nodes (using
      [InteractionLib.with_new]). Later, when running the shape
      domain, we will need unfoldings to be exactly of that form, but
      it is not necessary for definitions. *)
  Definition unfolding := node -> Interaction (℘ node) rule.


  (** Given a concretisation of for [indname], computes a
      concretisation for an [unfolding] at node [α]. *)
  Definition γ_unfolding (u:unfolding) (α:node) : ℘ Graph.conc :=
    Join (fun P =>
            Join (fun ν:(u α).(Com) P =>
                    Join (Γ:=[conc]) (fun r:(u α).(Resp) ν => γ_rule ((u α).(Output) r)))
         )
  .

  Definition avoiding_unfolding (u:unfolding) : Prop :=
    forall α P (ν:(u α).(Com) P) (r:(u α).(Resp) ν),
      avoids P (fun β => β=α)((u α).(Output) r)
  .

End Inductives.

Arguments rule indname : clear implicits.
Arguments rule indname : clear implicits.
Arguments unfolding indname : clear implicits.



(** All these partial concretisation are increasing in [ind_name] *)

Instance γ_rule_increasing n :
  Proper (sub (Γ:=[n;node;conc]) ==> eq ==> sub (Γ:=[conc])) γ_rule.
Proof.
  unfold Proper, respectful.
  intros γ₁ γ₂ γ₁_sub_γ₂ r ? <-.
  unfold γ_rule.
  rewrite sub_cons.
  intros s [ h₁ h₂ ].
  split.
  - clear h₂; revert s h₁.
    rewrite <- sub_one.
    rewrite γ₁_sub_γ₂; reflexivity.
  - eauto.
Qed.

Instance γ_unfolding_increasing n :
  Proper (sub (Γ:=[n;node;conc]) ==> eq ==> eq ==> sub (Γ:=[conc])) γ_unfolding.
Proof.
  unfold Proper, respectful.
  intros γ₁ γ₂  γ₁_sub_γ₂ i ? <- α ? <-.
  unfold γ_unfolding.
  apply Join_increasing;rewrite sub_cons; intros P.
  apply Join_increasing;rewrite sub_cons; intros ν.
  apply Join_increasing;rewrite sub_cons; intros r.
  rewrite γ₁_sub_γ₂.
  reflexivity.
Qed.


Definition def := { indname:Type & indname -> unfolding indname }.
Definition names_of (d:def) : Type := projT1 d.
Coercion names_of : def >-> Sortclass.


(** The concretisation function for a set of inductive definition is
    the least fixed point of [F_γ]. *)
Definition F_γ (d:def) (γr : rel [names_of d;node;Graph.conc]) :
  rel [projT1 d;node;Graph.conc] :=
  fun i => γ_unfolding γr (projT2 d i)
.

Instance F_γ_increasing d : Proper (sub==>sub) (F_γ d).
Proof.
  unfold Proper, respectful.
  intros γ₁ γ₂ γ₁_sub_γ₂.
  unfold F_γ.
  rewrite sub_cons; intros α.
  rewrite sub_cons; intros i.
  rewrite γ₁_sub_γ₂.
  reflexivity.
Qed.

Definition γ (d:def) : d -> node -> ℘ Graph.conc :=
  lfp (F_γ d)
. 

(** An unfolding is correct when applying the unfolding yields an over
    approximation of the summary *)
Definition correct_unfolding {d:def} i (r:unfolding d) :=
  sub (Γ:=[node;Graph.conc])
      (γ d i)
      (γ_unfolding (γ d) r)
.

Lemma definition_correct (d:def) i : correct_unfolding i (projT2 d i).
Proof.
  unfold correct_unfolding, γ.
  revert i; rewrite <- sub_cons.
  apply lfp_ind.
  { typeclasses eauto. }
  intros γ' γ'_sub_γ h.
  rewrite sub_cons; intros i.
  unfold F_γ at 1.
  rewrite sub_cons; intros α.
  rewrite γ'_sub_γ.
  reflexivity.
Qed.

Definition apply_rule {d:def} (g:Graph.t d) (r:rule d) :
   Graph.t d * expr Graph.node :=
  ( ptree_union g (fst r) , snd r )
.

Definition domain_of_graph {d:def} : Interaction (Graph.t d) (Graph.t d * ℘ node) :=
  functional_extension (fun g => (g,belongs_to_graph g))
.

Definition apply_unfolding {d:def} (u:unfolding d)(α:node) :
   Interaction (Graph.t d) (rule d) :=
  seq domain_of_graph
 (seq (functional_extension (fun gp => (NodeTree.remove α (fst gp),(snd gp))))
 (seq (tensor skip (u α))
      (functional_extension (fun gr => apply_rule (fst gr) (snd gr)))))
.

(** An unfolding must exhibit certain symmetry property in order to be
    useable. Of course, all unfolding built off as a finite product of
    sequences of [with_new] will be sufficiently symmetric. *)
(* arnaud: en fait il faut restreindre, dans tout ce fichier, les [℘ node] à être
   fini, sinon on n'a pas de garanti de pouvoir choisir les noms comme on veut. *)
Definition symmetric_unfolding {d:def} (u:unfolding d) : Prop :=
  forall (α:node) (P:℘ node) (c:(u α).(Com) P) (r:(u α).(Resp) c) ν f,
  (ν,f) ∈ γ_rule (γ d) ((u α).(Output) r) ->
  forall P':℘ node, forall (c':(u α).(Com) P'), exists (r':(u α).(Resp) c') ν',
    ( forall β, β∈P' -> ν' β = ν β ) /\
    ( (ν',f) ∈ γ_rule (γ d) ((u α).(Output) r') )
.

(** All the definitions [i] in [d] must have the property that they
    only fix in [ν] those node that belong to them. *)
Definition valuation_not_fixed_def (d:def) :=
  forall (i:d) α, 
  forall ν f, (ν,f) ∈ γ d i α ->
  forall ν', (forall δ, δ ∈ belongs_to_summary α i -> ν' δ = ν δ) ->
  (ν',f) ∈ γ d i α.


(** Applying an unfolding is always correct. *)
Theorem apply_at_spec (d:def) u α : forall i:d,
  valuation_not_fixed_def d ->
  avoiding_unfolding u ->
  correct_unfolding i u ->
  symmetric_unfolding u ->
  Correspondance (seq (assume (fun g => g!α = Some (Summarized i)))
                      (apply_unfolding u α))
                 skip
                 (fun g f => exists ν, (ν,f) ∈ Graph.γ (γ d) g)
                 (fun r f => exists ν, (ν,f) ∈ γ_rule (γ d) r).
Proof.
  (** preliminary goal preparations. *)
  intros i vnf h₁ h₂ sym_u; unfold Correspondance.
  intros s f [ ν h ].
  (** introducing the assumption. *)
  apply assume_spec; intros h₃.
  generalize (star_summarized_edge _ _ _ _ h₃ _ h); intros [ s₁ [ s₂ [ h₄ [ h₅ h₆ ]]]].
  (** further simplifications. *)
  unfold apply_unfolding,domain_of_graph; simpl.
  apply correspondance_seq_fun_skip.
  apply correspondance_seq_fun_skip.
  apply correspondance_seq_skip.
  unfold RT at 1; simpl.
  intros [ [] c₁ ]. exists tt; intros []; simpl.
  (** One of the unfolding rules correspond to the concrete graph. *)
  unfold correct_unfolding,γ_unfolding,sub in h₂; simpl in h₂.
  specialize (h₂ _ _ h₅).
  destruct h₂ as [ P [ βs [ r h₂ ]]].
  destruct s₂ as [ ν₂ f₂ ].
  apply sym_u in h₂.
  specialize (h₂ (belongs_to_graph s)).
  specialize (h₂ c₁).
  destruct h₂ as [ r₁ [ ν₂' [ h₂₁ h₂₂ ]]].
  exists (tt,r₁).
  unfold RT; simpl.
  intros []; exists tt; intros []; exists tt.
  exists ν₂'.
  (** Proving the final condition. *)
  unfold apply_rule; simpl.
  destruct h₂₂ as [ h₂₂ h₂₃ ]; simpl in h₂₂,h₂₃.
  split; simpl.
  - rewrite γ_disjoint_union.
    + unfold estar, Relation.extension2.
      destruct s₁ as [ ν₁ f₁ ].
      exists (ν₂',f₁).
      exists (ν₂',f₂).
      decompose_concl.
      * destruct h₆ as [ h₆ _ ]; simpl in h₆; destruct h₆.
        { apply valuation_not_fixed with ν₁.
          - eauto.
          - eauto.
          - intros β h₆.
            apply h₂₁.
            unfold belongs_to_graph.
            rewrite (ptree_remove_map_reduce _ _ _ α (Summarized i));
               [|typeclasses eauto..|assumption].
            now right. }
      * assumption.
      * destruct h₆ as [ _ h₆ ]; simpl in h₆.
        now constructor.
    + (* spiwack: this could be made in a separate lemma. *)
      unfold avoiding_unfolding in h₁.
      specialize (h₁ α (belongs_to_graph s) c₁ r₁).
      unfold avoids in h₁.
      unfold ptree_disjoint.
      intros β e e' h₇ h₈.
      specialize (h₁ β).
      prove_hyp h₁.
      { eexists; eauto. }
      destruct h₁ as [ <- | h₁ ].
      * ptree_simplify; congruence.
      * assert (s!β = None) as h₉.
        { clear -h₁.
          assert (s!β = None \/ exists e, s!β = Some e) as h₂.
          { destruct (s!β).
            + right; eexists; eauto.
            + now left. }
          destruct h₂ as [ h₂ | [ e h₂ ]].
          { assumption. }
          now apply domain_belongs in h₂. }
        ptree_simplify; congruence.
  - assumption.
Qed.

(** A completeness property for unfoldings: each rule can be folded
    back into the summary. Compare with the correctness property:
    [correct_unfolding]. Both together means that an unfolding must be
    equivalent to the summarised edge. *)
Definition complete_unfolding {d:def} i (u:unfolding d) :=
  forall P α βs r,
    sub (Γ:=[conc])
      (γ_rule (γ d) ((u α).(Output) (a:=P) (c:=βs) r))
      (γ d i α)
.

Lemma definition_complete (d:def) i : complete_unfolding i (projT2 d i).
Proof.
  unfold complete_unfolding.
  intros P α βs r.
  (* Unwinding a layer of F_γ *)
  unfold γ.
  pattern (lfp (F_γ d)) at 2.
  rewrite <- lfp_fixed_point; [|typeclasses eauto].
  change (lfp (F_γ d)) with (γ d).
  unfold F_γ.
  (* /unwinding *)
  unfold γ_unfolding.
  apply (Join_intro P), (Join_intro βs). refine (Join_intro r _). (* arnaud:bug de apply?*)
  reflexivity.
Qed.
  

Record env := {
  defs :> def ;
  defs_local : valuation_not_fixed_def defs ;

  unfoldings : defs -> { U:Type & U -> unfolding defs } ;
  unfoldings_correct : forall i u, correct_unfolding i (projT2 (unfoldings i) u) ;
  unfoldings_complete : forall i u, complete_unfolding i (projT2 (unfoldings i) u) ;
  unfoldings_avoiding : forall i u, avoiding_unfolding (projT2 (unfoldings i) u) ;
  unfoldings_symmetric : forall i u, symmetric_unfolding (projT2 (unfoldings i) u)
}.
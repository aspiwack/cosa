Require Import Cosa.Lib.Header.
Require compcert.common.Memdata.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Interaction.InteractionLib.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Abstract.Valuation.
Require Import Cosa.Shape.Graph.
Require Import Cosa.Shape.Summary.
Import List.ListNotations.
Import Coq.Classes.EquivDec.

(** In this file we define the concrete instances of inductive shapes
    we are interested in. *)

Section Schemata.

  Context {name:Type} (γ_name:name -> node -> ℘ Graph.conc).
  Hypothesis valuation_not_fixed_summary : forall α sm f,
    central (belongs_to_summary α sm)
            (fun ν => (ν,f) ∈ γ_name sm α).

  (** In this section we define generic combinators to build inductive
      summaries. *)

  (** [fnf n] is the type of functions taking [n] argument nodes and
      returning a rule. *)
  Fixpoint fnf (n:nat) : Type :=
    match n with
    | 0 => rule name
    | S n => Graph.node -> fnf n
    end
  .

  (** [rule_with_new n] is the type of interaction structures
      requiring [n] new nodes and producing a rule. *)
  Fixpoint rule_with_new {n:nat} : fnf n -> Interaction (℘ node) (rule name) :=
    match n with
    | 0 => fun r => just r
    | S n => fun r => bind with_new (fun α => rule_with_new (r α))
    end
  .

  (** A correction property for [rule_with_new n]: the nodes allowed
      in the generated rule must only contain nodes in a given set and
      the [n] new nodes. *)
  Fixpoint rule_correct {n:nat} : fnf n -> ℘ node -> Prop :=
    match n with
    | 0 => fun r P => sub (Γ:=[node]) (belongs_to_graph (fst r)) P /\
                      sub (Γ:=[node]) (belongs_to_expr (snd r)) P
    | S n => fun r P => forall α, rule_correct (r α) (P ∪ singleton α)
    end
  .

  (* arnaud: déplacer dans extra? *)
  Lemma exists_sigTr (A:Type) (F:A->Type) (P:forall x:A, F x -> Prop) :
    (exists u:{x:A & F x}, (P (projT1 u) (projT2 u))) <->
    (exists (x:A) (y:F x), P x y).
  Proof.
    split.
    - intros [ [ x y ] h ]; simpl in *.
      decompose_concl; eauto.
    - intros [ x [ y h ]].
      eexists (existT _ x y); simpl.
      easy.
  Qed.

  (* arnaud: déplacer dans extra? *)
  Lemma exists_sigT (A:Type) (F:A->Type) (P:{ x:A & F x} -> Prop) :
    (exists u, P u) <->
    (exists (x:A) (y:F x), P (existT _ x y)).
  Proof.
    split.
    - intros [ [ x y ] h ]; simpl in *.
      decompose_concl; eauto.
    - intros [ x [ y h ]].
      eexists (existT _ x y); simpl.
      easy.
  Qed.

  (* arnaud: déplacer dans extra? *)
  Lemma exists_sig (A:Type) (F:A->Prop) (P:{ x:A | F x} -> Prop) :
    (exists u, P u) <->
    (exists (x:A) (y:F x), P (exist _ x y)).
  Proof.
    split.
    - intros [ [ x y ] h ]; simpl in *.
      decompose_concl; eauto.
    - intros [ x [ y h ]].
      eexists (existT _ x y); simpl.
      easy.
  Qed.

  Lemma γ_unfolding_with_new (u:node->unfolding name) (P:℘ node) α :
    γ_unfolding_with γ_name P (fun α => (bind with_new (fun β => u β α))) α =
    Join (fun β => meet (Γ:=[_]) (fun _ => β ∉ P)
                                 (γ_unfolding_with γ_name (fun δ=>δ∈P\/δ=β) (u β) α)).
  Proof.
    double_sub; intros s.
    - unfold γ_unfolding_with; simpl.
      intros [ [ [ β hβ ] h₂ ] [ [ [] r] h₃ ]]; simpl in *.
      decompose_concl; eauto.
    - unfold γ_unfolding_with; simpl.
      intros [ β [ h₁ [ c [ r h₂ ]]]].
      rewrite ?exists_sigT,?exists_sig; simpl.
      eexists; split.
      { eauto. }
      exists (fun _ => c).
      rewrite ?exists_sigT,?exists_sig; simpl.
      decompose_concl; eauto.
      easy.
  Qed.

  (** The properties of [Summary.env] are verified by unfoldings of
      the form [rule_with_new n r] *)

  Obligation Tactic := idtac.
  Definition swap_set (α β :node) (P:℘ node) : ℘ node :=
    fun δ =>
      if      δ == α then P β
      else if δ == β then P α
           else           P δ
  .

  Program Fixpoint swap_com_rec {n:nat} : forall {r:fnf n} {P:℘ node} (α β:node), (rule_with_new r).(Com) P -> (rule_with_new r).(Com) (swap_set α β P) :=
    match n with
    | 0 => fun _ _ _ _ _ => tt
    | S n => fun r P α β c =>
               if proj1_sig (projT1 c) == α then
                 existT _ (exist _ β _) _
               else
                 _
    end.
  Next Obligation.
    intros * <-; simpl in *.
    intros r P α β [ [ δ hδ] c] <- ; simpl in *.
    unfold swap_set.
    rewrite if_eq_refl.
    destruct (β==δ) as [ <- | _ ]; assumption.
  Qed.
  Next Obligation.
    intros ? n <- r P α β [ [δ hδ] c ] <- ; simpl in *; intros _.
    

  Program Fixpoint swap_com {n:nat} : forall {r:fnf n} {P:℘ node} (α β:node), (rule_with_new r).(Com) P -> α ∉ P -> β ∉ P -> (rule_with_new r).(Com) P:=
    match n with
    | 0 => fun _ _ _ _ _ _ _ => tt
    | S n => fun r P α β c hα hβ =>
               if proj1_sig (projT1 c) == α then
                 existT _ (exist _ β hβ) _
               else
                 _
    end.
  Next Obligation.
    intros * <-; simpl in *.
    intros r P α β [ [ δ hδ ] c ] hα hβ e; simpl in *.
    Print sig.
    

  Lemma vnf_rule_with_new (n:nat) (r:fnf (S n)) (P:℘ node) (α:node) :
    α ∈ P ->
    (rule_correct (r α) P) ->
    forall f,
      central P
              (fun ν => (ν,f) ∈ γ_unfolding_with γ_name P (fun α => rule_with_new (r α)) α).
  Proof.
    revert r P α.
    induction n as [ | n hn ]; intros r P α.
    - admit.
    - intros h₁ h₂ f; simpl in h₂.
      intros β δ hβ hδ ν h₃; unfold γ_unfolding_with in h₃ |- *; simpl in h₃ |- *.
      destruct h₃ as [ [ [ γ hγ] c] h₃ ]; simpl in c,h₃.
      destruct h₃ as [ [ [] r'] h₃ ]; simpl in h₃.
      rewrite ?exists_sigT,?exists_sig; simpl.
      destruct (β==γ) as [ <- | nβγ ].
      + destruct (β==δ) as [ -> | nβδ ].
        * assert (swap δ δ ν = ν) as e; [|rewrite e;clear e].
          { extensionality x.
            apply swap_self_id. }
          exists δ; exists hδ; exists c.
          rewrite ?exists_sigT,?exists_sig; simpl.
          decompose_concl; eauto.
        * 
  Admitted.


End Schemata.

(** spiwack: There are few inductive at the time, until we are able to generate them. *)

Inductive name :=
| List
| ListSegment (β:Graph.node)
.

Local Notation "α ≡ β" := (Lang.Abinop (Cminor.Ocmpu Integers.Ceq) α β) (at level 70).
Local Notation "α ≠ β" := (Lang.Aunop Cminor.Onegint (α≡β)) (at level 70).
Local Notation "0" := (Lang.Aconst (Cminor.Ointconst Int.zero)).
Local Notation "1" := (Lang.Aconst (Cminor.Ointconst Int.one)).

Definition add_chunk (offs:int) (chunk:AST.memory_chunk) : int :=
  Int.add offs (Int.repr (Memdata.size_chunk chunk))
.

Definition def (i:name) (α:node) : Interaction (℘ node) (Summary.rule name) :=
  match i with
  | List =>
    Interaction.pi (Finite.access [
        just (Graph.NodeTree.empty _, (Avar α) ≡ 0) (** empty list *);
        bind with_new (fun β => (** head *)
        bind with_new (fun δ => (** tail *)
            just (NodeTree.set α (Point_to
                    [(Int.zero,{|destination:=(β,Int.zero);size:=AST.Mint32|});
                     (add_chunk (Int.zero) AST.Mint32,{|destination:=(δ,Int.zero);size:=AST.Mint32|})]
                   )
                  (NodeTree.set δ (Summarized List)
                  (NodeTree.empty _)) ,
                  (Avar α) ≠ 0)))
      ])
  | ListSegment β =>
    Interaction.pi (Finite.access [
        just (Graph.NodeTree.empty _, (Avar α) ≡ (Avar β)) (** empty segment *);
        bind with_new (fun γ => (** head *)
        bind with_new (fun δ => (** tail *)
            just (NodeTree.set α (Point_to
                    [(Int.zero,{|destination:=(γ,Int.zero);size:=AST.Mint32|});
                     (add_chunk (Int.zero) AST.Mint32,{|destination:=(δ,Int.zero);size:=AST.Mint32|})]
                   )
                  (NodeTree.set δ (Summarized (ListSegment β))
                  (NodeTree.empty _)) ,
                  (Avar α) ≠ 0)))
      ])
  end
.

(** Segments can be unfolded from the back node. *)
Definition list_segment_backward_unfolding (β α:node) :
   Interaction (℘ node) (Summary.rule name) :=
  Interaction.pi (Finite.access [
      just ( (** backward unfolding can yield identity. *)
        NodeTree.set α (Summarized (ListSegment β))
       (NodeTree.empty _),1 );

      bind with_new (fun γ => (** value *)
      bind with_new (fun δ => (** new end point *)
        just (NodeTree.set α (Summarized (ListSegment δ))
             (NodeTree.set δ (Point_to
                  [(Int.zero,{|destination:=(γ,Int.zero);size:=AST.Mint32|});
                     (add_chunk (Int.zero) AST.Mint32,{|destination:=(β,Int.zero);size:=AST.Mint32|})]
                   )
             (NodeTree.empty _)) ,
             (Avar δ) ≠ 0)))
      ])
.

Definition d : Summary.def :=
  existT _ name def
.

Inductive fb := Forward | Backward.

Definition list_unfoldings (i:name) : { U:Type & U -> unfolding name }:=
  match i with
  | List => existT _ (unit:Type) (fun _ => def List)
  | ListSegment β => existT (fun U => U -> unfolding name) (fb:Type)
                                 (fun d => match d with
                                           | Forward => def (ListSegment β)
                                           | Backward => list_segment_backward_unfolding β
                                           end)
  end
.

(* arnaud: WIP *)
Program Definition env : Summary.env := {|
  defs := d ;
  unfoldings := list_unfoldings
|}.
Next Obligation. (** [defs_local] *)
  unfold valuation_not_fixed_def, Valuation.central.
  (** Reformulate the goal into a form where [lfp_ind] can be applied *)
  cut (sub (Γ:=[names_of d;node;conc])
             (γ d)
             (fun i α s =>
                forall β δ,
                  ~ belongs_to_summary α i β ->
                  ~ belongs_to_summary α i δ ->
                  γ d i α (Valuation.swap β δ (fst s), (snd s)))).
  { simpl; intros h; intros i α f β δ h₁ h₂ ν.
    specialize (h i α (ν,f)); eauto. }
  (** by induction *)
  apply lfp_ind.
  { typeclasses eauto. }
  simpl; intros R h₁ h₂ i α [ν f] h₃ β δ hβ hδ; simpl.
  change (lfp (F_γ d)) with (γ d) in h₁.
  destruct i as [|γ].
  - (** [List] *)
    unfold F_γ,γ_unfolding in h₃.
    rewrite <- γ_fixed_point.
    unfold F_γ,γ_unfolding.
    destruct h₃ as [ P [ εs [ r h₃]]]. exists P.
    destruct h₃ as [ h₃₁ h₃₂ ].
    destruct r as [ [ [[]|] | ] r_plus ].
    * (** ν is of the form cons *)
      simpl in * |-.
      destruct r_plus as [ [] [ [] [] ]].
      destruct (εs (Some None)) as [ [ε hε] ζ₀ ]; simpl in * |-; clear εs.
      destruct (ζ₀ tt) as [ [ζ hζ] id_unit ]; simpl in * |-; clear ζ₀.
      
    * (** ν is of the form nil *)
  - (** [ListSegment β] *)
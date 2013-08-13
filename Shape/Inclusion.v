Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Shape.Graph.
Require Import Cosa.Shape.Summary.
Import Cosa.Interaction.Interaction.

(** Rules for inclusion checking *)

(** There are basically two ways to present the rules for inclusion
    checking. Either we suppose that the renaming ([Graph.phi] below]
    is given as input to the algorithm, or the algorithm discovers
    it. The former is better for certificate checking and the latter
    for a direct inclusion checking algorithm. We shall favour the
    certificate checking approach. It is marginally easier to prove
    correct, as the correctness of certificate checking follows from a
    local correctness property of each rule. Mostly, however, it gives
    more freedom to design a powerful oracle. *)
Local Notation expr := (Lang.expr Graph.node).

Module Graph.
Section Graph.

Context {ind_env : Summary.env}.

Local Notation t := (Graph.t ind_env).
Local Notation γ := (Graph.γ (Summary.γ ind_env)).

Record state := {
  g_left : t ;
  g_right  : t ;
  phi : NodeTree.t Graph.node (** Renaming of nodes from [g_right] to nodes from [g_left] *)
}.

Definition partial_comp {A B} (f:A->option A) (g:A -> B) (x:A) : B :=
  match f x with
  | Some x' => g x'
  | None => g x
  end
.

Definition valid_expr
           (ν:valuation) (r:Graph.node->option Graph.node) (constraint:list expr) : Prop :=
  List.fold_right and True (
     List.map (fun c => valid_pure_expr (partial_comp r ν) c true) constraint
  )
.

Lemma valid_expr_cons ν r c constraint :
      valid_expr ν r (c::constraint) =
      (valid_pure_expr (partial_comp r ν) c true /\
       valid_expr ν r constraint).
Proof. reflexivity. Qed.

Definition Correct (c:list expr) (s:state) : Prop :=
  let renaming α := s.(phi)!α in
  forall ν f, (ν,f) ∈ γ s.(g_left) ->
              valid_expr ν renaming c ->
              (partial_comp renaming ν , f ) ∈ γ (s.(g_right))
.

Lemma empty_correct : forall φ c,
  Correct c {| g_left:=NodeTree.empty _ ; g_right:=NodeTree.empty _ ; phi:=φ |}.
Proof.
  intros * ν f h₁. simpl in *.
  destruct f as [ m d ]; compute in h₁.
  easy.
Qed.

Lemma unfold_correct : forall φ c g_l g_r α i,
  Graph.equiv g_r (NodeTree.set α (Summarized i) (NodeTree.empty _)) ->
  forall u βs r,
    let gf :=
        (projT2 (ind_env.(unfoldings) i) u α).(Output) (a:=belongs_to_graph g_r) (c:=βs) r
    in
    Correct c {| g_left := g_l ; g_right:= fst gf; phi:=φ |} ->
    Correct ((snd gf)::c) {| g_left:=g_l; g_right:=g_r; phi:=φ|}.
Proof.
  intros * h₁ * h₂; unfold Correct in *; simpl in *.
  intros ν f h₃ h₄.
  rewrite valid_expr_cons in h₄. destruct h₄ as [ h₄ h₅ ].
  apply h₂ in h₃;[|solve[eauto]].
  rewrite (Graph.γ_equiv _ _ _ h₁).
  rewrite single_out_one_edge_set;[|ptree_simplify;congruence].
  rewrite γ_empty, star_empty_neutral; simpl.
  eapply unfoldings_complete.
    instantiate (1:=r).
  unfold γ_rule.
  now split.
Qed.


End Graph.
End Graph.
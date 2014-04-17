Require Import Cosa.Lib.Header.
Require Import Cosa.Lib.Relation.
Require Import Cosa.Interaction.Interaction.

(** This file deals with simulations, the interaction structure
    equivalent of forward refinement in the predicate transformers
    setting. Forward refinement, as noticed by Arnaud Spiwack,
    corresponds to the kind of abstract interpretation we are
    interested in. The relations here are manipulated in expanded form
    [A->B->Prop], rather than [rel [A;B]], it seems easier for our
    usecase. *)

(** A pair of interaction structures can act jointly on a
    relation. Roughly the two act dually, but the connectives are
    interleaved. [RT] stands for "relation transformer". Choosing [RT]
    to act on [Prop] (with [ex]) rather than on [Type] (with [sigT])
    forces the [has_choice] condition on the commutation rule with
    [seq]. However, empirically, it seems a better choice in the
    context of abstract interpretation.  *)
Definition RT {S₁ T₁ S₂ T₂}
   (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) (Q:T₁ -> T₂ -> Prop) : S₁ -> S₂ -> Prop :=
  fun s t =>
    forall c₁:i.(Com)  s , exists c₂:j.(Com)  t,
    forall x₂:j.(Resp) c₂, exists x₁:i.(Resp) c₁,
    Q (i.(Output) x₁) (j.(Output) x₂)
.

(** We say that the pair [(R,Q)] is a correspondance from [i] to [j]
    when [R] is included in [RT i j Q]. This parallels the definition
    of a pair of precondition and postcondition as [P⊆wp Q]. In plain
    English: if [s] and [t] are related by [R] then, outcomes of [i]
    and [j] are related by [Q]. The choice of quantifiers in [RT]
    allows to read [j] as a more concrete version of [i]. *)
Definition Correspondance {S₁ T₁ S₂ T₂}
   (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) (R:S₁ -> S₂ -> Prop) (Q:T₁ -> T₂ -> Prop) : Prop :=
  forall s t, R s t -> RT i j Q s t
.

Definition Simulation {S T} (i:Interface S) (j:Interface T) (R:S->T->Prop) : Prop :=
  Correspondance i j R R
.


Lemma correspondance_transitive {S₁ T₁ S₂ T₂ S₃ T₃}
      (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) (k:Interaction S₃ T₃) R₁ Q₁ R₂ Q₂ :
  Correspondance i j R₁ Q₁ -> Correspondance j k R₂ Q₂ -> Correspondance i k (R₁•R₂) (Q₁•Q₂).
Proof.
  unfold Simulation, Relation.comp.
  intros h₁ h₂.
  intros s u [ t [ h₃ h₄ ] ].
  specialize (h₁ s t h₃).
  specialize (h₂ t u h₄).
  intros c₁.
  specialize (h₁ c₁).
  destruct h₁ as [ c₁' h₁ ].
  specialize (h₂ c₁').
  destruct h₂ as [ c₂ h₂ ].
  exists c₂.
  intros x₂.
  specialize (h₂ x₂).
  destruct h₂ as [ x₂' h₂ ].
  specialize (h₁ x₂').
  destruct h₁ as [ x₁ h₁ ].
  exists x₁.
  unfold Relation.comp.
  eexists; intuition eauto.
Qed.

Lemma simulation_transitive {S T U} (i:Interface S) (j:Interface T) (k:Interface U) Q R :
                  Simulation i j R -> Simulation j k Q -> Simulation i k (R•Q).
Proof. apply correspondance_transitive. Qed.

Instance correspondance_proper_impl S₁ T₁ S₂ T₂ (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) :
         Proper (Relation.equiv ==> Relation.equiv ==> Basics.impl) (Correspondance i j).
Proof.
  unfold Proper, respectful, Simulation.
  intros R₁ R₂ equiv_R₁_R₂.
  intros Q₁ Q₂ equiv_Q₁_Q₂.
  intros h s t R₂_s_t.
  apply equiv_R₁_R₂ in R₂_s_t.
  specialize (h s t R₂_s_t).
  intros c₁.
  specialize (h c₁).
  destruct h as [ c₂ h ].
  exists c₂.
  intros x₂.
  specialize (h x₂).
  destruct h as [ x₁ h ].
  exists x₁.
  now apply equiv_Q₁_Q₂.
Qed.

Instance correspondance_proper S₁ T₁ S₂ T₂ (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) :
         Proper (Relation.equiv ==> Relation.equiv ==>iff) (Correspondance i j).
  unfold Proper, respectful.
  intros R₁ R₂ equiv_R₁_R₂ Q₁ Q₂ equiv_Q₁_Q₂.
  split.
  - rewrite equiv_R₁_R₂, equiv_Q₁_Q₂; trivial.
  - rewrite <- equiv_R₁_R₂, <- equiv_Q₁_Q₂; trivial.
Qed.


Instance simulation_proper S T (i:Interface S) (j:Interface T) :
                  Proper (Relation.equiv ==> Logic.iff) (Simulation i j).
Proof.
  unfold Proper, respectful, Simulation.
  intros R Q equiv_R_Q.
  now rewrite equiv_R_Q.
Qed.

Lemma RT_increasing S₁ S₂ T₁ T₂ (i:Interaction S₁ S₂) (j:Interaction T₁ T₂) :
  forall (R R':S₂->T₂->Prop), (forall s t, R s t -> R' s t) ->
  forall s t, RT i j R s t -> RT i j R' s t.
Proof.
  intros * h * h₁; unfold RT in *.
  intros c₁; specialize (h₁ c₁).
  destruct h₁ as [ c₂ h₁ ]; exists c₂.
  intros x₂; specialize (h₁ x₂).
  destruct h₁ as [ x₁ h₁ ]; exists x₁.
  eauto.
Qed.

(** relation transformers of composed interaction structures. *)

Lemma correspondance_seq_seq S₁ S₂ S₃ T₁ T₂ T₃
  (i₁:Interaction S₁ S₂) (i₂:Interaction S₂ S₃) (j₁:Interaction T₁ T₂) (j₂:Interaction T₂ T₃) :
  (forall s (c:j₁.(Com) s), has_choice (j₁.(Resp) c)) ->
  forall R s t, RT i₁ j₁ (RT i₂ j₂ R) s t -> RT (seq i₁ i₂) (seq j₁ j₂) R s t.
Proof.
  intros choice * h; unfold RT in *; unfold seq; simpl.
  generalize (fun s c => choice_exists _ (choice s c)); clear choice; intros choice.
  intros [c₁ c₁'].
  specialize (h c₁).
  destruct h as [c₂ h].
  apply choice in h.
  destruct h as [c₂' h ].
  generalize (fun x₂ => h x₂ (c₁' (c₂' x₂))); clear h; intros h.
  apply choice in h.
  destruct h as [ c₂'' h ].
  exists (existT _ c₂ c₂''); simpl.
  intros [ x₂ x₂' ]; simpl.
  specialize (h x₂ x₂').
  destruct h as [ x₁' h ].
  exists (existT _ (c₂' x₂) x₁'); simpl.
  assumption.
Qed.

Lemma correspondance_add_skip S₁ S₂ T₁ T₂ (i:Interaction S₁ S₂) (j:Interaction T₁ T₂) : 
  forall R s t, RT i (seq skip j) R s t -> RT i j R s t.
Proof.
  intros * h; unfold seq,RT in *; simpl in *.
  intros c₁; specialize (h c₁).
  destruct h as [ [ [] c₂ ] h ].
  exists (c₂ tt).
  intros x₂.
  specialize (h (existT _ tt x₂)); simpl in h.
  exact h.
Qed.

Corollary correspondance_seq_skip S₁ S₂ S₃ T₁ T₂
  (i₁:Interaction S₁ S₂) (i₂:Interaction S₂ S₃) (j:Interaction T₁ T₂) :
  forall R s t, RT i₁ skip (RT i₂ j R) s t -> RT (seq i₁ i₂) j R s t.
Proof.
  intros * h.
  apply correspondance_add_skip.
  apply correspondance_seq_seq.
  { simpl; intros **.
    apply unit_has_choice. }
  assumption.
Qed.

Lemma correspondance_curry A S₁ S₂ T₁ T₂ (i:A->Interaction S₁ S₂) (j:Interaction T₁ T₂) :
  forall R s t, RT (i (fst s)) j R (snd s) t -> RT (curry i) j R s t.
Proof.
  intros * h; unfold RT,curry in *; simpl in *.
  exact h.
Qed.

Lemma correspondance_bind_seq A S₁ S₂ S₃ T₁ T₂ T₃
  (i₁:Interaction S₁ (A*S₂)) (i₂:A-> Interaction S₂ S₃) (j₁:Interaction T₁ T₂) (j₂:Interaction T₂ T₃) :
  (forall s (c:j₁.(Com) s), has_choice (j₁.(Resp) c)) ->
  forall R s t, RT i₁ j₁ (fun s' t' => RT (i₂ (fst s')) j₂ R (snd s') t') s t ->
                RT (bind i₁ i₂) (seq j₁ j₂) R s t.
Proof.
  intros choice * h; unfold bind.
  apply correspondance_seq_seq.
  { apply choice. }
  eapply RT_increasing.
  + eapply correspondance_curry.
  + assumption.
Qed.

Corollary correspondance_bind_skip A S₁ S₂ S₃ T₁ T₂
  (i₁:Interaction S₁ (A*S₂)) (i₂:A-> Interaction S₂ S₃) (j:Interaction T₁ T₂) :
  forall R s t, RT i₁ skip (fun s' t' => RT (i₂ (fst s')) j R (snd s') t') s t ->
                RT (bind i₁ i₂) j R s t.
Proof.
  intros **.
  apply correspondance_add_skip.
  apply correspondance_bind_seq.
  { simpl; intros **.
    apply unit_has_choice. }
  assumption.
Qed.

Lemma correspondance_seq_fun_skip S₁ S₂ S₃ T₁ T₂
  (f:S₁ -> S₂) (i:Interaction S₂ S₃) (j:Interaction T₁ T₂) :
  forall R s t, RT i j R (f s) t -> RT (seq (functional_extension f) i) j R s t.
Proof.
  intros * h.
  apply correspondance_seq_skip.
  unfold RT at 1; simpl.
  repeat (decompose_goal;eauto).
Qed.

Lemma correspondance_bind_fun_skip A S₁ S₂ S₃ T₁ T₂
  (f:S₁ -> (A*S₂)) (i:A->Interaction S₂ S₃) (j:Interaction T₁ T₂) :
  forall R s t, RT (i (fst (f s))) j R (snd (f s)) t ->
                RT (bind (functional_extension f) i) j R s t.
Proof.
  intros * h.
  apply correspondance_bind_skip.
  unfold RT at 1; simpl.
  repeat (decompose_goal;eauto).
Qed.


(** Interaction structures and strategies. *)

Definition select {S T} (i:Interaction S T) (strat:forall s, i.(Com) s) : Interaction S T := {|
  Com s := unit ;
  Resp s c := i.(Resp) (strat s) ;
  Output s c x := i.(Output) x
|}.

Lemma select_simulation S (i:Interface S) strat : Simulation (select i strat) i eq.
Proof.
  unfold Simulation, Correspondance.
  intros s ? <-.
  intros [].
  exists (strat s); simpl.
  intros x₂.
  exists x₂.
  reflexivity.
Qed.

(** [serve] is given for demonstration, it shouldn't have a use in Cosa. *)
Definition serve {S T} (i:Interaction S T) (server:forall s (c:i.(Com) s), i.(Resp) c) : Interaction S T := {|
  Com s := i.(Com) s;
  Resp s c := unit;
  Output s c x := i.(Output) (server s c)
|}.

Lemma serve_simulation S (i:Interface S) server : Simulation i (serve i server) eq.
Proof.
  unfold Simulation,Correspondance,RT; simpl.
  intros s ? <-.
  intros c.
  exists c.
  intros _.
  exists (server s c).
  reflexivity.
Qed.
(** Extra generic tactics. *)

Require Import Maps.

Ltac simplify_transitivity1 :=
  etransitivity; eauto; [idtac]
.

Ltac simplify_transitivity :=
  repeat simplify_transitivity1
.
Ltac solve_transitivity :=
  solve [etransitivity;eauto]
.


Ltac decompose_conj :=
  lazymatch goal with
  | |- _ /\ _ => split; decompose_conj
  | |- _ <-> _ => split; decompose_conj
  | _ => idtac
  end
.
Ltac decompose_ex :=
  lazymatch goal with
  | |- ex _ => eexists; decompose_ex
  | _ => idtac
  end
.

Ltac decompose_concl :=
  repeat progress (decompose_ex;decompose_conj)
.


Ltac decompose_hyp h :=
  match type of h with
  | ex _ => 
    let x := fresh "x" in
    let h' := fresh "h" in
    destruct h as [x h'];
    decompose_hyp h'
  | _ <-> _ =>
    let h₁ := fresh "h" in
    let h₂ := fresh "h" in
    destruct h as [h₁ h₂];
    decompose_hyp h₁;decompose_hyp h₂
  | _ /\ _ =>
    let h₁ := fresh "h" in
    let h₂ := fresh "h" in
    destruct h as [h₁ h₂];
    decompose_hyp h₁;decompose_hyp h₂
  | ?y = _ => is_var y; try rewrite h in *; clear h y
  | _ = ?y => is_var y; try rewrite <- h in *; clear h y
  | _ => idtac
  end
.

Ltac decompose_hyps :=
  repeat
    match goal with
    | h:ex _ |- _ => decompose_hyp h
    | h:_ <-> _ |- _ => decompose_hyp h
    | h:_ /\ _ |- _ => decompose_hyp h
    | h:_ = ?y |- _ => is_var y; decompose_hyp h
    | h:?y = _ |- _ => is_var y; decompose_hyp h
    end
.

Ltac decompose_goal :=
  intros **;decompose_hyps;decompose_concl
.

Ltac rewrite_defs :=
  repeat match goal with
  | H:?y =  _ |- _ => is_var y; try rewrite H in *; clear H y
  | H: _ = ?y |- _ => is_var y; try rewrite <- H in *; clear H y
  end
.

(** applies t if the conclusion doesn't have existential vars *)
Ltac ifnevar t :=
  first [(
      match goal with
      | |- ?c => ((has_evar c; fail 1) || fail 2)
      end
    || idtac)
  | t]
.


Ltac prove_hyp h :=
  lazymatch type of h with
  | ?A->?B =>
    let h' := fresh "h" in
    assert A as h' ; [ | specialize (h h');clear h' ]
  | _ => fail"Hypothesis must be an implication."
  end
.


(** Tactics to simplify PTree expressions. *)

Lemma neq_symmetric A : forall (n m:A), m<>n -> n<>m.
Proof. congruence. Qed.

Ltac ptree_simplify_hyp h :=
  repeat match type of h with
  | appcontext[PTree.get ?n (PTree.set ?m _ _)] => constr_eq n m;rewrite PTree.gss in h
  | appcontext[PTree.get ?n (PTree.set ?m _ _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite PTree.gso in h; [| exact ne]
    | ne : m<>n |- _ => rewrite PTree.gso in h; [| exact (neq_symmetric _ n m ne)]
    | |- _ => generalize (PTree.elt_eq n m); intros [ <- | ? ]
    end
  | appcontext[PTree.get ?n (PTree.remove ?m _)] =>
         constr_eq n m;rewrite PTree.grs in h
  | appcontext[PTree.get ?n (PTree.remove ?m _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite PTree.gro in h; [| exact ne]
    | ne : m<>n |- _ => rewrite PTree.gro in h; [| exact (neq_symmetric _ n m ne)]
    | |- _ => generalize (PTree.elt_eq n m); intros [ <- | ? ]
    end
  | appcontext[PTree.get _ (PTree.empty _)] => rewrite PTree.gempty in h
  end
.

Ltac ptree_simplify_concl :=
  repeat match goal with
  | |- appcontext[PTree.get ?n (PTree.set ?m _ _)] => constr_eq n m;rewrite PTree.gss
  | |- appcontext[PTree.get ?n (PTree.set ?m _ _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite PTree.gso; [| exact ne]
    | ne : m<>n |- _ => rewrite PTree.gso; [| exact (neq_symmetric _ n m ne)]
    | |- _ => generalize (PTree.elt_eq n m); intros [ <- | ? ]
    end
  | |- appcontext[PTree.get ?n (PTree.remove ?m _)] =>
         constr_eq n m;rewrite PTree.grs
  | |- appcontext[PTree.get ?n (PTree.remove ?m _)] =>
    lazymatch goal with
    | ne : n<>m |- _ => rewrite PTree.gro; [| exact ne]
    | ne : m<>n |- _ => rewrite PTree.gro; [| exact (neq_symmetric _ n m ne)]
    | |- _ => generalize (PTree.elt_eq n m); intros [ <- | ? ]
    end
  | |- appcontext[PTree.get _ (PTree.empty _)] => rewrite PTree.gempty
  end
.

Ltac ptree_simplify_hyps :=
  repeat match goal with
  | h : _ |- _ => progress ptree_simplify_hyp h
  end
.

Ltac ptree_simplify := ptree_simplify_hyps; ptree_simplify_concl.

(** A place holder for a by-file termination tactic. *)
Ltac crush := fail.

Tactic Notation "by" tactic(t) := (t;crush).
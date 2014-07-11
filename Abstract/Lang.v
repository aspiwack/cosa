Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.Valuation.
Require Import Cosa.Nominal.Set.
Require Import Cosa.Nominal.CompcertInstances.
Require Import Coq.Classes.EquivDec.
Require Cminor.

(** An abstract notion of expression. The type [expr] is a variant of
    [Cminor.expr] where the variables are taken to be at an arbitrary
    type rather than a type of identifier. They will be instantiated
    with [Graph.node]. Most of the evaluation relation is reused from
    [Cminor].*)

Section Expr.

  Context {var:Type} {nominal_var:Action var}.

  Inductive expr :=
  | Avar : var -> expr
  | Aconst : Cminor.constant -> expr
  | Aunop : Cminor.unary_operation -> expr -> expr
  | Abinop : Cminor.binary_operation -> expr -> expr -> expr
  | Aload : AST.memory_chunk -> expr -> expr
  .


  Global Program Instance action_expr : Action expr := {|
    act π := (fix act e :=
      match e return _ with
      | Avar v => Avar (π·v)
      | Aconst c => Aconst c
      | Aunop op e => Aunop op (act e)
      | Abinop op e₁ e₂ => Abinop op (act e₁) (act e₂)
      | Aload c e => Aload c (act e)
      end)
  |}.
  Next Obligation.
    autounfold.
    intros π₁ π₂ hπ e e' <-.
    induction e; (congruence||now rewrite hπ).
  Qed.
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    intros e.
    induction e; (congruence||now rewrite act_id).
  Qed.
  Next Obligation.
    (* [x] should not have been introduced *)
    revert x.
    (* / *)
    intros e.
    induction e; (congruence||now rewrite act_comp).
  Qed.

  (** Evaluation is parametrised by an environment for the
      variables. And a read relation for loads.

      [reads chunk vaddr v] holds if reading chunk [chunk] at the
      memory address corresponding to value [vaddr] yields [v]. *)
  (* spiwack: I use a function [var->Values.val] as my environment
     because it's what is useful for abstract interpretation. However,
     we could use a relation [var->Values.val->Prop] and hence be
     more compatible with [Cminor]'s expressions. *)
  Variable (env:var -> Values.val)
           (reads:AST.memory_chunk -> Values.val -> Values.val->Prop).

  Inductive eval_expr : expr -> Values.val -> Prop :=
  | eval_Avar : forall α, eval_expr (Avar α) (env α)
  | eval_Aconst : forall cst v sp (ge:Cminor.genv),
             Cminor.eval_constant ge sp cst = Some v ->
             eval_expr (Aconst cst) v
    (** For the moment, we ignore Oaddrsymbol (which calls to the
        global environment) and Oaddrstack (which points to the top of
        the local stack-frame). *)
  | eval_Aunop : forall op a1 v1 v,
      eval_expr a1 v1 ->
      Cminor.eval_unop op v1 = Some v ->
      eval_expr (Aunop op a1) v
  | eval_Abinop: forall op a1 a2 v1 v2 v m,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      Cminor.eval_binop op v1 v2 m = Some v ->
      eval_expr (Abinop op a1 a2) v
    (** For the moment, we ignore unsigned comparison of pointers, which requires
        some access to memory. *)
  | eval_Aload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      reads chunk vaddr v ->
      eval_expr (Aload chunk addr) v
  .

End Expr.

Arguments expr var : clear implicits.

Ltac apply_hyps :=
  repeat match goal with
  | H:_|-_ => eapply H
  end
.

Ltac equivariant_eval_expr_tac :=
  simpl; intros h; inversion_clear h; econstructor; apply_hyps
.

Lemma equivariant_eval_expr var `(Action var) : Equivariant (@eval_expr var).
Proof.
  apply equivariant_alt₄.
  intros π env read e v.
  assert ( forall π env read e v,  eval_expr (π · env) (π · read) (π · e) (π · v) -> eval_expr env read e v ) as h.
  { clear. intros π env read e.
    induction e; intros ?; [|equivariant_eval_expr_tac..].
    intros h; inversion h. simpl in *. simplify_act. subst.
    econstructor. }
  apply prop_extensionality.
  split.
  + apply h.
  + intros r.
    apply (h (op_p π)). simplify_act.
    exact r.
Qed.
(* Hint EResolve equivariant_eval_expr : equivariant. *)
Hint Extern 0 (Equivariant eval_expr) => eapply equivariant_eval_expr : equivariant.

Lemma eval_expr_increasing var (env:var->Values.val) :
  forall (reads₁ reads₂:_->_->_->Prop),
  (forall chunk vaddr v, reads₁ chunk vaddr v -> reads₂ chunk vaddr v) ->
  forall e v, eval_expr env reads₁ e v -> eval_expr env reads₂ e v.
Proof.
  intros * h *.
  induction 1; try (econstructor (solve[eauto])).
Qed.

(** Evaluation of pure expressions: ignores [Aload] expressions. *)
Definition eval_pure_expr {var} env e v :=
  eval_expr (var:=var) env (fun _ _ _ => True) e v
.

Lemma equivariant_eval_pure_expr var `(Action var) :
  Equivariant (@eval_pure_expr var).
Proof.
  unfold eval_pure_expr.
  combinatorize.
  narrow_equivariant.
  + easy.
Qed.
(* Hint EResolve equivariant_eval_pure_expr : equivariant. *)
Hint Extern 0 (Equivariant eval_pure_expr) => eapply equivariant_eval_pure_expr : equivariant.


(** Pure expressions as assertions. *)
Definition check_pure_expr {var} env e b :=
  eval_pure_expr (var:=var) env e (Values.Val.of_bool b)
.

Lemma equivariant_check_pure_expr var `(Action var) :
  Equivariant (@check_pure_expr var).
Proof.
  unfold check_pure_expr.
  combinatorize.
  narrow_equivariant.
  + easy.
Qed.
(* Hint EResolve equivariant_check_pure_expr : equivariant. *)
Hint Extern 0 (Equivariant check_pure_expr) => eapply equivariant_check_pure_expr : equivariant.

Definition valid_pure_expr {var} env e b :=
  check_pure_expr (var:=var) env e b /\ ~(check_pure_expr env e (negb b))
.

Lemma equivariant_valid_pure_expr var `(Action var) :
  Equivariant (@valid_pure_expr var).
Proof.
  unfold valid_pure_expr.
  combinatorize.
  Time narrow_equivariant; easy.
Qed.
(* Hint EResolve equivariant_valid_pure_expr : equivariant. *)
Hint Extern 0 (Equivariant valid_pure_expr) => eapply equivariant_valid_pure_expr : equivariant.

(** Substitution. *)
Fixpoint subs {A B} (φ:A->B) (e:expr A) : expr B :=
  match e with
  | Avar v => Avar (φ v)
  | Aconst c => Aconst c
  | Aunop op e => Aunop op (subs φ e)
  | Abinop op e₁ e₂ => Abinop op (subs φ e₁) (subs φ e₂)
  | Aload chunk e => Aload chunk (subs φ e)
  end
.

Fixpoint collect {F} (a:Applicative F) {A} (e:expr (F A)) : F (expr A) :=
  match e with
  | Avar v => a.(map) Avar v
  | Aconst c => pure a (Aconst c)
  | Aunop op e => a.(map) (Aunop op) (collect a e)
  | Abinop op e₁ e₂ => map2 a (Abinop op) (collect a e₁) (collect a e₂)
  | Aload chunk e => a.(map) (Aload chunk) (collect a e)
  end
.

(** Partial renaming. *)
Definition rename {A B} (φ:A->option B) (e:expr A) : option (expr B) :=
  collect Option (subs φ e)
.
(* arnaud: not needed?
(* arnaud: belongs_to_expr can actually be defined in term of [collect], using
   the writer applicative and a list. *)
Fixpoint belongs_to_expr {A} (e:expr A) (x:A) : Prop :=
  match e with
  | Avar v => x=v
  | Aconst _ => False
  | Aunop _ e => belongs_to_expr e x
  | Abinop _ e₁ e₂ => belongs_to_expr e₁ x \/ belongs_to_expr e₂ x
  | Aload _ e => belongs_to_expr e x
  end
.

Lemma value_not_fixed_eval_pure_expr A {_:EqDec A eq} (e:expr A) v :
  central (belongs_to_expr e)
          (fun ρ => eval_pure_expr ρ e v).
Proof.
  unfold central; revert v.
  induction e as [ x | c | op e he | op e₁ he₁ e₂ he₂ | chunk e he ]; simpl.
  - intros ** ν h.
    inversion h; subst; clear h.
    assert (ν x = swap α β ν x) as ->.
    { unfold swap.
      rewrite !if_eq_neq; congruence. }
    constructor.
  - intros ** h.
    inversion h; subst; clear h.
    econstructor; eauto.
  - intros ** h.
    inversion h; subst; clear h.
    econstructor; eauto.
    now apply he.
  - intros v α β hα hβ ** h.
    inversion h; subst; clear h.
    econstructor; eauto; [apply he₁|apply he₂]; solve[easy|clear -hα hβ; firstorder].
  - intros ** h.
    inversion h; subst; clear h.
    econstructor; eauto.
    eapply he; eauto.
Qed.

Lemma value_not_fixed_check_pure_expr A {_:EqDec A eq} (e:expr A) b :
  central (belongs_to_expr e)
          (fun ρ => check_pure_expr ρ e b).
Proof.
  apply value_not_fixed_eval_pure_expr.
Qed.

Lemma value_not_fixed_valid_pure_expr A {_:EqDec A eq} (e:expr A) b :
  central (belongs_to_expr e)
          (fun ρ => valid_pure_expr ρ e b).
Proof.
  unfold central, valid_pure_expr.
  intros ** [h₁ h₂].
  split.
  - apply value_not_fixed_check_pure_expr; eauto.
  - intros h₃; apply h₂.
    assert (ν = swap α β (swap α β ν)) as h₄.
    { extensionality x.
      now rewrite swap_idempotent. }
    rewrite h₄.
    apply value_not_fixed_check_pure_expr; eauto.
Qed. *)
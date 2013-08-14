Require Import Cosa.Lib.Header.
Require Cminor.

(** An abstract notion of expression. The type [expr] is a variant of
    [Cminor.expr] where the variables are taken to be at an arbitrary
    type rather than a type of identifier. They will be instantiated
    with [Graph.node]. Most of the evaluation relation is reused from
    [Cminor].*)

Section Expr.

  Context {var:Type}.

  Inductive expr :=
  | Avar : var -> expr
  | Aconst : Cminor.constant -> expr
  | Aunop : Cminor.unary_operation -> expr -> expr
  | Abinop : Cminor.binary_operation -> expr -> expr -> expr
  | Aload : AST.memory_chunk -> expr -> expr
  .

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

(** Pure expressions as assertions. *)
Definition check_pure_expr {var} env e b :=
  eval_pure_expr (var:=var) env e (Values.Val.of_bool b)
.

Definition valid_pure_expr {var} env e b :=
  check_pure_expr (var:=var) env e b /\ ~(check_pure_expr env e (negb b))
.   

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
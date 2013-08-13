Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.Lang.
Import EquivDec.

(** A definition of value domains. It's design so as to be simple to
    wrap around [AbMachinEnv.ab_machine_env] from the Verasco cfg
    analyser. *)

(** Lifts a concretisation on [A] to a concretisation on [option A] *)
Definition lift {A B} (γ:A->℘ B) : option A -> ℘ B :=
  fun x => 
    match x with
    | Some a => γ a
    | None => ∅
    end
.

Definition update {var val} {_:EqDec var eq} (ρ:var -> val) (x:var) (v:val) : var -> val :=
  fun y => if equiv_dec y x then v else ρ y
.

Record t (var:Type) {dec_var:EqDec var eq} := {
  carrier :> Type ;
  γ : carrier -> ℘ (var -> Values.val) ;
  leb : carrier -> carrier -> bool ;
  leb_correct : forall a b, leb a b = true -> γ a ⊆ γ b ;
  top : carrier ;
  top_correct : forall a, a ∈ γ top ;
  join : carrier -> carrier -> carrier ;
  join_correct : forall a b, γ a ∪ γ b ⊆ γ (join a b) ;
  widen : carrier -> carrier -> carrier ;
  (** No property is imposed on widen, as its action is checked afterwards. *)
  assign : var -> expr var -> carrier -> option carrier ;
  assign_correct : forall x e v a ρ,
    ρ ∈ γ a ->
    v ∈ eval_pure_expr ρ e ->
    update ρ x v ∈ lift γ (assign x e a) ;
  assume : Lang.expr var -> bool -> carrier -> option carrier ;
  assume_correct : forall e b a ρ,
    ρ ∈ γ a ->
    b ∈ check_pure_expr ρ e ->
    ρ ∈ lift γ (assume e b a) ;
  prove : Lang.expr var -> bool -> carrier -> bool ;
  prove_correct : forall e b a ρ,
    prove e b a = true ->
    ρ ∈ γ a ->
    b ∈ valid_pure_expr ρ e
}.
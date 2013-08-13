Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.NumericalDomain.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Shape.Summary.
Require Import Cosa.Shape.Graph.
(* spiwack: [Graph] and [NumericalDomain] are imported because of typeclasses. *)

(** Pairing of a [Graph.t] and a value domain element. *)
Module NumGraph.

Section NumGraph.

Variable num_dom : NumericalDomain.t Graph.node.
Variable ind_env : Summary.env.

Definition t := (Graph.t ind_env * num_dom)%type.

Let γ_graph (g:Graph.t ind_env) : ℘ (Graph.conc) :=
  Graph.γ (Summary.γ ind_env) g
.

(** [γ_num a] is the set of all concrete states whose valuation is in
    in the concretisation of [a]. *)
Let γ_num (a:num_dom) : ℘ (Graph.conc) :=
  fun s => fst s ∈ NumericalDomain.γ _ _ a
.

Definition γ (a:t) : ℘ (Graph.conc) :=
  γ_graph (fst a) ∩ γ_num (snd a)
.

End NumGraph.

End NumGraph.


(** The abstract domain is the set of pairs of a [NumGraph.t] and an
    abstract environment relating variables to nodes in the graph. *)

(** Concrete environments. *)
Notation cenv := (PTree.t Values.val).

(** Abstract environments. *)
Notation aenv := (PTree.t Graph.node).


Definition compatible_env (ν:valuation) (e:cenv) (e':aenv) :=
  forall x, e!x = option_map ν (e'!x)
.

Section ShapeDomain.

Variable num_dom : NumericalDomain.t Graph.node.
Variable ind_env : Summary.env.

Definition t := (aenv*NumGraph.t num_dom ind_env)%type.


End ShapeDomain.
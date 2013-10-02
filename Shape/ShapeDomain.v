(** In this file, the shape domain of Cosa is defined *)

Require Import Cosa.Lib.Header.
Require Import Cosa.Abstract.NumericalDomain.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Shape.Summary.
Require Import Cosa.Shape.Graph.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Interaction.Rule.
Require Import Cosa.Shape.ShapeDomainSig.

(* WORK IN PROGRESS *)

Section Domain.

  Variable num_dom : NumericalDomain.t Graph.node.
  Variable ind_env : Summary.env.

  (** Domain signature *)
  Record t := {
     carrier :> Type ;
     γ : carrier -> ℘ (cenv*ConcreteFragment.fragment) ;

     inclusion : Rule.rule_set (carrier*carrier) (carrier*carrier) ;
     inclusion_correct : forall g₁ g₂, Proof_of (deductive inclusion) (g₁,g₂) -> γ g₁ ⊆ γ g₂
     (** More operations here. *)
  }.

  (** inclusion is not fully implemented yet. We replace it by a dummy [Rule_set]
      in which there are no proofs. *)
  Definition inclusion_rules {S} : Rule.rule_set S S := {|
    Rule := Empty_set ;
    action := fun magic => match magic with end
  |}.

  Program Definition make : t := {|
     carrier := ShapeDomainSig.t num_dom ind_env ;
     γ := ShapeDomainSig.γ ;

     inclusion := inclusion_rules
  |}.
  Next Obligation. (** inclusion_correct *)
    destruct X.
    simpl in c.
    destruct c as [ [] ? ].
  Qed. (** it is true, though as inclusion is a dummy, irrelevant. *)

End Domain.
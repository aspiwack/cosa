(** Adding axioms about equality. The goal is to handle equality of
    predicates smoothly, to be used for the concretisation of graphs
    (see [Cosa.Shape.Graph].*)

(** Axiom of functional extensionality. *)
Require Export Coq.Logic.FunctionalExtensionality.

(** Axiom of propositional extensionality. By
    Coq.Logic.ClassicalFacts.ext_prop_dep_proof_irrel_cic it also
    implies proof irrelevance, but I don't plan on making use of that
    fact. *)
Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
Require Export Cosa.Lib.Axioms.
Require Export Coq.PArith.BinPos.
Require Export Coq.Numbers.Integer.Binary.ZBinary.
Require Export Cosa.Lib.Bracket.
Require Export Cosa.Lib.Tactics.
Require Export Cosa.Lib.Algebra.
Require Export Cosa.Lib.Extra.
Require Export Cosa.Lib.CompleteLattice.
Require Export Cosa.Lib.Predicate.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Maps.
Require Export Coq.Classes.Morphisms.
Export List.ListNotations.

(** Out of the tactic module because the combinators are defined there
    and it would clash with the Ocaml module initialisation. If it is
    needed earlier, the combinators should be moved to a separate
    file. *)
Declare ML Module "combinatorize".

Ltac combinatorize :=
  lazymatch goal with
  | |- ?c => let c' := eval combinatorize in c in change c with c'
  end
.
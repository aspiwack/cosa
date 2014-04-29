Require Import Cosa.Lib.Header.
Require Import Cosa.Nominal.Set.
Require Import AST.
(* Require Import Memory. *)
Require Import Values.


(** This files defines nominal instances for Compcert types. (all
    discrete, of course). *)


Instance chunk_nominal : Nominal AST.memory_chunk := discrete_nominal.
Instance val_nominal : Nominal val := discrete_nominal.
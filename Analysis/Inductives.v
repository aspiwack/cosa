Require Import Cosa.Lib.Header.
Require compcert.common.Memdata.
Require Import Cosa.Interaction.Interaction.
Require Import Cosa.Interaction.InteractionLib.
Require Import Cosa.Abstract.Lang.
Require Import Cosa.Shape.Graph.
Require Import Cosa.Shape.Summary.
Import List.ListNotations.

(** In this file we define the concrete instances of inductive shapes
    we are interested in. *)

(** spiwack: I have few *)

Inductive name :=
| List
| ListSegment (β:Graph.node)
.

Local Notation "α ≡ β" := (Lang.Abinop (Cminor.Ocmpu Integers.Ceq) α β) (at level 70).
Local Notation "α ≠ β" := (Lang.Aunop Cminor.Onegint (α≡β)) (at level 70).
Local Notation "0" := (Lang.Aconst (Cminor.Ointconst Int.zero)).

Definition add_chunk (offs:int) (chunk:AST.memory_chunk) : int :=
  Int.add offs (Int.repr (Memdata.size_chunk chunk))
.

Definition def (i:name) (α:node) : Interaction (℘ node) (Summary.rule name) :=
  match i with
  | List =>
    Interaction.pi (Finite.access [
        just (Graph.NodeTree.empty _, (Avar α) ≡ 0) (** empty list *);
        bind with_new (fun β => (** head *)
        bind with_new (fun δ => (** tail *)
            just (NodeTree.set α (Point_to
                    [(Int.zero,{|destination:=(β,Int.zero);size:=AST.Mint32|});
                     (add_chunk (Int.zero) AST.Mint32,{|destination:=(δ,Int.zero);size:=AST.Mint32|})]
                   )
                  (NodeTree.set δ (Summarized List)
                  (NodeTree.empty _)) ,
                  (Avar α) ≠ 0)))
      ])
  | ListSegment β =>
    Interaction.pi (Finite.access [
        just (Graph.NodeTree.empty _, (Avar α) ≡ (Avar β)) (** empty segment *);
        bind with_new (fun γ => (* head *)
        bind with_new (fun δ => (* tail *)
            just (NodeTree.set α (Point_to
                    [(Int.zero,{|destination:=(γ,Int.zero);size:=AST.Mint32|});
                     (add_chunk (Int.zero) AST.Mint32,{|destination:=(δ,Int.zero);size:=AST.Mint32|})]
                   )
                  (NodeTree.set δ (Summarized (ListSegment β))
                  (NodeTree.empty _)) ,
                  (Avar α) ≠ 0)))
      ])
  end
.
Require Import Cosa.Lib.Header.
Require Import Cosa.Lib.Relation.
Require Import Cosa.Interaction.Transition.

(** Interaction structures, due to Peter Hancock, are an intentional
    representation of transition systems with disjunctive (angelic)
    and conjunctive (demonic) non-determinism. They are a very generic
    kind of data and therefore can be used in various way. One of the
    most important way is that it can be used to represent an
    interface, where capabilities (in form of command) are provided by
    an implementer, and a user can issue commands to advance the
    internal state. They can also be used as proof inference systems,
    which we shall leverage for certificate checking.

    The definition of interaction structures given here is expanded,
    but an alternative definition is [A -> Fam (Fam B)], where
    [Fam X = { i:Type & I -> X}] is the type of families on [X] with
    an arbitrary index. *)

Record Interaction {A B:Type} := {
  Com : A -> Type; (** Issuable commands *)
  Resp : forall {a:A}, Com a -> Type; (** Responses *)
  Output : forall {a:A} {c:Com a}, Resp c -> B (** Output state *)
}.
Arguments Interaction _ _ : clear implicits.

Definition Interface (A:Type) := Interaction A A.

(** Predicate transformers *)

(** For any complete lattice Ω, interaction structures act on
    "predicates" mapping into Ω. Mapping commands to a join and
    responses to a meet. *)
Definition Angelic {A B} Γ (i:Interaction A B) : (B->rel Γ) -> (A->rel Γ) :=
  fun X a => Join (fun c:i.(Com) a => Meet (fun x:i.(Resp) c => X(i.(Output) x)))
.

Instance angelic_increasing {A B} Γ (i:Interaction A B) :
  Proper (@sub (B::Γ) ==> @sub (A::Γ)) (Angelic Γ i)
.
Proof.
  unfold Proper, respectful, Subset, Angelic.
  intros p q p_sub_q;simpl; intros a.
  apply Join_increasing; simpl; intros c.
  apply Meet_increasing; simpl.
  eauto.
Qed.
  
(** Dually, we can map commands to a meet and responses to a join. *)
Definition Demonic {A B} Γ (i:Interaction A B) : (B->rel Γ) -> (A->rel Γ) :=
  fun X a => Meet (fun c:i.(Com) a => Join (fun x:i.(Resp) c => X(i.(Output) x)))
.

Instance demonic_increasing {A B} Γ (i:Interaction A B) :
  Proper (@sub (B::Γ) ==> @sub (A::Γ)) (Demonic Γ i)
.
Proof.
  unfold Proper, respectful, Subset, Demonic.
  intros p q p_sub_q; simpl; intros a.
  apply Meet_increasing; simpl; intros c.
  apply Join_increasing; simpl.
  eauto.
Qed.

(** Sequence *)

Definition skip {S} : Interface S := {|
  Com s := unit ;
  Resp s c := unit ;
  Output s c x := s
|}.

Definition seq {S T U} (i:Interaction S T) (j:Interaction T U) : Interaction S U := {|
  Com s := { c₁ : i.(Com) s & forall x₁:i.(Resp) c₁, j.(Com) (i.(Output) x₁) } ;
  Resp s c := { x₁ : i.(Resp) (projT1 c) & j.(Resp) (projT2 c x₁) };
  Output s c x := j.(Output) (projT2 x)
|}.

(** "Monadic" unit and bind *)
Definition munit {S A} (a:A) : Interaction S (A*S) := {|
  Com s := unit ;
  Resp s c := unit ;
  Output s c x := (a,s)
|}.

Definition curry {A S T} (i:A->Interaction S T) : Interaction (A*S) T := {|
  Com s := (i (fst s)).(Com) (snd s);
  Resp s c := (i (fst s)).(Resp) c;
  Output s c x := (i (fst s)).(Output) x
|}.

Definition bind {S T U A} (i:Interaction S (A*T)) (j:A->Interaction T U) : Interaction S U :=
  seq i (curry j)
.

(** Cartesian product *)

Definition pi {A S T} (i:A->Interaction S T) : Interaction S T := {|
  Com s := forall a:A, (i a).(Com) s ;
  Resp s c := { a:A & (i a).(Resp) (c a) } ;
  Output s c x := (i (projT1 x)).(Output) (projT2 x)
|}.

(** Sum *)

Definition sigma {A S T} (i:A->Interaction S T) : Interaction S T := {|
  Com s := { a:A & (i a).(Com) s } ;
  Resp s c := (i (projT1 c)).(Resp) (projT2 c) ;
  Output s c x := (i (projT1 c)).(Output) x
|}.

(** Tensor product *)

Definition tensor {S₁ T₁ S₂ T₂} (i:Interaction S₁ T₁) (j:Interaction S₂ T₂) : Interaction (S₁*S₂) (T₁*T₂) := {|
  Com s := (i.(Com) (fst s) * j.(Com) (snd s))%type ;
  Resp s c := (i.(Resp) (fst c) * j.(Resp) (snd c))%type ;
  Output s c x := (i.(Output) (fst x) , j.(Output) (snd x))
|}.

(** Angelic iteration *)

Inductive Prog {S} {i:Interface S} {s:S} : Type:=
 | ret : Prog
 | issue (c:i.(Com) s) (k:forall (x:i.(Resp) c), @Prog S i (i.(Output) x)) : Prog
.
Arguments Prog {S} i _ : clear implicits.

(* arnaud: TProg et RProg sont assez mystérieux avec tous ces arguments implicites. Il vaudrait peut-être bien de les expliquer un peu mieux, ou peut-être de rendre plus d'arguments explicites… *)
Fixpoint TProg {S} {i:Interface S} {s} (p:Prog i s) : Type :=
  match p with
  | ret => unit
  | issue c k => { x:i.(Resp) c & TProg (k x) }
  end
.

Fixpoint RProg {S} {i:Interface S} {s} {p:Prog i s} (x:TProg p) : S :=
  match p return TProg p -> S with
  | ret => fun _ => s
  | issue c k => fun x => RProg (projT2 x)
  end x
.

Definition angelic_iteration {S} (i:Interface S) : Interface S := {|
  Com s := Prog i s ;
  Resp s c := TProg c ;
  Output s c x := RProg x
|}.

(*** Demonic iteration ***)

(* TODO *)

(*** Angelic extension of transition structure. ***)
Definition angelic_extension {S T} (t:Transition S T) : Interaction S T := {|
  Com := t.(trans) ;
  Resp s c := unit ;
  Output s c x := t.(next) s c
|}.

(*** Demonic extension of transition structure. ***)
Definition demonic_extension {S T} (t:Transition S T) : Interaction S T := {|
  Com s := unit ; 
  Resp s c := t.(trans) s ;
  Output s c x := t.(next) s x
|}.

(** Extension of a function *)
Definition functional_extension {S T} (f:S->T) : Interaction S T := {|
  Com s := unit ;
  Resp s c := unit ;
  Output s c x := f s
|}.

(*** Interaction structures as proof systems ***)

(* Interfaces are seen as a set of inference rules, where the states
   are the goals or judgement to be proved.

   The type of proofs for a given set of inference rules is just like
   the type of programs except there is no way to return the current
   goal: the proof is finished when there are no goals left to prove,
   i.e. when issuing a command whose return type is the empty type. *)
Inductive Proof_of {S} {i:Interface S} {s:S} : Type:=
 | rule (c:i.(Com) s) (k:forall (x:i.(Resp) c), @Proof_of S i (i.(Output) x)) : Proof_of
.
Arguments Proof_of {S} i _ : clear implicits.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Require Import Coq.Logic.Eqdep_dec.
Require Import Cosa.Lib.Extra.

(** Initial segments of ℕ, aka (skeletal) finite types. *)

Fixpoint fin (n:nat) : Type := match n with
  | 0 => Empty_set
  | S n' => option (fin n')
end.

(** Vectors are lists anotated by their size. *)
Definition vector (A:Type) (n:nat) := { l:list A | length l = n }.

(** Because the equality on natural number is decidable, [eq] has uip
    on nat. *)
Lemma nat_eq_uip (n m:nat) : forall (p q:n=m), p = q.
Proof.
  apply UIP_dec.
  { decide equality. }
Qed.

(** Because the equality on natural number is decidable, vector
    equality is just the equality of the underlying list. *)
Lemma vector_eq {A n} (l v:vector A n) : `l = `v -> l = v.
Proof.
  destruct l as [ l ? ]; destruct v as [ v ? ]; simpl.
  intros ->.
  f_equal.
  apply nat_eq_uip.
Qed.

Definition pack_vector {A:Type} (l:list A) : vector A (length l) :=
  exist _ l eq_refl
.

(** A function [fin n -> A] is essentially a list of [A] *)
Fixpoint listify {A n} : (fin n -> A) -> list A :=
  match n as n return (fin n -> A) -> list A with
  | 0 => fun _ => nil
  | S n' => fun f => f None :: listify (fun (i:fin n') => f (Some i))
  end
.

Lemma listify_length {A n} (f:fin n -> A) : length (listify f) = n.
Proof.
  induction n as [ | n h ].
  - easy.
  - simpl.
    f_equal.
    auto.
Qed.

Program Definition listifyv {A n} (f:fin n -> A) : vector A n :=
  listify f
.
Next Obligation.
  apply listify_length.
Qed.

Lemma listifyv_correct {A n} (f:fin n -> A) : proj1_sig (listifyv f) = listify f.
Proof.
  reflexivity.
Qed.

Definition elim_nil_s {A B n} (p:length (@nil A) = S n) : B.
Proof.
  discriminate p.
Defined.

Definition strip_s {n m} (p:S n = S m) : n=m :=
  match p
        in (_ = y)
        return (n = match y with
                    | 0 => n
                    | S n0 => n0
                    end)
  with
  | eq_refl => eq_refl
  end
.

Fixpoint accessv {A n} : vector A n -> fin n -> A :=
  match n as n return vector A n -> fin n -> A with
  | 0 => fun _ (i:Empty_set) => match i with end
  | S n' => fun v =>
              let '(exist l e) := v in
              match l
                    as l
                    return length l = S n' -> fin (S n') -> A
              with
              | a::l' => fun (e:length (a::l') = S n') i =>
                match i return A with
                | None => a
                | Some i' => accessv (exist _ l' (strip_s e)) i'
                end
              | nil => elim_nil_s
              end e
  end
.
    
Definition access {A} (l:list A) (i:fin (length l)) : A :=
  accessv (pack_vector l) i
.

Lemma accessv_correct {A} (l:list A) : forall i, accessv (pack_vector l) i = access l i.
Proof. easy. Qed.


Lemma listify_access {A} (l:list A) : listify (access l) = l.
Proof.
  induction l.
  - easy.
  - simpl.
    f_equal.
    assumption.
Qed.

Lemma listifyv_accessv {A n} (l:vector A n) : listifyv (accessv l) = l.
Proof.
  destruct l as [ l <- ].
  apply vector_eq.
  simpl.
  refine (listify_access _).
Qed.


(** [forall i, access (listify f) i = f i] is basically true, but does
    not typecheck. We only have the vectorised version. *)
Lemma accessv_listifyv {A n} (f:fin n -> A) : forall i, accessv (listifyv f) i = f i.
Proof.
  induction n as [ | n h ].
  - (* n=0 *)
    intros [].
  - (* n=S n *)
    unfold listifyv; simpl.
    intros [ i' | ].
    + (* i=Some i' *)
      unfold listifyv in h.
      specialize (h (fun i=>f (Some i)) i').
      match goal with
      | H:appcontext[exist _ _ ?e₁] |-appcontext[exist _ _ ?e₂] => assert (e₁=e₂) as ->
      end.
      { apply nat_eq_uip. }
      apply h.
    + (* i=None *)
      reflexivity.
Qed.




(** The type [Collectible] is a caracterisation of finite types (see
    http://winterkoninkje.dreamwidth.org/81209.html ). In Coq, it is
    not probably weaker to having a list of all the elements which is
    also true of [fin n].

   We use collectibility in [Cosa.Interaction.Rule]. *)

Section Collection.

  Context {F:Type->Type} (a:Applicative F).

  Definition Collectible A := forall B, (forall x:A, F (B x)) -> F (forall x:A,B x).

  Definition patch {A B} (n:B None) (s:forall x:A, B (Some x)) : forall x:option A, B x :=
    fun x => match x with None => n | Some x => s x end
  .

  Fixpoint collectn {n} : Collectible (fin n) :=
    match n as n return Collectible (fin n) with
    | 0 => fun _ _ => pure a (fun i:Empty_set => match i with end)
    | S _ => fun B f =>
               let n := f None in
               let s := collectn _ (fun i => f (Some i)) in
               map2 a patch n s
    end
  .

End Collection.
Arguments Collectible F A : clear implicits.
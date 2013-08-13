(** This file contains miscellaneous lemmas *)

Require Import Cosa.Lib.Tactics.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Import List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Lemma list_map_nil A B (f:A->B) : List.map f [] = [].
Proof. easy. Qed.

Lemma list_map_cons A B (f:A->B) : forall a l, List.map f (a::l) = f a :: List.map f l.
Proof. easy. Qed.

Lemma singleton_eq_norepet A (a:A) (l:list A) :
  (forall x, In x l <-> x=a) ->
  list_norepet l ->
  [a] = l.
Proof.
  intros h₁ h₂.
  destruct h₂ as [ | y l ni hl ].
  { simpl in h₁.
    specialize (h₁ a); firstorder. }
  simpl in h₁.
  generalize (h₁ y); destruct 1 as [ h₂ _ ].
  prove_hyp h₂.
  { left; trivial. }
  rewrite h₂ in *; clear h₂.
  destruct l as [ | z l ].
  { easy. }
  simpl in h₁, ni.
  specialize (h₁ z).
  firstorder.
Qed.


Lemma ptree_equal_eq_alt A (m₁ m₂:PTree.t A) :
  PTree_Properties.Equal _ m₁ m₂ <-> (forall k, m₁!k = m₂!k).
Proof.
  unfold PTree_Properties.Equal.
  split.
  - intros h k.
    specialize (h k).
    destruct (m₁!k); destruct (m₂!k); unfold Equivalence.equiv in *; (easy||congruence).
  - intros h k.
    specialize (h k).
    rewrite h.
    now destruct (m₂!k).
Qed.

(** Category of PERs *)

(** spiwack: we probably will not need the correction properties in
    [Functor] and [Applicative]. It is more a sanity check on my
    part. *)
Local Notation Rel A := (A->A->Prop).
Local Open Scope signature_scope.

Definition id {A:Type} (x:A) : A := x.
Definition comp {A B C:Type} (f:A->B) (g:B->C) (x:A) : C := g (f x).

Instance id_proper A (E:Rel A) : Proper (E==>E) id.
Proof. compute; easy. Qed.

Instance comp_proper A (E₁:Rel A) B (E₂:Rel B) C (E₃:Rel C) :
  Proper ((E₁==>E₂)==>(E₂==>E₃)==>(E₁==>E₃)) comp.
Proof. compute; eauto. Qed.

Lemma comp_assoc A (E₁:Rel A) B (E₂:Rel B) C (E₃:Rel C) D (E₄:Rel D) :
  forall f g h,
    Proper (E₁==>E₂) f ->
    Proper (E₂==>E₃) g ->
    Proper (E₃==>E₄) h ->
    (E₁==>E₄)%signature (comp (comp f g) h) (comp f (comp g h)).
Proof. compute; eauto. Qed.

Lemma comp_id_left_neutral A (E₁:Rel A) B (E₂:Rel B) :
  forall f, Proper (E₁==>E₂) f ->
            (E₁==>E₂) (comp id f) f.
Proof. compute;eauto. Qed.

Lemma comp_id_right_neutral A (E₁:Rel A) B (E₂:Rel B) :
  forall f, Proper (E₁==>E₂) f ->
            (E₁==>E₂) (comp f id) f.
Proof. compute;eauto. Qed.


Definition map_prod {A B C D} (f:A->B) (g:C->D) : (A*C) -> (B*D) :=
  fun ac => (f (fst ac) , g (snd ac))
.

Definition per_prod {A B} (E₁:Rel A) (E₂:Rel B) : Rel (A*B) :=
  fun ab₁ ab₂ =>
    E₁ (fst (ab₁)) (fst (ab₂)) /\
    E₂ (snd (ab₁)) (snd (ab₂))
.
Instance per_prod_per A (E₁:Rel A) {e₁:PER E₁} B (E₂:Rel B) {e₂: PER E₂} :
  PER (per_prod E₁ E₂).
Proof.
  split.
  - intros [ a₁ b₁ ] [ a₂ b₂ ]; compute.
    easy.
  - intros [ a₁ b₁ ] [ a₂ b₂ ] [ a₃ b₃ ]; compute.
    intuition solve_transitivity.
Qed.

Definition per_unit : Rel unit :=
  fun _ _ => True
.
Instance per_unit_per : PER per_unit.
Proof. easy. Qed.

(** Functors. *)

Record Functor {F:Type->Type} := {
  map : forall {A B}, (A->B) -> (F A->F B) ;

  per_map : forall {A} (E:Rel A) {_:PER E}, Rel (F A) ;
  per_map_per : forall A (E:Rel A) {e:PER E}, PER (per_map E) ;

  map_id : forall A (E:Rel A) {e:PER E},
             (per_map E ==> per_map E) (map (@id A)) id ;
  map_comp :
    forall A (E₁:Rel A) {e₁:PER E₁} B (E₂:Rel B) {e₂:PER E₂} C (E₃:Rel C) {e₃:PER E₃},
    forall (f:A->B) {p₁:Proper (E₁==>E₂) f} (g:B->C) {p₂:Proper (E₂==>E₃) g},
      (per_map E₁ ==> per_map E₃) (map (comp f g)) (comp (map f) (map g))
}.
Arguments Functor F : clear implicits.
Existing Instance per_map_per.

Definition option_per_map {A} (E:Rel A) o₁ o₂ :=
  match o₁,o₂ return _ with
  | Some x₁ , Some x₂ => E x₁ x₂
  | None , None => True
  | _ , _ => False
  end
.
Program Definition option_functor : Functor option := {|
  map := option_map ;
  per_map A E e := option_per_map E
|}.
Next Obligation.
  split.
  - intros [x₁|] [x₂|]; compute; easy.
  - intros [x₁|] [x₂|] [x₃|]; try (compute;easy).
    unfold option_per_map.
    intros **.
    solve_transitivity.
Qed.
Next Obligation.
  compute.
  intros [x₁|] [x₂|]; easy.
Qed.
Next Obligation.
  compute.
  intros [x₁|] [x₂|]; try easy.
  eauto.
Qed.

(** Applicative functors. *)

(** We define applicative functors as lax-monoidal functors. See
    for instance http://blog.ezyang.com/2012/08/applicative-functors/
    about the equivalence with the usual presentation. *)

Definition assoc {A B C} (x:(A*(B*C))) : (A*B)*C :=
  let '(a,(b,c)) := x in ((a,b),c)
.

Record Applicative {F:Type->Type} := {
  a_functor :> Functor F ;

  cunit : F unit ;
  collect : forall {A B}, F A -> F B -> F(A*B)%type ;

  naturality : forall A (E₁:Rel A) {e₁:PER E₁} B (E₂:Rel B) {e₂:PER E₂}
                      C (E₃:Rel C) {e₃:PER E₃} D (E₄:Rel D) {e₄:PER E₄},
               forall f {p₁:Proper (E₁==>E₂) f} g {p₂:Proper (E₃==>E₄) g}
                      u {p₃:Proper (a_functor.(per_map) E₁) u} 
                      v {p₄:Proper (a_functor.(per_map) E₃) v},
                 a_functor.(per_map) (per_prod E₂ E₄)
                                     (a_functor.(map) (map_prod f g) (collect u v))
                                     (collect (a_functor.(map) f u) (a_functor.(map) g v));
  cunit_left_neutral : forall A (E₁:Rel A) {e₁:PER E₁}
                              u {p:Proper (a_functor.(per_map) E₁) u},
                        a_functor.(per_map) (per_prod per_unit E₁)
                                            (collect cunit u)
                                            (a_functor.(map) (fun x => (tt,x)) u) ;
  cunit_right_neutral : forall A (E₁:Rel A) {e₁:PER E₁}
                              u {p:Proper (a_functor.(per_map) E₁) u},
                         a_functor.(per_map) (per_prod E₁ per_unit)
                                             (collect u cunit)
                                             (a_functor.(map) (fun x => (x,tt)) u) ;
  collect_assoc : forall A (E₁:Rel A)  {e₁:PER E₁} B (E₂:Rel B) {e₂:PER E₂}
                         C (E₃:Rel C) {e₃:PER E₃}
                         u {p₁:Proper (a_functor.(per_map) E₁) u} 
                         v {p₂:Proper (a_functor.(per_map) E₂) v}
                         w {p₃:Proper (a_functor.(per_map) E₃) w},
                    a_functor.(per_map) (per_prod (per_prod E₁ E₂) E₃)
                      (collect (collect u v) w)
                      (a_functor.(map) assoc (collect u (collect v w)))
}.
Arguments Applicative F : clear implicits.

(** Extra primitives for applicative functors. *)
Definition pure {F} (a:Applicative F) {A} (x:A) : F A :=
  a.(map) (fun _ => x) a.(cunit)
.

Definition app {F} (a:Applicative F) {A B} (f:F(A->B)) (x:F A) : F B :=
  let eval := (fun fx => fst fx (snd fx)) in
  a.(map) eval (a.(collect) f x)
.

(** n-ary map operations. We could make a variadic version, but it
    would be awkward to use. *)
Definition map2 {F} (a:Applicative F) {A B C} (f:A->B->C) (x:F A) (y:F B) : F C :=
  app a (app a (pure a f) x) y
.
Definition map3 {F} (a:Applicative F) {A B C D} (f:A->B->C->D) (x:F A) (y:F B) (z:F C): F D :=
  app a (app a (app a (pure a f) x) y) z
.


Definition option_collect {A B} (o₁:option A) (o₂:option B) : option (A*B) :=
  match o₁,o₂ return _ with
  | Some x₁,Some x₂ => Some (x₁,x₂)
  | _,_ => None
  end
.

Program Definition Option : Applicative option := {|
  a_functor := option_functor ;
  cunit := Some tt ;
  collect := @option_collect
|}.
Solve All Obligations using
  intros **;
  compute;
  repeat match goal with
  | u:option _ |- _ => destruct u; try easy
  end;
  solve[intuition eauto].
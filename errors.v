(** * Monad for raising runtime errors *)

Require Import utils.
Require Import String.
Require Import ssreflect ssrbool.
Set Implicit Arguments.

(** monadic values *)
Variant E A := ret(a: A) | err(e: string).
Arguments err {_} _.

Declare Scope error_scope.
Bind Scope error_scope with E.
Open Scope error_scope.

(** standard monadic operations *)
Definition e_bind {A B} (x: E A) (f: A -> E B): E B :=
  match x with ret a => f a | err e => err e end.
Notation "x >>= f" := (e_bind x f) (at level 30): error_scope.
Notation "'elet' x := f 'in' g" := (e_bind f (fun x => g)) (at level 200, x binder, right associativity): error_scope.  

Definition e_bind2 {A B C} (x: E A) (y: E B) (f: A -> B -> E C): E C :=
  x >>= fun a => y >>= f a.
Definition e_map {A B} (f: A -> B) (x: E A): E B := e_bind x (fun a => ret (f a)).
Definition e_map2 {A B C} (f: A -> B -> C) (x: E A) (y: E B): E C := e_bind2 x y (fun a b => ret (f a b)).

Fixpoint emap {A B} (f: A -> E B) (l: list A): E (list B) :=
  match l with
  | nil => ret nil
  | cons x q => elet x := f x in elet q := emap f q in ret (cons x q)
  end.

Definition assert (b: bool) (e: string): E (is_true b) :=
  if b return E (is_true b) then ret eq_refl else err e.


(** lifting predicates to monadic values: errors are left unspecified *)
Definition EP {A} (P: A -> Prop) (x: E A) := match x with ret a => P a | err _ => True end.
Variant EP' {A} (P: A -> Prop): E A -> Prop :=
  | ep_ret: forall a, P a -> EP' P (ret a)
  | ep_err: forall s, EP' P (err s).
Lemma EPV {A} (P: A -> Prop) (x: E A): EP' P x <-> EP P x.
Proof. split. by case. by case x; constructor. Qed.

(** lifting relations to monadic values *)
Definition ER {A B} (R: A -> B -> Prop) (x: E A) (y: E B) :=
  match x,y with
  | ret a, ret b => R a b
  | err _, err _ => True
  | _,_ => False
  end.
Variant ER' {A B} (R: A -> B -> Prop): E A -> E B -> Prop :=
  | er_ret a b: R a b -> ER' R (ret a) (ret b)
  | er_err s t: ER' R (err s) (err t).
Lemma ERV {A B} (R: A -> B -> Prop) (x: E A) (y: E B): ER' R x y <-> ER R x y.
Proof. split. by case. by case: x y =>?[]//; constructor. Qed.

(** helpers for proving lifted predicates *)
Lemma ep_bind {A B} (f: A -> E B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> EP Q (f a)): forall a, EP P a -> EP Q (a >>= f).
Proof. by case. Qed.

Lemma ep_bind2 {A B C} (f: A -> B -> E C) (P: A -> Prop) (Q: B -> Prop) (R: C -> Prop)
      (F: forall a b, P a -> Q b -> EP R (f a b)): forall a b, EP P a -> EP Q b -> EP R (elet a := a in b >>= f a).
Proof. eauto using ep_bind. Qed.

Lemma ep_map {A B} (f: A -> B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> Q (f a)): forall a, EP P a -> EP Q (e_map f a).
Proof. by apply ep_bind. Qed.

Lemma ep_map2 {A B C} (f: A -> B -> C) (P: A -> Prop) (Q: B -> Prop) (R: C -> Prop)
      (F: forall a b, P a -> Q b -> R (f a b)): forall a b, EP P a -> EP Q b -> EP R (e_map2 f a b).
Proof. by apply ep_bind2. Qed.

Lemma er_bind {A B C D} (f: A -> E B) (g: C -> E D) (R: A -> C -> Prop) (S: B -> D -> Prop)
      (F: forall a c, R a c -> ER S (f a) (g c)): forall a c, ER R a c -> ER S (a>>=f) (c>>=g).
Proof. case=>?[]//=. auto. Qed.

Lemma er_map {A B C D} (f: A -> B) (g: C -> D) (R: A -> C -> Prop) (S: B -> D -> Prop)
      (F: forall a c, R a c -> S (f a) (g c)): forall a c, ER R a c -> ER S (e_map f a) (e_map g c).
Proof. apply er_bind; auto. Qed.

(** special case for Boolean monadic values, to be read as implication *)
Variant Eimpl (P: Prop): E bool-> Prop :=
  | Eimpl_true: P -> Eimpl P (ret true)
  | Eimpl_false: Eimpl P (ret false)
  | Eimpl_err: forall s, Eimpl P (err s).
Global Hint Constructors Eimpl: core.
Notation "b ~~> P" := (Eimpl P b) (at level 99).
Definition Ebb (x: E bool) := match x with ret b => b | _ => false end.
Lemma EimplV P b: (b ~~> P) <-> (Ebb b -> P).
Proof. split. by case. move: b=>[[]|]; auto. Qed.

Lemma Eimpl_forall {A} b (P: A -> Prop): (forall a, b ~~> P a) <-> (b ~~> forall a, P a).
Proof. setoid_rewrite EimplV. firstorder. Qed.

Lemma Eimpl_impl b (P Q: Prop): (P -> Q) -> (b ~~> P) -> b ~~> Q.
Proof. setoid_rewrite EimplV. auto. Qed.

(** (lazy) logical or/and, considering errors as false, and returning the first error if any *)
Definition Eor (a: E bool) (b: unit -> E bool): E bool :=
  match a with
  | ret false => b tt
  | err s => match b tt with
            | ret true => ret true
            | _ => err s
            end
  | rt => rt
  end.

Definition Eand (a: E bool) (b: unit -> E bool): E bool :=
  match a with
  | ret true => b tt
  | o => o
  end.

Lemma Eimpl_or' a b P: (a ~~> P) -> (b tt ~~> P) -> Eor a b ~~> P.
Proof. case=>//=; auto=>s []=>//=; auto. Qed.

Lemma Eimpl_or a b (P Q: Prop): (a ~~> P) -> (b tt ~~> Q) -> Eor a b ~~> P\/Q.
Proof. intros. apply Eimpl_or'; eauto using Eimpl_impl. Qed.

Lemma Eimpl_and a b (P Q: Prop): (a ~~> P) -> (b tt ~~> Q) -> Eand a b ~~> P/\Q.
Proof. case=>//=?. case=>//=?. auto. Qed.

Lemma Eimpl_and' a b (P Q R: Prop): (a ~~> P) -> (b tt ~~> Q) -> (P -> Q -> R) -> Eand a b ~~> R.
Proof.
  intros???. eapply Eimpl_impl.
  2: apply Eimpl_and; eassumption.
  tauto. 
Qed.


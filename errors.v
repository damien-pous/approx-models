(** * Monad for raising runtime errors *)

Require Import utils.
Require Import String.
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
Infix ">>=" := e_bind (at level 30): error_scope.
Notation "'elet' x := f 'in' g" := (e_bind f (fun x => g)) (at level 200, x binder, right associativity): error_scope.  

Definition e_map {A B} (f: A -> B) (x: E A): E B :=
  x >>= fun a => ret (f a).
Definition e_map2 {A B C} (f: A -> B -> C) (x: E A) (y: E B): E C :=
  x >>= fun a => y >>= fun b => ret (f a b).

Fixpoint emap {A B} (f: A -> E B) (l: list A): E (list B) :=
  match l with
  | nil => ret nil
  | cons x q => elet x := f x in elet q := emap f q in ret (cons x q)
  end.

Definition assert (b: bool) (e: string): E (is_true b) :=
  if b return E (is_true b) then ret eq_refl else err e.


(** lifting predicates to monadic values: errors are left unspecified *)
Variant EP {A} (P: A -> Prop): E A -> Prop :=
| ep_ret: forall a, P a -> EP P (ret a)
| ep_err: forall s, EP P (err s).
Global Hint Constructors EP: core.
Arguments ep_ret {_ _ _}.
Arguments ep_err {_ _ _}.

Lemma EPret {A} (P: A -> Prop) a: EP P (ret a) <-> P a.
Proof. split. now inversion 1. now constructor. Qed.

Definition EP' {A B} (P: A -> B -> Prop): E A -> B -> Prop :=
  fun x b => EP (fun a => P a b) x.
Arguments EP' {_ _} _ _ _ /.
Global Hint Unfold EP': core.

Lemma EP'ret {A B} (P: A -> B -> Prop) a b: EP' P (ret a) b <-> P a b.
Proof. apply (@EPret _ (fun a => P a b)). Qed.

Variant ER {A B} (R: A -> B -> Prop): E A -> E B -> Prop :=
| er_ret a b: R a b -> ER R (ret a) (ret b)
| er_err s: ER R (err s) (err s).
Global Hint Constructors ER: core.
Arguments er_ret {_ _ _ _ _}.
Arguments er_err {_ _ _ _}.

(** helpers for proving lifted predicates *)
Lemma ep_bind {A B} (f: A -> E B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> EP Q (f a)): forall a, EP P a -> EP Q (a >>= f).
Proof. intros ? [??|]; cbn; auto. Qed.

Lemma ep_bind2 {A B C} (f: A -> B -> E C) (P: A -> Prop) (Q: B -> Prop) (R: C -> Prop)
      (F: forall a b, P a -> Q b -> EP R (f a b)): forall a b, EP P a -> EP Q b -> EP R (elet a := a in b >>= f a).
Proof. intros. do 2 (eapply ep_bind; eauto=>*). Qed.

Lemma ep_map {A B} (f: A -> B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> Q (f a)): forall a, EP P a -> EP Q (e_map f a).
Proof. apply ep_bind; constructor; auto. Qed.

Lemma ep_map2 {A B C} (f: A -> B -> C) (P: A -> Prop) (Q: B -> Prop) (R: C -> Prop)
      (F: forall a b, P a -> Q b -> R (f a b)): forall a b, EP P a -> EP Q b -> EP R (e_map2 f a b).
Proof. intros. do 2 (eapply ep_bind; eauto=>*). Qed.

Lemma er_bind {A B C D} (f: A -> E B) (g: C -> E D) (R: A -> C -> Prop) (S: B -> D -> Prop)
      (F: forall a c, R a c -> ER S (f a) (g c)): forall a c, ER R a c -> ER S (a>>=f) (c>>=g).
Proof. destruct 1. now apply F. constructor. Qed.

Lemma er_map {A B C D} (f: A -> B) (g: C -> D) (R: A -> C -> Prop) (S: B -> D -> Prop)
      (F: forall a c, R a c -> S (f a) (g c)): forall a c, ER R a c -> ER S (e_map f a) (e_map g c).
Proof. apply er_bind; auto. Qed.

(** special case for Boolean monadic values, to be read as implication *)
Definition Eimpl: E bool -> Prop -> Prop := EP' (fun P b => wreflect b P).
Arguments Eimpl !_ _.
Global Hint Unfold Eimpl: core.

Lemma EimplE s P: Eimpl (err s) P.
Proof. auto. Qed.
Lemma EimplF P: Eimpl (ret false) P.
Proof. auto. Qed.
Global Hint Resolve EimplE EimplF: core.

Lemma EimplR b P: Eimpl (ret b) P <-> impl b P.
Proof. split. now inversion 1. now constructor. Qed.
Lemma EimplT P: Eimpl (ret true) P <-> P.
Proof. rewrite EimplR. apply implT. Qed.

Lemma Eimpl_forall {A} b P: (forall a: A, Eimpl b (P a)) <-> Eimpl b (forall a, P a).
Proof.
  destruct b as [b|].
  setoid_rewrite EimplR; setoid_rewrite implE. firstorder.
  split; auto. 
Qed.

Lemma Eimpl_impl b (P Q: Prop): (P -> Q) -> Eimpl b P -> Eimpl b Q.
Proof. intros PQ [a H|]; auto; constructor. case H; auto. Qed.

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

Lemma Eimpl_or' a b P: Eimpl a P -> Eimpl (b tt) P -> Eimpl (Eor a b) P.
Proof.
  destruct a as [[|]|]; cbn; auto.
  inversion 2 as [[|] H' E|]; auto.
Qed.

Lemma Eimpl_or a b P Q: Eimpl a P -> Eimpl (b tt) Q -> Eimpl (Eor a b) (P\/Q).
Proof.
  intros. apply Eimpl_or'; eapply Eimpl_impl; try eassumption; tauto. 
Qed.

Lemma Eimpl_and a b P Q: Eimpl a P -> Eimpl (b tt) Q -> Eimpl (Eand a b) (P/\Q).
Proof.
  destruct a as [[|]|]; cbn; auto.
  intro H. rewrite EimplT in H.
  apply Eimpl_impl. now split. 
Qed.

Lemma Eimpl_and' a b (P Q R: Prop): Eimpl a P -> Eimpl (b tt) Q -> (P -> Q -> R) -> Eimpl (Eand a b) R.
Proof.
  intros. eapply Eimpl_impl.
  2: apply Eimpl_and; eassumption.
  cbv; tauto. 
Qed.

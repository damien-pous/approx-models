(** * Monad for raising runtime errors *)

Require Export String.
Set Implicit Arguments.

(** monadic values *)
Inductive E A := ret(a: A) | err(e: string).
Arguments err {_} _.

Declare Scope error_scope.
Bind Scope error_scope with E.
Open Scope error_scope.

(** standard monadic operations *)
Definition e_bind {A B} (x: E A) (f: A -> E B): E B :=
  match x with ret a => f a | err e => err e end.
Infix ">>=" := e_bind (at level 30): error_scope.
Notation "'LET' x ::= f 'IN' g" := (e_bind f (fun x => g)) (at level 200, x binder, right associativity): error_scope.  

Definition e_map {A B} (f: A -> B) (x: E A): E B :=
  x >>= fun a => ret (f a).
Definition e_map2 {A B C} (f: A -> B -> C) (x: E A) (y: E B): E C :=
  x >>= fun a => y >>= fun b => ret (f a b).

Definition assert (b: bool) (e: string): E (is_true b) :=
  if b return E (is_true b) then ret eq_refl else err e.
Notation "'ASSERT' b 'AS' x 'MSG' e 'IN' g" := (e_bind (assert b e) (fun x => g)) (at level 200, x binder, right associativity): error_scope.

Definition trycatch {A} (x: E A) (y: unit -> E A) :=
  match x with err _ => y tt | _ => x end.
Notation "'TRY' x 'CATCH' g" := (trycatch x (fun _ => g)) (at level 200, right associativity): error_scope.  


(** lifting predicates to monadic values: errors are left unspecified *)
Inductive EP {A} (P: A -> Prop): E A -> Prop :=
| ep_ret: forall a, P a -> EP P (ret a)
| ep_err: forall s, EP P (err s).
Global Hint Resolve ep_err: core.

Definition EP' {A B} (P: A -> B -> Prop): E A -> B -> Prop :=
  fun x b => EP (fun a => P a b) x.

(** special case for Boolean monadic values, to be read as implication *)
Definition EPimpl (b: E bool) (P: Prop) := EP (fun b => is_true b -> P) b.

(** helpers for proving lifted predicates *)
Lemma ep_bind {A B} (f: A -> E B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> EP Q (f a)): forall a, EP P a -> EP Q (a >>= f).
Proof. intros ? [??|]; cbn; auto. Qed.

Lemma ep_map {A B} (f: A -> B) (P: A -> Prop) (Q: B -> Prop)
      (F: forall a, P a -> Q (f a)): forall a, EP P a -> EP Q (e_map f a).
Proof. apply ep_bind; constructor; auto. Qed.

Lemma ep_map2 {A B C} (f: A -> B -> C) (P: A -> Prop) (Q: B -> Prop) (R: C -> Prop)
      (F: forall a b, P a -> Q b -> R (f a b)): forall a b, EP P a -> EP Q b -> EP R (e_map2 f a b).
Proof. intros ?? [??|] [??|]; cbn; constructor; auto. Qed.

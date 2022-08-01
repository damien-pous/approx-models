(** * Basic utilities *)

(** some of the functions below are left unspecified, they are only used to implement oracles *)

Require Import FSets.FMapPositive ZArith List.
Require Import ssreflect ssrbool.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * weak reflection: implication from boolean values *)
Variant wreflect (P : Prop): bool -> Prop :=
  | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.
Notation "b ~> P" := (wreflect P b) (at level 99). 
#[export] Hint Constructors wreflect: core.
Lemma implE b P: (b ~> P) <-> (b -> P).
Proof. split. by case. case: b=>//; constructor; auto. Qed.


(** * alternative induction schemes on lists and natural numbers *)
Fixpoint list_ind2 {C: Type} (P: list C -> Prop)
         (P0: P nil) (P1: forall x, P [x]) (P2: forall x y l, P l -> P (x::y::l)) l: P l.
Proof.
  destruct l. apply P0.
  destruct l. apply P1.
  now apply P2, list_ind2.
Qed.

Fixpoint nat_ind2 (P: nat -> Prop)
         (P0: P O) (P1: P 1%nat) (P2: forall n, P n -> P (S (S n))) n: P n.
Proof.
  destruct n. apply P0.
  destruct n. apply P1.
  now apply P2, nat_ind2.
Qed.

Lemma nat2_ind (P: nat -> Prop) :
  P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
  intros ???. cut (forall n, P n /\ P (S n)). firstorder.
  induction n; firstorder.
Qed.

(** * efficient pseudo-fixpoint operator *)
Section powerfix.
  Variables A B: Type.
  Notation Fun := (A -> B).
  Fixpoint powerfix' n (f: Fun -> Fun) (k: Fun): Fun := 
    fun a => match n with O => k a | S n => f (powerfix' n f (powerfix' n f k)) a end.
  Definition powerfix n f k a := f (powerfix' n f k) a.
  (**
    [let f x := Fix (fun f x => body) k]
    is intuitively equivalent to
    [let rec f x := body]
    the continutation [k] is virtually never called (at depth 2^100)
   *)
  Definition Fix := powerfix 100.
End powerfix.


(** * efficient folding functions on [Z] *)
(** Zfold f n a = f 0 (f 1 (... (f (n-1) a)))  *)
Definition Zfold A (f: Z -> A -> A): Z -> A -> A :=
  Fix (fun Zfold z a => if Z.eqb z 0 then a else let z:=Z.pred z in Zfold z (f z a)) f.
(** Zfold' f n a = f 1 (f 2 (... (f n a)))  *)
Definition Zfold' A (f: Z -> A -> A): Z -> A -> A :=
  Fix (fun Zfold z a => if Z.eqb z 0 then a else let z':=Z.pred z in Zfold z' (f z a)) f.

(** * pseudo-arrays, indexed by [Z] *)
Module Zmap.
  Definition t := PositiveMap.t.
  (** empty array *)
  Definition empty {A} := @PositiveMap.empty A.
  (** update a cell *)
  Definition add {A} i (v: A) m :=
    match i with
    | Z0 => PositiveMap.add xH v m
    | Zpos p => PositiveMap.add (Pos.succ p) v m
    | _ => m
    end.
  (** create an array of length [n], initialized using the given function *)
  Definition mk {A} (f: Z -> A) n := Zfold (fun z => add z (f z)) n empty.
  (** retrieve a cell *)
  Definition find {A} m i: option A :=
    match i with
    | Z0 => PositiveMap.find xH m
    | Zpos p => PositiveMap.find (Pos.succ p) m
    | _ => None
    end.
  (** idem, with a default value *)
  Definition get {A} d m i: A := match find m i with Some v => v | None => d end. 
  (** convert the first [n] elements of the array into a list [d] is the default value for uninitialized cells *)
  Definition tolist {A} d n m: list A := Zfold (fun z => cons (get d m z)) n nil.
End Zmap.

(** * linear implementation of List.rev *)
Definition rev {A} (l: list A) := List.rev_append l nil.
Lemma revE {A} (l: list A): rev l = List.rev l.
Proof. symmetry. apply List.rev_alt. Qed.

(** * even predicate *)
Arguments Nat.even !_/: simpl nomatch.
Notation even := Nat.even.
Lemma evenS n: even (S n) = negb (even n).
Proof. by induction n using nat_ind2. Qed.
Lemma even2n n: even (n*2) = true.
Proof. by induction n. Qed.
Lemma even2np1 n: even (n*2+1) = false.
Proof. by induction n. Qed.

(** * elements at even/odd positions in a list *)
Section l.
Context {C: Type}.
Fixpoint evens l: list C :=
  match l with
  | [] => []
  | x::l => x::odds l
  end
with odds l: list C :=
  match l with
  | [] => []
  | x::l => evens l
  end.
End l.
Arguments evens {_} !_/: simpl nomatch.
Arguments odds {_} !_/: simpl nomatch.

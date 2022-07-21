(** * Basic utilities for oracles: pseudo fixpoint operator, arrays on [Z] *)
(** the functions below are left unspecified, they are only used to implement oracles *)

Require Import FSets.FMapPositive ZArith.
Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * weak reflection: implication from boolean values *)
Variant wreflect (P : Prop): bool -> Prop :=
  | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.
Notation impl b P := (wreflect P b). 
#[export] Hint Constructors wreflect: core.
Lemma implE P b: impl b P <-> (b -> P).
Proof. split. by case. case b; constructor; auto. Qed.
Lemma implT P: impl true P <-> P.
Proof. split. by inversion 1. by constructor. Qed.

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

(** * Definition of general polynomial functional operators on Models (monomial basis) 
    to encode polynomial functional equations 
 *)

Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct banach.
Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition M k x := x^k.

(** naive evaluation (defined in vectorspace) *)
Notation eval_ := (eval_ M).
Notation eval := (eval M).

(* Definition of operations on polynomial functional operators *)

Section P_Op.
 Context {N: NBH} {M: Ops0}.
 Notation poly_op := (list M).
 Variable fromN : nat -> M. 
 
 Definition opone: poly_op := [1].
 
 Definition opcst h: poly_op := [h].
 
 Fixpoint Xk (k: nat): poly_op :=
   match k with
   | O => [1]
   | S k => 0::Xk k
   end.
  
 (** multiplication *)
 Fixpoint opmul (P Q: poly_op): poly_op :=
   match P with
   | [] => []
   | h::P => sadd (sscal h Q) (0::opmul P Q)
   end.

 (** identity (X) *)
 Definition opid: poly_op := [0;1].
 
 (** composition *)
 Fixpoint opcomp (P Q: poly_op): poly_op :=
   match P with
   | [] => []
   | h::P => sadd (opcst h) (opmul (opcomp P Q) Q)
   end.

 (** derivation on poly_opnoms (equals to the differential of the operator) *)
 Fixpoint opderive_ n (P : poly_op) : poly_op :=
   match P with
   | [] => []
   | h::Q => (mul (fromN n) h)::(opderive_ (n .+1) Q)
   end.

 Definition opderive P : poly_op :=
   match P with
   | [] => []
   | h0::Q => opderive_ 1 Q
   end.

 (** linear time evaluation (Hörner) *)
 Fixpoint opeval (P:list M) (s: M) : M :=
   match P with
   | [] => 0
   | h::Q => add h (mul s (opeval Q s))
   end.
   
End P_Op.


Section e.
 Context { A : Type } { C : Ops0 }.
 Notation Fun := (A -> C).

 Fixpoint direct_eval (P :list Fun) (s : Fun) (t:A) : C :=
   match P with
   | [] => 0
   | h::Q => h t + ( s t * direct_eval Q s t)
   end.

End e.


Lemma opeval_direct_eval (P : list (R -> R)) s (t :R) : (opeval P s) t = direct_eval P s t.
Admitted. 

Section TubePolyn.
Variable (D : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).


Lemma newton ( F : list (R -> R)) (phi A : R -> R) (d lambda0 lambda1 r eta : R) :
  let lambda := lambda0 + eta*lambda1 in
  (forall t, D t -> Rabs (1 - A t * direct_eval (opderive F) phi t) <= lambda0 ) ->
  (forall t, D t -> Rabs ( A t ) <= eta ) ->
  (forall (s : R->R), (forall t, D t -> Rabs (s t - phi t) <= r) ->
                      (forall t, D t -> Rabs ( direct_eval (opderive F) phi t - direct_eval (opderive F) s t ) <= lambda1)) ->
  (forall t, D t -> Rabs ( A t * direct_eval F phi t ) <= d) ->
  0 <= lambda /\ lambda < 1 /\ d + lambda * r <= r ->
  ( forall t, D t  -> direct_eval F phi t <= d / (1 - lambda)).


End TubePolyn.

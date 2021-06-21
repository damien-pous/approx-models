(** * Definition of general polynomial functional operators on Models (monomial basis) 
    to encode polynomial functional equations 
 *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Definition of operations on polynomial functional operators *)

Section P_Op.
 Context {N: NBH} {M: ModelOps}.
 Notation poly_op := (list M).

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
   | h::Q => (mul (mcst (fromN n)) h)::(opderive_ (n .+1) Q)
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

Section Newton_Op.
 Context {N: NBH} {M: ModelOps}.
 Notation poly_op := (list M).
 Parameter n : Z.

 Definition inv_DF (P : poly_op) (s0 : M)  :=
   mdiv n 1 (opeval (opderive P) s0).
 

 Definition newton_op (P : poly_op) (s0 : M) : E poly_op :=
   let EA := inv_DF P s0 in
   match EA with
   | ret A => ret (ssub opid (sscal A P))
   | err x => err x
   end.
        
End Newton_Op.

Section e.
 Context { A : Type } { C : Ops0 }.
 Notation Fun := (A -> C).

 Fixpoint direct_eval (P :list Fun) (s : Fun) (t:A) : C :=
   match P with
   | [] => 0
   | h::Q => h t + ( s t * direct_eval Q s t)
   end.

End e.

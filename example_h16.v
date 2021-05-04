(** * Example 2: evaluation of Abelian integrals related to Hilbert's 16th problem  *)

Require Import approx rescale intervals errors.
Require chebyshev.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.
 Context {NN: NBH}.
 Variables (rp rq: Z) (N: nat).

 Let N' := Z.of_nat N.
 Let r: II := fromZ rp / fromZ rq.
 Let x0: II := fromZ 9 / fromZ 10.
 Let y0: II := fromZ 11 / fromZ 10.
 Let sqrt2: II := sqrt (fromZ 2). 
 Let r2: II := r*r. 
 Let r_sqrt2: II := r / sqrt2.
 Let xmin: II := sqrt (x0 - r_sqrt2).
 Let xmax: II := sqrt (x0 + r_sqrt2).
 Let ymin: II := sqrt (y0 - r_sqrt2).
 Let ymax: II := sqrt (y0 + r_sqrt2).

 Let Fx := approx.model_ops (chebyshev.basis_ops xmin xmax).
 Let Fy := approx.model_ops (chebyshev.basis_ops ymin ymax).
 
 Let sqrx (f: Fx): Fx := mtruncate N (f * f).
 Let sqry (f: Fy): Fy := mtruncate N (f * f).
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => mtruncate N (f*sqrx f) | 4 => sqrx (sqrx f) | _ => 1 end.
 Infix "^x" := powx (at level 30).
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => mtruncate N (f*sqry f) | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^y" := powy (at level 30).
 Definition calcul :=
   LET deltay ::= msqrt N' (mcst r2 - sqrx (sqrx mid - mcst x0)) IN
   LET deltax ::= msqrt N' (mcst r2 - sqry (sqry mid - mcst y0)) IN
   LET ydown ::= msqrt N' (mcst y0 - deltay) IN
   LET yup ::= msqrt N' (mcst y0 + deltay) IN
   LET yupdown ::= 
     LET a ::= mdiv N' 1 yup IN
     LET b ::= mdiv N' 1 ydown IN
     ret (a-b)
   IN
   LET xleft ::= msqrt N' (mcst x0 - deltax) IN
   LET xright ::= msqrt N' (mcst x0 + deltax) IN
   LET xleftright ::=
     LET a ::= mdiv N' 1 (xleft * deltax) IN
     LET b ::= mdiv N' 1 (xright * deltax) IN
     ret (a+b)
   IN
   let integrand1 (i j : nat) :=
       match j with
       | 0 => mid ^x i * yupdown
       | S j' => mid ^x i * (yup ^x j' - ydown ^x j')
       end
   in
   let integrand2 (i j : nat) :=
       match i with
       | 0 => ret (xleftright * (mid ^y j * (mid ^y 2 - mcst y0)))
       | S i' => mdiv N' ((xleft ^y i' + xright ^y i') * mid ^y j * (mid ^y 2 - mcst y0)) deltax
       end
   in
   let Integral1 (i j : nat) := mintegrate (integrand1 i j) None None in
   let Integral2 (i j : nat) := LET fy ::= integrand2 i j IN mintegrate fy None None in
   let Integral i j := LET a ::= Integral1 i j IN LET b ::= Integral2 i j IN ret (a+b) in
   (LET I00 ::= Integral 0 0 IN
    LET I20 ::= Integral 2 0 IN
    LET I22 ::= Integral 2 2 IN
    LET I40 ::= Integral 4 0 IN
    LET I04 ::= Integral 0 4 IN
    ret (I00, I20, I22, I40, I04))%nat.
   
End s.
Arguments calcul: clear implicits.

(* TOCHECK *)

Time Eval vm_compute in     calcul       _       5  10  13.

(* first one is always slow: native_compute must initialise *)
Time Eval native_compute in calcul       _       5  10  13.
Time Eval native_compute in calcul       _       5  10  13.
Time Eval native_compute in calcul       _      78 100  15.

(* quite slower with IBigInt... *)
Time Eval native_compute in @calcul IBigInt.nbh 78 100  15.

From Interval Require Import Specific_bigint Specific_ops.
Import BigZ.

Module FBigInt128 <: FloatOpsP.
  Include SpecificFloat BigIntRadix2.
  Definition p := 128%bigZ.
End FBigInt128. 
Module IBigInt128 := Make FBigInt128.

Module FBigInt300 <: FloatOpsP.
  Include SpecificFloat BigIntRadix2.
  Definition p := 300%bigZ.
End FBigInt300. 
Module IBigInt300 := Make FBigInt300.

(* TOCHECK: looks ok now! (but pretty slow and thus commented out) *)
(*
Time Eval native_compute in calcul IBigInt128.nbh 88   100  65.
Time Eval native_compute in calcul IBigInt128.nbh 89   100  95.
Time Eval native_compute in calcul IBigInt300.nbh 895 1000 135.
*)

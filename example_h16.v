(** * Example 2: evaluation of Abelian integrals related to Hilbert's 16th problem  *)

Require Import approx rescale intervals errors.
Require chebyshev.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.
 Variables rp rq: Z.
 Let r {C: Ops1}: C := fromZ rp / fromZ rq.
 Variable N: nat.
 Let N' := Z.of_nat N.
 
 Section t.
 Context {C: Ops1} {Fx: FunOps C} {Fy: FunOps C}.
 Let x0: C := fromZ 9 / fromZ 10.
 Let y0: C := fromZ 11 / fromZ 10.
 Let sqrt2: C := sqrt (1+1). 
 Let r2: C := r*r. 
 Let r_sqrt2: C := r / sqrt2.
 Let xmin: C := sqrt (x0 - r_sqrt2).
 Let xmax: C := sqrt (x0 + r_sqrt2).
 Let ymin: C := sqrt (y0 - r_sqrt2).
 Let ymax: C := sqrt (y0 + r_sqrt2).
 (* sligthly larger domains *)
 Definition xmin' := xmin-1/fromZ 100.
 Definition xmax' := xmax+1/fromZ 100.
 Definition ymin' := ymin-1/fromZ 100.
 Definition ymax' := ymax+1/fromZ 100.
 Let sqrx (f: Fx): Fx := mtruncate N (f * f).
 Let sqry (f: Fy): Fy := mtruncate N (f * f).
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => mtruncate N (f*sqrx f) | 4 => sqrx (sqrx f) | _ => 1 end.
 Infix "^x" := powx (at level 30).
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => mtruncate N (f*sqry f) | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^y" := powy (at level 30).
 Definition Integrals :=
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
   let Integral1 (i j : nat) := mintegrate (integrand1 i j) xmin xmax in
   let Integral2 (i j : nat) := LET fy ::= integrand2 i j IN mintegrate fy ymin ymax in
   let Integral i j := LET a ::= Integral1 i j IN LET b ::= Integral2 i j IN ret (a+b) in
   (LET I00 ::= Integral 0 0 IN
    LET I20 ::= Integral 2 0 IN
    LET I22 ::= Integral 2 2 IN
    LET I40 ::= Integral 4 0 IN
    LET I04 ::= Integral 0 4 IN
    ret (I00, I20, I22, I40, I04))%nat.
 End t.


 (* TODO: improve definition of domains... *)
 Definition parametric (a: forall {C: Ops1}, C) := forall (R S : Ops1) (T : Rel1 R S), T a a. 
  
 Lemma check_lt (a b: forall {C: Ops1}, C) (ra: parametric (@a)) (rb: parametric (@b))
       (E: is_lt a b): a<b.
 Proof. revert E. case is_ltE=>//. intros H _. apply H. apply ra. apply rb. Qed.

 Definition D (a b: forall {C: Ops1}, C)
            (ra: parametric (@a)) (rb: parametric (@b)) (E: is_lt a b): Domain :=
   {|rdlo:=ra;rdhi:=rb;dlohi:=check_lt ra rb E|}.

 Lemma rr: parametric (@r). 
 Proof. unfold parametric, r. rel. Qed.
 Hint Resolve rr: rel. 

 Hypothesis Hx: is_lt xmin' xmax'. 
 Let Dx: Domain.
 apply D with @xmin' @xmax'.
 abstract (unfold parametric,xmin'; rel). 
 abstract (unfold parametric,xmax'; rel). 
 exact Hx.
 Defined.

 Hypothesis Hy: is_lt ymin' ymax'. 
 Let Dy: Domain.
 apply D with @ymin' @ymax'.
 abstract (unfold parametric,ymin'; rel). 
 abstract (unfold parametric,ymax'; rel). 
 exact Hy. 
 Defined.

 Let Bx := rescale Dx chebyshev.basis.
 Let By := rescale Dy chebyshev.basis.
 
 Definition calcul {N: NBH} := @Integrals II (MFunOps Bx) (MFunOps By).
   
End s.

(* DAMIEN: below, we used to play with the precision (commented column)
   no longer as obvious to do with the neighborhood instances provided in intervals.v
   the first ones, using IPrimitive.nbh / IBigInt.nbh are not with 63/64 bits now
 *)

(* TOCHECK *)

Time Eval vm_compute in @calcul         5      10  13 (*  32 *) eq_refl eq_refl Iprimitive.nbh.

(* first one is always slow: native_compute must initialise *)
Time Eval native_compute in @calcul  5      10  13 (*  32 *) eq_refl eq_refl Iprimitive.nbh.
Time Eval native_compute in @calcul  5      10  13 (*  32 *) eq_refl eq_refl Iprimitive.nbh.
Time Eval native_compute in @calcul 78     100  15 (*  32 *) eq_refl eq_refl Iprimitive.nbh.

(* quite slower with IBigInt... *)
Time Eval native_compute in @calcul 78     100  15 (*  32 *) eq_refl eq_refl IBigInt.nbh.

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

(* TOCHECK: we obtain very large intervals... *)
Time Eval native_compute in @calcul 88     100  65 (* 128 *) eq_refl eq_refl IBigInt128.nbh.
Time Eval native_compute in @calcul 89     100  95 (* 128 *) eq_refl eq_refl IBigInt128.nbh.
Time Eval native_compute in @calcul 895   1000 135 (* 300 *) eq_refl eq_refl IBigInt300.nbh.

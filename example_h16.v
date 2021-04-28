(** * Example 2: evaluation of Abelian integrals related to Hilbert's 16th problem  *)

Require Import approx rescale intervals.
Require chebyshev.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope RO_scope.

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
 Definition xmin: C := sqrt (x0 - r_sqrt2).
 Definition xmax: C := sqrt (x0 + r_sqrt2).
 Definition ymin: C := sqrt (y0 - r_sqrt2).
 Definition ymax: C := sqrt (y0 + r_sqrt2).
 (* sligthly larger domains *)
 Definition xmin' := xmin-1/fromZ 100.
 Definition xmax' := xmax+1/fromZ 100.
 Definition ymin' := ymin-1/fromZ 100.
 Definition ymax' := ymax+1/fromZ 100.
 Let sqrx (f: Fx): Fx := mtruncate N (f * f).
 Let sqry (f: Fy): Fy := mtruncate N (f * f).
 Let deltay: E Fx := msqrt N' (mcst r2 - sqrx (sqrx mid - mcst x0)).
 Let deltax: E Fy := msqrt N' (mcst r2 - sqry (sqry mid - mcst y0)).
 Let ydown: E Fx := deltay >>= fun deltay => msqrt N' (mcst y0 - deltay).
 Let yup: E Fx := deltay >>= fun deltay => msqrt N' (mcst y0 + deltay).
 Let yupdown: E Fx :=
   ydown >>= fun ydown =>
               yup >>= fun yup =>
                         mdiv N' 1 yup >>= fun a =>
                                             mdiv N' 1 ydown >>= fun b => ret (a-b).
 Let xleft: E Fy := deltax >>= fun deltax => msqrt N' (mcst x0 - deltax).
 Let xright: E Fy := deltax >>= fun deltax => msqrt N' (mcst x0 + deltax).
 Let xleftright: E Fy :=
   deltax >>= fun deltax =>
   xleft >>= fun xleft =>  
   xright >>= fun xright =>  
   mdiv N' 1 (xleft * deltax) >>= fun a =>
   mdiv N' 1 (xright * deltax) >>= fun b => 
   ret (a+b).
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => mtruncate N (f*sqrx f) | 4 => sqrx (sqrx f) | _ => 1 end.
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => mtruncate N (f*sqry f) | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^" := powx.
 Let integrand1 (i j : nat): E Fx :=
   match j with
   | 0 => yupdown >>= fun yupdown => ret (mid ^ i * yupdown)
   | S j' => yup >>= fun yup => ydown >>= fun ydown => ret (mid ^ i * (yup ^ j' - ydown ^ j'))
   end.
 Infix "^" := powy.
 Let integrand2 (i j : nat): E Fy :=
   match i with
   | 0 => xleftright >>= fun xleftright => ret (xleftright * (mid ^ j * (mid ^ 2 - mcst y0)))
   | S i' => xleft >>= fun xleft =>
             xright >>= fun xright =>
             deltax >>= mdiv N' ((xleft ^ i' + xright ^ i') * mid ^ j * (mid ^ 2 - mcst y0))
   end.
 Let Integral1 (i j : nat) := integrand1 i j >>= fun fx => mintegrate fx xmin xmax.
 Let Integral2 (i j : nat) := integrand2 i j >>= fun fy => mintegrate fy ymin ymax.
 Let Integral i j := Integral1 i j >>= fun a => Integral2 i j >>= fun b => ret (a+b).
 Definition integrands1 :=
   (integrand1 0 0,
    integrand1 2 0,
    integrand1 2 2,
    integrand1 4 0,
    integrand1 0 4).
 Definition integrands2 :=
   (integrand2 0 0,
    integrand2 2 0,
    integrand2 2 2,
    integrand2 4 0,
    integrand2 0 4).
 Definition TotalIntegral :=
   (Integral 0 0,
    Integral 2 0,
    Integral 2 2,
    Integral 4 0,
    Integral 0 4).
 End t.

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
 abstract (unfold parametric,xmin',xmin; rel). 
 abstract (unfold parametric,xmax',xmax; rel). 
 exact Hx.
 Defined.

 Hypothesis Hy: is_lt ymin' ymax'. 
 Let Dy: Domain.
 apply D with @ymin' @ymax'.
 abstract (unfold parametric,ymin',ymin; rel). 
 abstract (unfold parametric,ymax',ymax; rel). 
 exact Hy. 
 Defined.

 Let Bx := rescale Dx chebyshev.basis.
 Let By := rescale Dy chebyshev.basis.

 Definition intermediate1 {N: NBH} := 
   let '(a,b,c,d,e) := @integrands1 II (MFunOps Bx)
   in (a, b, c, d, e).

 Definition intermediate2 {N: NBH} := 
   let '(a,b,c,d,e) := @integrands2 II (MFunOps By)
   in (a, b, c, d, e).
 
 Definition calcul {N: NBH} :=
   let '(a,b,c,d,e) := @TotalIntegral II (MFunOps Bx) (MFunOps By)
   in (a, b, c, d, e).
   
End s.

(* DAMIEN: below, we used to play with the precision (commented column)
   no longer as obvious to do with the neighborhood instances provided in intervals.v
   the first ones, using IPrimitive.nbh / IBigInt.nbh are not with 63/64 bits now
 *)

(* TOCHECK *)

Time Eval vm_compute in @intermediate1  5      10  13 (*  32 *) eq_refl Iprimitive.nbh.
Time Eval vm_compute in @intermediate2  5      10  13 (*  32 *) eq_refl Iprimitive.nbh.
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

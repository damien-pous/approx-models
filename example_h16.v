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
 Definition xmin' := xmin-1.
 Definition xmax' := xmax+1.
 Definition ymin' := ymin-1.
 Definition ymax' := ymax+1.
 Let sqrx (f: Fx): Fx := mtruncate N (f * f).
 Let sqry (f: Fy): Fy := mtruncate N (f * f).
 Let deltay: Fx := msqrt N' (mcst r2 - sqrx (sqrx mid - mcst x0)).
 Let deltax: Fy := msqrt N' (mcst r2 - sqry (sqry mid - mcst y0)).
 Let ydown: Fx := msqrt N' (mcst y0 - deltay).
 Let yup: Fx := msqrt N' (mcst y0 + deltay).
 Let yupdown: Fx := mdiv N' 1 yup - mdiv N' 1 ydown.
 Let xleft: Fy := msqrt N' (mcst x0 - deltax).
 Let xright: Fy := msqrt N' (mcst x0 + deltax).
 Let xleftright: Fy := mdiv N' 1 (xleft * deltax) + mdiv N' 1 (xright * deltax).
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => mtruncate N (f*sqrx f) | 4 => sqrx (sqrx f) | _ => 1 end.
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => mtruncate N (f*sqry f) | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^" := powx.
 Let integrand1 (i j : nat): Fx :=
   match j with
   | 0 => mid ^ i * yupdown
   | S j' => mid ^ i * (yup ^ j' - ydown ^ j')
   end.
 Infix "^" := powy.
 Let integrand2 (i j : nat): Fy :=
   match i with
   | 0 => xleftright * (mid ^ j * (mid ^ 2 - mcst y0))
   | S i' => mdiv N' ((xleft ^ i' + xright ^ i') * mid ^ j * (mid ^ 2 - mcst y0)) deltax
   end.
 Let Integral1 (i j : nat) := mintegrate (integrand1 i j) xmin xmax.
 Let Integral2 (i j : nat) := mintegrate (integrand2 i j) ymin ymax.
 Let Integral i j := Integral1 i j + Integral2 i j.
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

 Definition calcul {N: NBH} :=
   let '(a,b,c,d,e) := @TotalIntegral II (MFunOps Bx) (MFunOps By)
   in (width a, width b, width c, width d, width e).
   
End s.

(* DAMIEN: below, we used to play with the precision (commented column)
   no longer as obvious to do with the neighborhood instances provided in intervals.v
   the first ones, using IPrimitive.nbh / IBigInt.nbh are not with 63/64 bits now
 *)

(* TOCHECK: seems to be broken now, we always get [nan]
   I guess this is because now we do check that arguments of evaluations and bounds of integrals belong to the domain. Possibly these checks fail because the example is wrong...
 *)

(* first one is always slow: native_compute must initialise *)
Time Eval native_compute in (fun Hx Hy => @calcul  5      10  13 (*  32 *) Hx Hy Iprimitive.nbh).
Time Eval native_compute in (fun Hx Hy => @calcul  5      10  13 (*  32 *) Hx Hy Iprimitive.nbh).
Time Eval native_compute in (fun Hx Hy => @calcul 78     100  15 (*  32 *) Hx Hy Iprimitive.nbh).

(* quite slower with IBigInt... *)
Time Eval native_compute in (fun Hx Hy => @calcul 78     100  15 (*  32 *) Hx Hy IBigInt.nbh).

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

(* TOCHECK: rather heavy and thus commented out *)
Time Eval native_compute in (fun Hx Hy => @calcul 88     100  65 (* 128 *) Hx Hy IBigInt128.nbh).
Time Eval native_compute in (fun Hx Hy => @calcul 89     100  95 (* 128 *) Hx Hy IBigInt128.nbh).
Time Eval native_compute in (fun Hx Hy => @calcul 895   1000 135 (* 300 *) Hx Hy IBigInt300.nbh).

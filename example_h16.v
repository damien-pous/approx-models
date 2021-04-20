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
 Let sqrx (f: Fx): Fx := truncate N (f * f).
 Let sqry (f: Fy): Fy := truncate N (f * f).
 Let deltay: Fx := sqrt' N' (cst r2 - sqrx (sqrx id - cst x0)).
 Let deltax: Fy := sqrt' N' (cst r2 - sqry (sqry id - cst y0)).
 Let ydown: Fx := sqrt' N' (cst y0 - deltay).
 Let yup: Fx := sqrt' N' (cst y0 + deltay).
 Let yupdown: Fx := div' N' 1 yup - div' N' 1 ydown.
 Let xleft: Fy := sqrt' N' (cst x0 - deltax).
 Let xright: Fy := sqrt' N' (cst x0 + deltax).
 Let xleftright: Fy := div' N' 1 (xleft * deltax) + div' N' 1 (xright * deltax).
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => truncate N (f*sqrx f) | 4 => sqrx (sqrx f) | _ => 1 end.
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => truncate N (f*sqry f) | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^" := powx.
 Let integrand1 (i j : nat): Fx :=
   match j with
   | 0 => id ^ i * yupdown
   | S j' => id ^ i * (yup ^ j' - ydown ^ j')
   end.
 Infix "^" := powy.
 Let integrand2 (i j : nat): Fy :=
   match i with
   | 0 => xleftright * (id ^ j * (id ^ 2 - cst y0))
   | S i' => div' N' ((xleft ^ i' + xright ^ i') * id ^ j * (id ^ 2 - cst y0)) deltax
   end.
 Let Integral1 (i j : nat) := integrate (integrand1 i j) xmin xmax.
 Let Integral2 (i j : nat) := integrate (integrand2 i j) ymin ymax.
 Let Integral i j := Integral1 i j + Integral2 i j.
 Definition TotalIntegral :=
   (Integral 0 0,
    Integral 2 0,
    Integral 2 2,
    Integral 4 0,
    Integral 0 4).
 End t.
 
 Variable p: BigZ.BigZ.t.
 Let INBH := INBH p.
 Existing Instance INBH. 

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

 Hypothesis Hx: is_lt xmin xmax. 
 Let Dx: Domain.
 apply D with @xmin @xmax.
 abstract (unfold parametric,xmin; rel). 
 abstract (unfold parametric,xmax; rel). 
 exact Hx.
 Defined.

 Hypothesis Hy: is_lt ymin ymax. 
 Let Dy: Domain.
 apply D with @ymin @ymax.
 abstract (unfold parametric,ymin; rel). 
 abstract (unfold parametric,ymax; rel). 
 exact Hy. 
 Defined.

 Let Bx := rescale Dx chebyshev.basis.
 Let By := rescale Dy chebyshev.basis.

 Definition err (x: II): FF :=
   match x with
   | Float.Ibnd a b => b-a
   | _ => F.nan
   end.

 Definition calcul :=
   let '(a,b,c,d,e) := @TotalIntegral II (MFunOps INBH Bx) (MFunOps INBH By)
   in (err a, err b, err c, err d, err e).
   
End s.

Open Scope bigZ_scope.
(* first one is always slow: native_compute mus initialise *)
(*
Time Eval native_compute in (fun Hx Hy => @calcul  5      10  13  32 Hx Hy).
Time Eval native_compute in (fun Hx Hy => @calcul  5      10  13  32 Hx Hy).
Time Eval native_compute in (fun Hx Hy => @calcul 78     100  15  32 Hx Hy).
Time Eval native_compute in (fun Hx Hy => @calcul 88     100  65 128 Hx Hy).
Time Eval native_compute in (fun Hx Hy => @calcul 89     100  95 128 Hx Hy).
Time Eval native_compute in (fun Hx Hy => @calcul 895   1000 135 300 Hx Hy).
*)

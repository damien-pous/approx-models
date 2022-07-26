(** * Example 2: evaluation of Abelian integrals related to Hilbert's 16th problem  *)

Require Import approx rescale intervals.
Require chebyshev.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.
 (** [NN] is an arbitrary neighborhood, i.e., an abstract machine for computing with intervals *)
 Context {NN: NBH}.
 (** [r_] is a parameter for the considered computations *)
 Variable r_: Q.
 (** [N] is the interpolation degree for divisions/square roots 
     [T] is the truncation degree for multiplications 
     (in other words, the maximal degree for the considered approximations)
  *)
 Variable N: Z.
 Variable T: option nat.

 Let r: II := fromQ r_.
 Let x0: II := fromQ 0.9.
 Let y0: II := fromQ 1.1.
 Let sqrt2: II := sqrt (fromZ 2). 
 Let r2: II := r*r. 
 Let r_sqrt2: II := r / sqrt2.
 Let xmin: II := sqrt (x0 - r_sqrt2).
 Let xmax: II := sqrt (x0 + r_sqrt2).
 Let ymin: II := sqrt (y0 - r_sqrt2).
 Let ymax: II := sqrt (y0 + r_sqrt2).

 (** we use two instances of the Chebyshev basis: on [[xmin;xmax]], and on [[ymin;ymax]] *)
 Let Fx := approx.model_ops (chebyshev.basis_ops xmin xmax).
 Let Fy := approx.model_ops (chebyshev.basis_ops ymin ymax).
 
 Let sqrx (f: Fx): Fx := f *[.T] f.
 Let sqry (f: Fy): Fy := f *[.T] f.
 Let powx f n: Fx := match n with 1 => f | 2 => sqrx f | 3 => f*[.T]sqrx f | 4 => sqrx (sqrx f) | _ => 1 end.
 Infix "^x" := powx (at level 30).
 Let powy f n: Fy := match n with 1 => f | 2 => sqry f | 3 => f*[.T]sqry f | 4 => sqry (sqry f) | _ => 1 end.
 Infix "^y" := powy (at level 30).
 
 (** the considered integrals, in monadic style for dealing with potential runtime errors *)
 Definition calcul :=
   LET midx ::= mid IN
   LET midy ::= mid IN
   LET deltay ::= msqrt N T (mcst r2 - sqrx (sqrx midx - mcst x0)) IN
   LET deltax ::= msqrt N T (mcst r2 - sqry (sqry midy - mcst y0)) IN
   LET ydown ::= msqrt N T (mcst y0 - deltay) IN
   LET yup ::= msqrt N T (mcst y0 + deltay) IN
   LET yupdown ::= 
     LET a ::= mdiv N T 1 yup IN
     LET b ::= mdiv N T 1 ydown IN
     ret (a-b)
   IN
   LET xleft ::= msqrt N T (mcst x0 - deltax) IN
   LET xright ::= msqrt N T (mcst x0 + deltax) IN
   LET xleftright ::=
     LET a ::= mdiv N T 1 (xleft *[.T] deltax) IN
     LET b ::= mdiv N T 1 (xright *[.T] deltax) IN
     ret (a+b)
   IN
   let integrand1 (i j : nat) :=
       match j with
       | 0 => midx ^x i * yupdown
       | S j' => midx ^x i * (yup ^x j' - ydown ^x j')
       end
   in
   let integrand2 (i j : nat) :=
       match i with
       | 0 => ret (xleftright * (midy ^y j * (midy ^y 2 - mcst y0)))
       | S i' => mdiv N T ((xleft ^y i' + xright ^y i') *[.T] midy ^y j *[.T] (midy ^y 2 - mcst y0)) deltax
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

(** computations with the virtual machine *)
Time Eval vm_compute in     calcul       _       0.5  13 (Some 13%nat).

(** computations with native runtime
   first call is always slow: native_compute must initialise *)
Time Eval native_compute in calcul       _       0.5  13 (Some 13%nat).
Time Eval native_compute in calcul       _       0.5  13 (Some 13%nat).
Time Eval native_compute in calcul       _       0.78 15 (Some 15%nat).

(** by default, native floating point numbers are used
    by specifying the first argument, we may chose other options *)
(** here with emulated floating point numbers, based on BigInts (big numbers based on 63bit native integers) 
    -> quite slower *)
Time Eval native_compute in @calcul IBigInt60.nbh  0.5 8 (Some 8%nat).
(** or with emulated floating point numbers, based on emulated relative numbers 
    -> even slower *)
Time Eval native_compute in @calcul IStdZ60.nbh  0.5 8 (Some 8%nat).


(** more precise computations, but pretty slow and thus commented out *)
(**
Time Eval native_compute in calcul IBigInt120.nbh 0.88   65 (Some 100%nat). (* 8s *)
Time Eval native_compute in calcul IBigInt120.nbh 0.89   95 (Some 100%nat). (* 14s *)
Time Eval native_compute in calcul IBigInt300.nbh 0.895 135 (Some 150%nat). (* 83s *)
*)

(* Example of a polynomial equation resolution *)

Require Import interfaces.
Require Import vectorspace.
Require Import taylor fourier approx.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*TODO : Factorise with interpolation section in fourier.v *)

Section i.

  Context {C: Ops1} {B: BasisOps_on C}. 
  Notation Fun := (C -> C).
  Notation poly := (list Fun).
  Variable n: Z.

  Definition newton_method (N:Z) (f : Fun) (f' : Fun) (u0: C) :=
    Zfold (fun _ u=> u - (f u)/(f' u)) N u0.

  
  Definition oval_approx (F: poly) (N:Z) (s0 : Fun) :=
    let f := (fun t => newton_method N (eval' (apply F t)) (eval' (apply (derive F) t)) (s0 t)) in
    interpolate n f.
  
End i.


 

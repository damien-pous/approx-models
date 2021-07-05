(* Example of a polynomial equation resolution *)

Require Import interfaces.
Require Import vectorspace approx.
Require Import taylor chebyshev.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section i.
  Context {nbh: NBH} {BO: BasisOps}.
  Notation Tube := (Tube (car (ops0 (@II nbh)))).
(*  Context {C: Ops1} {B: BasisOps_on C}. 
  Notation Fun := (C -> C).
  Notation poly := (list Fun).*)
  Variable n: Z.

  Definition newton_method (N:Z) (f f' : list FF)  u0 :=
    Zfold (fun _ u=> u - (taylor.eval' f u)/(taylor.eval' f' u)) N u0.

  
  Definition solution_approx (F: list Tube) (N:Z) (s0 : Tube) :=
    let p0 := mcf s0 in
    let Fp := map (fun f => mcf f) F in
    let f := (fun t => let P := map (fun f=> beval f t) Fp in
                 newton_method N P (derive P) (beval p0 t)) in
    mfc (interpolate n f).
  
End i.

Require Import intervals.

Section test.
 
  Let C :=intervals.FOps1.
  Let Bc := basis11_ops.
  Let nbh := IPrimFloat.nbh.
  Let Bt := taylor.basis_ops (fromZ (-1)) (fromZ 1).
  Definition a0: list C := sopp (sadd pone (pmul pid pid)).
  Eval compute in a0.
  Definition A0  := mfc a0.
  
  Definition F := A0::(mfc [0])::(mfc pone)::[].
  Eval compute in F.
  Definition s0 := mfc pone.
  Definition Pf := @taylor.eval' (@approx.MOps0 nbh Bt) F s0.
  Eval compute in Pf.
  Eval compute in @mrange nbh (model_ops Bc) Pf.

  Definition s := @solution_approx nbh Bc 100 F 10 s0.
  (*Eval compute in s.*)
  Definition Pf' := @taylor.eval' (@approx.MOps0 nbh Bt) F s.
  (*Eval compute in Pf'.*)
  Eval compute in @mrange nbh (model_ops Bc) Pf'.
  (* We get [[-0.046307697537852952; 0.00365240036736261]] *)

  (*
  Definition s' := @solution_approx nbh Bc 100 F 10 (@mtruncate nbh (model_ops Bc) 20 s).
  Definition Pf'' := @taylor.eval' (@approx.MOps0 nbh Bt) F s'.
  Eval compute in @mrange nbh (model_ops Bc) Pf''.
 *)


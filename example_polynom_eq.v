(** * examples of polynomial functional equation resolution *)

Require Import interfaces.
Require Import vectorspace taylor approx.
Require Import utils intervals String.
Require fourier chebyshev.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance IPrimFloat.nbh.

Module sqrt_cheb.
  
  (** * a square root as a solution of a polynomial functional equations

        F(phi) = - (1 + X^2 / 10) + phi^2
        F(phi) = 0  <->   phi(X) = sqrt (1 + X^2 / 10)
   *)
  
  (** Chebyshev basis by default for models *)
  Import chebyshev.
  Local Existing Instance basis11_ops.
  Notation Model := (@model_ops IPrimFloat.nbh basis11_ops).

  (** polynomial equation *)
  (* TOTHINK: we use the operations on polynomials in Chebyshev basis directly (pid, multiplication):
     building a model directly would require us to use monadic style: [mid] may raise exceptions...
   *)
  Definition a0 : Model := mfc (sopp (1 + (sscal (fromQ 0.1) (pid*pid)))).
  Definition F : list Model := [a0; 0; 1].
  Eval compute in F.

  (** (bad) candidate solution *)
  Definition phi0 : Model := 1. 

  Definition Fphi0 := taylor.eval' F phi0.
  Eval compute in Fphi0.
  Eval compute in mrange Fphi0.

  (** ** automatic computation of a certified solution 
     (degree: 60, Newton iterations: 20, recursion depth for finding radius: 10, maximal radius: 1)
   *)
  Definition valid_s : E Model :=
    mpolynom_eq 60 20 5 1 F phi0.
  Eval vm_compute in valid_s.


  (** ** manual computation *)
  
  (** refined solution, via the oracle (degree: 5, Newton iterations: 10) *)
  Definition phi := polynom_eq_oracle 5 10 F phi0.
  Eval vm_compute in phi.
  
  Definition Fphi := taylor.eval' F phi.
  Eval vm_compute in Fphi.
  Eval vm_compute in mrange Fphi. 

  (** manual validation of this refined solution (d is the degree for the contracting operator) *)
  Definition valid_aux_s d : E Model :=
    let DF := mcf (eval' (taylor.derive F) phi) in
    let A := mfc (interpolate d (fun x => 1 / eval' DF x)) in
    mpolynom_eq_aux F phi A (fromQ 0.3).
  Eval vm_compute in valid_aux_s 40.
  
End sqrt_cheb.

Module oval_fourier.
 Section s.

  Import fourier.
  Let Bf := basis_ops 0 (fromZ 2 * pi).
  Local Existing Instance Bf.
  Notation Model := (@model_ops IPrimFloat.nbh Bf).
  
  Let X0 : Model := msingle [fromQ 0.9].
  Let Y0 : Model := msingle [fromQ 1.1].
  Let h : Model := msingle [fromQ 0.64]. (* 16/25 *)

  Let x0 : Model := msingle [fromQ 0.9; 0; fromQ 0.3].
  Let y0 : Model := msingle [1;fromQ 0.3].

  Let msquare M : list Model := smul M M.
  Let Px : list Model := ssub (msquare sid) [X0].
  Let Py : list Model := ssub (msquare sid) [Y0].
  Let Hx : list Model := sscal (msingle [fromZ 4]) (smul sid Px).
  Let Hy : list Model := sscal (msingle [fromZ 4]) (smul sid Py).
  
  Let u : Model := taylor.eval' Hx x0.
  Let v : Model := taylor.eval' Hy y0.

  Let sx : list Model := [x0;u].
  Let sy : list Model := [y0;v].
  Let H : list Model := sadd (taylor.comp (msquare Px) sx) (taylor.comp (msquare Px) sy).

  Eval vm_compute in H.

  (** system of polynomial equations *)
  Definition F : list Model := ssub H [h].
  Eval vm_compute in F.

  (** (bad) initial candidate solution *)
  Definition phi0 : Model := 0.
  Definition Fphi0 : Model := taylor.eval' F phi0.
  Eval vm_compute in Fphi0.
  Eval vm_compute in mrange Fphi0.

  (** automatic computation of a certified solution 
      - [d]: interpolation degree
      - [n]: Newton iterations
      - [10]: recursion depth for finding the radius
      - [1]: maximal radius
   *)
  Definition oval_valid d n: E Model :=
    mpolynom_eq d n 10 1 F phi0.

  (* timings on Damien's machine, plugged *)
  Time Eval vm_compute in oval_valid 20 10. (* [[-0.015...; 0.015...]]; / 1.4s *)
  Time Eval vm_compute in oval_valid 25 10. (* [[-0.0031...; 0.0031...]]; / 2.8s*)
  
  Time Eval vm_compute in oval_valid 30 10. (* [[-0.00107...; 0.00107...]] / 4.4s *)
  Time Eval vm_compute in polynom_eq_oracle 30 10 F phi0. (* 1.2s -> 3.2s for the certification *)
  
  Time Eval vm_compute in oval_valid 50 10. (* e-05 / 19.6s *)
  Time Eval vm_compute in polynom_eq_oracle 50 10 F phi0. (* 3.3s -> 16.3s for the certification *)

  (** manual computation *)
  (** refined solution, with degree [d] for the oracle, and [n] Newton iterations for each point  *)
  Definition phi d n : Model := polynom_eq_oracle d n F phi0.
  Eval vm_compute in mrange (sub (phi 20 10) (phi 30 10)). (* 0.002 *)
  
 End s.
End oval_fourier.

(** * Example 3: resolution of polynomial functional equations *)

Require Import interfaces.
Require Import vectorspace taylor approx.
Require Import intervals String.
Require fourier chebyshev.

From ReductionEffect Require Import PrintingEffect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance IPrimFloat.nbh.

Module sqrt_cheb.
  
  (** ** a square root as a solution of a polynomial functional equations

        F(phi) = - (1 + X^2 / 10) + phi^2
        F(phi) = 0  <->   phi(X) = sqrt (1 + X^2 / 10)
   *)
  
  (** Chebyshev basis by default for models *)
  Import chebyshev.
  Local Existing Instance basis11_ops.
  Notation Model := (@model_ops IPrimFloat.nbh basis11_ops).

  (** polynomial equation *)
  Definition F': list (list FF) := [sopp (1 + (sscal (fromQ 0.1) (pid*pid)));0;1].
  Definition F : list Model := map mfc F'.

  (** (bad) candidate solution *)
  Definition phi0 : list FF := 1. 

  (** ** automatic computation of a certified solution 
     (60: interpolation degree; None: no truncation)
   *)
  Definition valid_s : E float :=
    elet M := mpolynom_eq 60 None F phi0 
    in ret (width (rem M)).
  Eval vm_compute in valid_s.   (* 3e-14 *)


  (** ** manual computation *)
  
  (** refined solution, via the oracle (degree: 5) *)
  Definition phi := polynom_eq_oracle 5 (map mcf F) phi0.
  
  (** manual validation of this refined solution (d is the degree for the contracting operator) *)
  Definition valid_aux_s d t : E Model :=
    let DF := eval' (taylor.derive F') phi in
    let A := interpolate d (fun x => 1 / eval' DF x) in
    mpolynom_eq_aux t F phi A (fromQ 0.00001).
  Eval vm_compute in e_map (fun M => width (rem M)) (valid_aux_s 40 None). (* 7e-6 *)
  
End sqrt_cheb.


(** ** a parametrisation for Abelian integrals (related to example_h16.v) *)

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

  (* Eval vm_compute in H. *)

  (** system of polynomial equations *)
  Definition F : list Model := ssub H [h].
  Definition F' := map mcf F.

  (** (bad) initial candidate solution *)
  Definition phi0 : list FF := 0.

  (** automatic computation of a certified solution 
      - [d]: interpolation degree
      - [t]: truncation degree (if any)
   *)
  Definition oval_valid d t: E float :=
    elet x := mpolynom_eq d t F phi0 
    in ret (width (rem x)).

  Definition ignore [A] (a: A) := tt.

  Definition full_oracle d t :=
   let phi' := polynom_eq_oracle d F' phi0 in
   let DF := beval (taylor.eval't t (taylor.derive F') phi') in
   let A' := interpolate d (fun x => 1 / DF x) in
   let A := mfc A' in
   let phi := mfc phi' in
   elet c := mnorm (A * taylor.eval't t F phi) in
   let L := taylor.derive (polynom_eq.opnewton F A) in
   let L' := map (fun M => map I2F (pol M)) L in
   elet l := polynom_for_lambda t L' phi' in
   find_radius (I2F c) l.
  
  (* timings on Damien's machine, plugged *)
  (* negative degree: do not truncate (and use absolute value for interpolation degree) *)
  Time Eval native_compute in oval_valid 20 (Some 40%nat).    (* missed / .07s *)
  Time Eval native_compute in oval_valid 20 None.            (* 0.006  / .07s *)
  Time Eval native_compute in oval_valid 25 (Some 50%nat).    (* 0.006  / .08s*)
  Time Eval native_compute in oval_valid 25 None.            (* 0.002  / .08s*)
  
  Time Eval native_compute in oval_valid 30 (Some 60%nat).    (* 0.001  / .08s *)
  Time Eval native_compute in oval_valid 30 None.            (* 0.0006 / .09s *)
  Time Eval native_compute in ignore (polynom_eq_oracle 30 F' phi0). (* .1s *)
  Time Eval native_compute in ignore (full_oracle 30 None).          (* .2s -> .1s for radius *)
  
  Time Eval native_compute in oval_valid 50 (Some 100%nat).   (* 1.0e-4 / .2s *)
  Time Eval native_compute in oval_valid 50 None.            (* 1.4e-5 / .2s *)
  Time Eval native_compute in ignore (polynom_eq_oracle 50 F' phi0). (* .1s *)
  Time Eval native_compute in ignore (full_oracle 50 None).          (* .2s -> .1s for radius *)

  Time Eval native_compute in oval_valid 100 (Some 200%nat).  (* 1.6e-8 / .3s *)
  Time Eval native_compute in oval_valid 100 None.           (* 2.1e-9 / .4s *)
  Time Eval native_compute in ignore (polynom_eq_oracle 100 F' phi0). (* .2s *)
  Time Eval native_compute in ignore (full_oracle 100 None).          (* .4s -> .2s for radius *)

  Time Eval native_compute in oval_valid 200 (Some 400%nat).  (* 2.7e-12 / 1.3s *)
  Time Eval native_compute in oval_valid 200 None.           (* 2.7e-12 / 1.6s *)
  Time Eval native_compute in ignore (polynom_eq_oracle 200 F' phi0). (* .5s *)
  Time Eval native_compute in ignore (full_oracle 200 None).          (* 1.4s -> 1.1s for radius *)
  
  (** manual computation *)
  (** refined solution, with degree [d] for the oracle *)
  Definition phi d: Model := mfc (polynom_eq_oracle d F' phi0).
  Eval vm_compute in mrange (sub (phi 20) (phi 30)). (* 0.002 *)
  
 End s.
End oval_fourier.

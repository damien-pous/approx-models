(** * Tests for the library *)

Require Import intervals rescale tactic syntax.
Require taylor chebyshev approx.

(** ** testing the tactics  *)
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  approx.
  Restart.
  approx (i_deg 15).
  Restart.
  approx chebyshev11.
  Restart.
  approx (chebyshev11, i_deg 15).
  Restart.
  approx (static 0.5 2).
  Restart.
  approx (static 0.5 2, i_deg 15).
Qed.

Goal 1.5 <= sqrt 2 <= 1.6.
Proof.
  Fail approx.
Abort.

Goal 1 <= 2.
Proof. approx. Qed.
Goal 1 < 2.
Proof. approx. Qed.
Goal 2 > 1.
Proof. approx. Qed.
Goal 2 >= 1.
Proof. approx. Qed.

Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  approx.
Qed.

Goal 0.9999 <= RInt (fun x => x*x*3.0) 0 1 <= 1.00001.
Proof.
  approx.
Qed.

Goal 2.08670 <= RInt (fun x => (1+x)/((1-x)*(1-x)+1/4)) 0 (pi/4)  <= 2.08672.
  approx (i_deg 11).
Qed.

Goal -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  Fail approx (chebyshev11).
  approx (i_deg 5).
Qed.

Goal 0 <= RInt (fun x => x) (-2) 2 <= 0.
Proof.
  (* we cannot be that precise! *)
  Fail approx (i_deg 5).
Abort.

Goal -0.1 <= RInt (fun x => 0%R) (-1/3) (1/3) <= 0.1.
Proof.
  approx.
Qed.

Goal -0.1 <= RInt (fun x => 0%R) (-3) (3) <= 0.1.
Proof.
  Fail approx (chebyshev11).
  approx. 
Qed.

Goal RInt (fun x => RInt id 1 x) 0 1 <= 5.
  (* variable x occurs in bad position *)
  Fail approx.
Abort.

Goal 1.84 <= RInt (fun x => cos x + 1) 0 1 <= 1.85.
Proof.
  Fail approx.                  (* need Fourier basis *)
  approx fourier.
Qed.

Goal 1/3 <= RInt (fun x => cos x * sin x) 0 1 <= 1/2.
Proof.
  Fail approx.                  (* need Fourier basis *)
  approx fourier. 
Qed.

Goal RInt (fun x => cos 1 + x) 0 1 <= cos 1+0.6.
Proof.
  approx.
Qed.

Goal RInt (fun x => cos (x*x)) 0 1 <= 100.
Proof.
  Fail approx.                  (* only [cos x] is allowed in Fourier *)
  Fail approx fourier. 
Abort.

Goal RInt (fun x => x * cos x) 0 1 <= 100.
Proof.
  Fail approx.                  (* would need a basis supporting both [id] and [cos] *)
  Fail approx fourier.
Abort.


Goal forall x, 0<=x<=1 -> 1<2.
  approx.
Qed.
Goal forall x, 0<=x<=1 -> x<2.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x*x<x.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x < sqrt x.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x <> sqrt x.
  approx.
Qed.
Goal forall x, 0.111<=x<=0.999 -> x <> sqrt x.
  approx (i_deg 60).
Qed.
Goal forall x, 0.111<=x<=0.999 -> x < sqrt x.
  approx (i_deg 60).
Qed.

Goal 3.46 <= RInt (fun x => sqrt (2+x)) (-1.999) 1 <= 3.47.
  estimate (RInt (fun x => sqrt (2+x)) (-1.999) 1) (i_deg 52). (* fails *)
  estimate (RInt (fun x => sqrt (2+x)) (-1.999) 1) (i_deg 53). (* imprecise: [-6; 13] *)
  estimate (RInt (fun x => sqrt (2+x)) (-1.999) 1) (i_deg 100). (* very imprecise: [-2e+17; 2e+17] *)
  (* increasing precision works... *)
  approx (bigint120, i_deg 100).   (* with truncation *)
  Restart.
  approx (bigint120, i_deg (-68)). (* without truncation *)
Qed.


(** testing Fourier basis *)
Goal True.
  estimate (RInt (fun x => sin x / (2+cos x)) 0 pi) fourier.
  estimate (RInt (fun x => sin x / (2+cos x)) (pi/4) (pi/3)) fourier.
  estimate (RInt (fun x => sin x / (2+cos x)) (-4) (18*pi/3)) fourier.
  (* below: although 1+sin x > 0 on [0;pi], the range is estimated on [0;2pi], so this cannot work... *)
  estimate (RInt (fun x => sqrt (1+sin x)) 0 pi) fourier.
  (* even in dynamic mode: the declared domain does not change the way the range is estimated *)
  estimate (RInt (fun x => sqrt (1+sin x)) 0 pi) (fourier, dynamic).
  estimate (RInt (fun x => sqrt (2+sin x)) 0 pi) fourier.
  estimate (RInt (fun x => sqrt (2+sin x) / (2+cos x)) (-4) (18*pi/3)) fourier.
Abort.


(** ** testing direct computations  *)
Eval vm_compute in
    let e := EXPR ((integrate' (1 / (1 + id'))) 0 (pi'/fromZ' 4)) in 
    LET E ::= Dynamic.Sem' chebyshev_model_ops 20 e IN ret (width E).

(** increase 20 to get more digits *)
Eval vm_compute in
    let e := EXPR (integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)) in
    LET E ::= Static.Sem' chebyshev11_model_ops 20 e IN ret (width E).

(** testing interpolation on rescaled bases *)
Eval vm_compute in
    let f := FXPR (id' / fsqrt ((1+id') / (fromZ' 3+id'))) in
    Static.Sem' (chebyshev_model_ops (fromZ 18) (fromZ 200)) 10 f.


(** Note that the neighborhood is set by default to [IPrimFloat.nbh], i.e., intervals with primitive floating point endpoints 
   other candidates include:
   - [IBigInt60/120/300.nbh]: intervals with floating points endpoints, floating points being represented via primitive 63bit integers (less axioms, a bit less efficient)
   - [IStdZ60/120.nbh]: intervals with floating points endpoints, floating points being represented via Coq integers (Z) (no axioms, not so efficient)
  *)

Time Eval vm_compute in
    let e := EXPR (integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)) in
    e_map width (Static.Sem' (N:=IStdZ60.nbh) chebyshev11_model_ops 10 e).
(** above: need 1sec *)
(** below: also need 1sec thanks to sharing *)
Time Eval vm_compute in
    let e := EXPR (let_ee x := integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)
                       in x + x)
    in
    e_map width (Static.Sem' (N:=IStdZ60.nbh) chebyshev11_model_ops 10 e).

Time Eval vm_compute in
    let e := FXPR ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) in
    Static.Sem' (N:=IStdZ60.nbh) chebyshev11_model_ops 12 e.
(** above: need 1sec *)
(** below: also need 1sec thanks to sharing *)
Time Eval vm_compute in
    let e := FXPR (let_ff x := (1+id') / ((1-id')*(1-id')+1/fromZ' 4)
                       in x + x)
    in
    Static.Sem' (N:=IStdZ60.nbh) chebyshev11_model_ops 12 e.


(** About the axioms we use: *)
(**
Print Assumptions syntax.Dynamic.check.   (** only three axioms for the (classical) construction of reals *)
Print Assumptions approx.model.           (** plus excluded middle for classical logic *)
Print Assumptions chebyshev.basis.        (** idem *)
Print Assumptions IStdZ60.nbh.            (** idem, everything is emulated *)
Print Assumptions IBigInt60.nbh.          (** plus axioms for primitive 63bits integers (Int63) *)
Print Assumptions IPrimFloat.nbh.         (** plus axioms for primitive floats (PrimFloat) *)
*)

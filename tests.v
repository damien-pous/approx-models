(** * Tests for the library *)

Require Import intervals rescale syntax tactic.
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
  Fail approx.                  (* TOFIX: reify with e_cst *)
Abort.

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


(** solving quantified formulas by subdivision (here up to depth 3) 
    (no reification provided for this so far: we would probably need an Ocaml plugin)
 *)
Goal forall c, 0<=c<=1 -> RInt (fun x => x+c/2) 0 1 <= 1+c.
  (* we can provide the reified term explicitly to the tactic *)
  approx (term (forall_bisect 0 1
            (fun c => integrate (id'+cst c/fromZ 2) 0 1 <= 1 + c))).
  Restart.
  (* or change the goal to let it appear before calling the tactic *)
  change (sem' (TERM (forall_bisect 0 1
            (fun c => integrate (id'+cst c/fromZ 2) 0 1 <= 1 + c)))).
  approx. 
Qed.

Goal forall c, 0<=c<=1 -> c <= 2/3 \/ 1/3 <= c.
  approx (term (forall_bisect 0 1
            (fun c => c <= fromZ 2 / fromZ 3 \/ 1 / fromZ 3 <= c))).
Qed.

(** quantifiers may appear in subformulas with this method *)
Goal forall c, 0<=c<=1 -> c <= 2/3 \/ forall d, 0<=d<=1 -> 1/3 <= d \/ d <= c.
  approx (term (forall_bisect 0 1
                       (fun c => c <= fromZ 2 / fromZ 3 \/ 
                      forall_bisect 0 1
                       (fun d => 1 / fromZ 3 <= d \/ d <= c)))).
Qed.

(** solving (restricted) quantified formulas by model comparisons *)
Goal forall c, 0.1<=c<=0.9 -> c < sqrt c.
  approx. 
Qed.
Goal forall c, 0.1<=c<=0.9 -> c < sqrt c < sqrt (sqrt c).
  approx.
  (* there are two comparisons, but the model for the inner term (sqrt c)
     is computed only once, thanks to a let..in :
     the reified term is 
     [TERM (forall_models (fromQ 0.1) (fromQ 0.9)
              (tlet s := sqrt id' in id' < s /\ s < sqrt (sqrt id'))))]
   *)   
  (* Show Proof. *)
  Restart.
  (* to further share the occurence of [sqrt c] in the rhs, we can provide an explicit term *)
  approx (term (forall_models (fromQ 0.1) (fromQ 0.9)
                                    (tlet s := sqrt id' in id' < s < sqrt s))).
  (* Show Proof. *)
  Restart.
  (* alternatively: *)
  change (sem' (TERM (forall_models (fromQ 0.1) (fromQ 0.9)
                                    (tlet s := sqrt id' in id' < s < sqrt s)))).
  approx. 
  (* Show Proof. *)
Qed.

(** with this method, quantifiers appearing in subformulas must be dealt with by bisection *)
Goal forall c, 0.1<=c<=0.4 -> forall d, 0<=d<=0.5 -> c+d < sqrt (c+d).
  change (sem' (TERM (forall_models (fromQ 0.1) (fromQ 0.4)
                     (forall_bisect 0 (fromQ 0.5) 
                     (fun d => id'+cst d < sqrt (id'+cst d))
         )))).
  approx.
Qed.


(** ** testing direct computations  *)
Goal True.
  estimate_term ((integrate (1 / (1 + id'))) 0 (pi/fromZ 4))
                (i_deg 20). 

  estimate_term (integrate ((1+id') / ((1-id')*(1-id')+1/fromZ 4)) 0 (pi/fromZ 4))
                (chebyshev11, i_deg 20).
  
  estimate_term (id' / sqrt ((1+id') / (fromZ 3+id')))
                (static 18 200).

  estimate_term (integrate ((1+id') / ((1-id')*(1-id')+1/fromZ 4)) 0 (pi/fromZ 4))
                (chebyshev11, i_deg 50).
  (** below: not longer, thanks to sharing *)
  estimate_term (tlet x := integrate ((1+id') / ((1-id')*(1-id')+1/fromZ 4)) 0 (pi/fromZ 4)
                         in x + x)%term
                (chebyshev11, i_deg 50).
  (* TODO: check: above estimations are no longer precise at precision 100... *)
  
  estimate_term (sqrt (sqrt (fromZ 2 + id')))
                (chebyshev11, i_deg 50).
Abort.

(** About the axioms we use: *)
(**
Print Assumptions syntax.Dynamic.check.   (** only three axioms for the (classical) construction of reals *)
Print Assumptions approx.model.           (** plus excluded middle for classical logic *)
Print Assumptions chebyshev.basis.        (** idem *)
Print Assumptions IStdZ60.nbh.            (** idem, everything is emulated *)
Print Assumptions IBigInt60.nbh.          (** plus axioms for primitive 63bits integers (Int63) *)
Print Assumptions IPrimFloat.nbh.         (** plus axioms for primitive floats (PrimFloat) *)
*)

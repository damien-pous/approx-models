(** * tests for the library *)

Require Import intervals rescale errors tactic syntax.
Require taylor chebyshev approx.


Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  bound (sqrt (fromZ 2)).
Qed.

Goal 1.5 <= sqrt 2 <= 1.6.
Proof.
  Fail bound (sqrt (fromZ 2)).
Abort.

Lemma ex1: 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  bound (e_integrate (f_id * f_id) 0 1).
Qed.

Lemma ex2: 0.405465 <= RInt (fun x => 1/(2+x)) 0 1 <= 0.405466.
  (** ln3 - ln2 = 0.405465108108 *)
  Fail bound (e_integrate (1 / (fromZ 2 + f_id)) 0 1).
  (** need to increase the interpolation degree *)
  bound (e_integrate (1 / (fromZ 2 + f_id)) 0 1) 13%Z.
Qed.

Lemma ex3: 0.405465108108 <= RInt (fun x => 1/(2+x)) 0 1 <= 0.405465108109.
  (** ln3 - ln2 = 0.405465108108 *)
  bound (e_integrate (1 / (fromZ 2 + f_id)) 0 1) 23%Z.
Qed.

Lemma ex4: 2.08670 <= RInt (fun x => (1+x)/((1-x)*(1-x)+1/4)) 0 (pi/4)  <= 2.08672.
  Fail bound (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) 20%Z.
Abort.

(** problem: above, [echeck] fails to verify that the denominator cannot be 0 

    the range of   (1-X)² + 1/4 = 7/4 - 2 T1 X + 1/2 T2 X
    is approximated as [ 7/4-2-1/2 ; 7/4 +2+1/2 ] = [-3/4;17/4] 
    
    we could try to evaluate the polynomial on the interval [0;pi/4] 
    used in the integral, but we would again obtain something containing 0 
    ([-1.8915926535898033; 2.8207963267949037], see below)   
*)

Lemma ex5: -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [-1;1] *)
  Fail bound (e_integrate f_id (fromZ (-2)) (fromZ 2)).
  (* with a rescaled chebyshev basis *)
  bound (e_integrate f_id (fromZ (-2)) (fromZ 2)) 5%Z
        (approx.model (chebyshev.basis (DZ2 (-2) 2))).
  Restart.
  (* with the monomial basis *)
  bound (e_integrate f_id (fromZ (-2)) (fromZ 2)) 5%Z
        (approx.model (taylor.basis (DZ2 (-2) 2))).  
Qed.

Lemma ex5': 0 <= RInt (fun x => x) (-2) 2 <= 0.
Proof.
  (* we cannot be that precise! *)
  Fail bound (e_integrate f_id (fromZ (-2)) (fromZ 2)) 5%Z
        (approx.model (rescale.to (DZ2 (-2) 2) chebyshev.basis)).
  Restart.
  Fail bound (e_integrate f_id (fromZ (-2)) (fromZ 2)) 10%Z
       (approx.model (taylor.basis (DZ2 (-2) 2))).
Abort.

Lemma ex6: -0.1 <= RInt (fun x => 0%R) (-1/3) (1/3) <= 0.1.
Proof.
  bound (e_integrate f_zer (fromZ (-1)/fromZ 3) (fromZ 1/fromZ 3)).
Qed.

Lemma ex6': -0.1 <= RInt (fun x => 0%R) (-3) (3) <= 0.1.
Proof.
  Fail bound (e_integrate f_zer (fromZ (-3)) (fromZ 3)).
  bound (e_integrate f_zer (fromZ (-3)) (fromZ 3)) 10%Z
        (approx.model (chebyshev.basis (DZ2 (-3) 3))).
Qed.


(** direct computations  *)

Eval vm_compute in
    let e := (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) in
    LET E ::= eSem (approx.model chebyshev.basis11) 20 e IN ret (width E).
    (** increase 20 to get more digits *)


(** testing interpolation on rescaled bases *)
Eval vm_compute in
    let f: fxpr := f_id / sqrt ((1+f_id) / (fromZ 3+f_id)) in
    fSem (approx.model (chebyshev.basis (DZ2 18 200) )) 3 f.


(** Note that the neighborhood is set by default to [Iprimitive.nbh], i.e., intervals with primitive floating point endpoints 
   other candidates include:
   - [IBigInt.nbh]: intervals with floating points endpoints, floating points being represented via primitive 63bit integers (less axioms, a bit less efficient)
   - [IZ.nbh]: intervals with floating points endpoints, floating points being represented via Coq integers (Z) (no axioms, not so efficient)
  *)

Eval vm_compute in
    let e := (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) in
    e_map width (eSem (N:=IZ.nbh) (approx.model chebyshev.basis11) 20 e).


(* TOCHECK: why is 1+1 not a singleton with primitive floats? *)
Eval vm_compute in (fromZ 2: Iprimitive.nbh).
Eval vm_compute in (1+1: Iprimitive.nbh). (* arg *)
Eval vm_compute in (1+1: IZ.nbh).         (* ok *)
Eval vm_compute in (1+1: IBigInt.nbh).    (* ok *)


(** About neighborhood instances:
Print Assumptions syntax.bound.   (** only four axioms for the (classical) construction of reals *)
Print Assumptions approx.model.   (** idem *)
Print Assumptions chebyshev.basis.(** idem *)
Print Assumptions IZ.nbh.         (** idem, only 4, everything is emulated *)
Print Assumptions IBigInt.nbh.    (** plus axioms for primitive 63bits integers (Int63) *)
Print Assumptions Iprimitive.nbh. (** plus axioms for primitive floats (PrimFloat) *)
 *)

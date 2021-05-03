(** * Examples on how to use the library *)

Require Import Reals.
Require Import syntax tactic.
Require taylor chebyshev approx.

Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  bound (e_sqrt (e_fromZ 2)).
Qed.

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

Lemma ex2': 0.405465108108 <= RInt (fun x => 1/(2+x)) 0 1 <= 0.405465108109.
  (** ln3 - ln2 = 0.405465108108 *)
  bound (e_integrate (1 / (fromZ 2 + f_id)) 0 1) 23%Z.
Qed.

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

Lemma ex7: 1.578 <= RInt (fun x => sqrt (2+x)) 0 1 <= 1.579.
Proof.
  bound (e_integrate (sqrt (fromZ 2+f_id)) 0 1).
Qed.

Lemma ex7': 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (* since we use Chebyshev basis on [-1;1] by default, 
     we get too close from sqrt of a negative value here *)
  Fail bound (e_integrate (sqrt (1+f_id)) 0 1).
  (* solved by using a better basis *)
  bound (e_integrate (sqrt (1+f_id)) 0 1)  5%Z
        (approx.model (chebyshev.basis (DZ2 0 1))).
Qed.

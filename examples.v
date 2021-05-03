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

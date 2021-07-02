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
 
  Let sn: Z := n+1.
  Let sdn: Z := 2*n+1.
  Let osdn: C := divZ sdn 1.
  Let twopisdn: C := mulZ 2 (pi * osdn).

  Definition newton_method (N:Z) (f : Fun) (f' : Fun) :=
    Zfold (fun _ s=> s - (f s)/(f' s)) N 0.

  Let point : Z -> C :=
    Zmap.get 0 (
               Zmap.mk (fun i => mulZ i twopisdn) sdn).

  Let apply_points G : Z -> list C :=
    Zmap.get 0 (
               Zmap.mk (fun i => apply G (point i)) sdn).

  Let map_points g : Z -> C :=
   Zmap.get 0 (
              Zmap.mk (fun i => g (point i)) sdn).

  Let cosin := map_points cos.
  Let sinus := map_points sin.

  
 Definition coeff_aux (value:Z->C) (g: Z -> C) (i : Z) : C :=
   Zfold (fun j acc => acc +  value j * g ((i*j) mod sdn)%Z) sdn 0.
      
 Definition coeff_cos (v:Z->C) (i : Z) :=
   (if Z.eqb i 0%Z then ssrfun.id else mulZ 2)
   (coeff_aux v cosin i * osdn).

 Definition coeff_sin (v:Z->C) (i : Z) :=
   mulZ 2 (coeff_aux v sinus (i+1) * osdn).
  
  
  Definition oval_approx (F DFx DFy: poly) (u v : Fun) (N:Z) :=
    let F' := sadd (sscal u DFx) (sscal v DFy) in
    let value :=
    Zmap.get 0 (
               Zmap.mk (fun i => newton_method N (eval' (apply_points F i)) (eval' (apply_points F' i))) sdn)
    in
    merge (Zmap.tolist 0 sn (Zmap.mk (coeff_cos value) sn))
         (Zmap.tolist 0  n (Zmap.mk (coeff_sin value)  n)). 

End i.

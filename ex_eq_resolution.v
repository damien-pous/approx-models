(* Example of a polynomial equation resolution *)

Require Import interfaces.

Require Import vectorspace taylor approx.

Require Import utils String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section i.
  Context {nbh: NBH} {BO: BasisOps}.
  Notation Model := (@model_ops nbh BO).
  Variable n: Z.

  Definition newton_method (N:Z) (f f' : list FF)  u0 :=
    Zfold (fun _ u=> u - (taylor.eval' f u)/(taylor.eval' f' u)) N u0.

  
  Definition solution_approx (F: list Model) (N:Z) (s0 : Model) : Model :=
    let p0 := mcf s0 in
    let Fp := map (fun f => mcf f) F in
    let f := (fun t => let P := map (fun f=> beval f t) Fp in
                 newton_method N P (derive P) (beval p0 t)) in
    mfc (vectorspace.interpolate n f).
  
End i.

Require Import intervals.
Require Import chebyshev.
Section testCheb.

  Let Bc := basis11_ops.
  Let nbh := IPrimFloat.nbh.
  Let flt := @FF nbh.
  Let Bt := taylor.basis_ops (fromZ (-1)) (fromZ 1).
  Notation Model := (@model_ops nbh Bc).

  
  Definition a0 : list flt := sopp (sadd pone (sscal (fromZ 10) (pmul pid pid))).
  Eval compute in a0.
  Definition A0 : Model  := mfc a0.
  
  Definition F1 : list Model := A0::(mfc [0])::(mfc pone)::[].
  Eval compute in F1.
  Definition s0 : Model := mfc pone.

  Definition Pf := taylor.eval' F1 s0.
  Eval compute in Pf.
  Eval compute in mrange Pf.

  Definition s : Model := solution_approx 5 F1 10 s0.
  (*Eval compute in s.
  
  Definition Pf' := taylor.eval' F1 s.
  (* We make a taylor evaluation but we use the operations of the Cheb basis (for the multiplication) *)
  Eval compute in Pf'.
  Eval compute in mrange Pf'.*)

  Definition valid_aux_s n : E Model :=
    let DF := mcf (eval' (taylor.derive F1) s) in
    let A := mfc (interpolate n (fun x=> 1 / eval' DF x)) in
    @mpolyn_eq_aux nbh Bc F1 s A (F2I (divZ 10 (fromZ 1))).
 (* Eval compute in valid_aux_s 40.*)

  Definition valid_s : E Model :=
    @mpolyn_eq nbh Bc 5 20 10 F1 s0 (divZ 1 (fromZ 1)).
   Eval native_compute in valid_s.
 
  
End testCheb.

Require Import fourier.

Section testFourier.

  Let Bf := fourier.basis_ops 0 (fromZ 2 * pi).
  Let nbh := IPrimFloat.nbh.
  Let flt := @FF nbh.
  Let Bt := taylor.basis_ops (fromZ (-1)) (fromZ 1).
  Notation Model := (@model_ops nbh Bf).
  
  Let X0 : Model := msingle [divZ 10 (fromZ 9)].
  Let Y0 : Model := msingle [divZ 10 (fromZ 11)].
  Let h : Model := msingle [divZ 25 (fromZ 16)].

  Let x0 : Model := msingle ((divZ 10 (fromZ 9))::0::(divZ 10 (fromZ 3))::[]).
  Let y0 : Model := msingle ((divZ 100 (fromZ 100))::(divZ 10 (fromZ 3))::[]).

  Let msquare T : list Model := smul T T.
  Let Px : list Model := ssub (msquare sid) [X0].
  Let Py : list Model := ssub (msquare sid) [Y0].
  Let Hx : list Model := sscal (msingle [fromZ 4]) (smul sid Px).
  Let Hy : list Model := sscal (msingle [fromZ 4]) (smul sid Py).
  
  Let u : Model := taylor.eval' Hx x0.
  Let v : Model := taylor.eval' Hy y0.

  Let sx : list Model := x0::u::[].
  Let sy : list Model := y0::v::[].
  Let H : list Model := sadd (taylor.comp (msquare Px) sx) (taylor.comp (msquare Px) sy).

  Definition F2 : list Model := ssub H [h].
  Definition s_init : Model := 0.
 (* Eval compute in F2.*)
  Definition Pf2 : Model := taylor.eval' F2 s_init.
  (*Eval compute in Pf2.*)
 (* Eval compute in mrange Pf2.*)
  
  Definition s_approx50 : Model := solution_approx 50 F2 10 s_init.
  Definition s_approx : Model := solution_approx 50 F2 10 s_init.
 (* Definition diff := mrange (sub s_approx50 s_approx60).
  Eval compute in diff.*)
 (*Eval compute in s_approx.*)

  Definition  Pf2' : Model := taylor.eval' F2 s_approx.
  (*Eval compute in Pf2'.*)
  (*Time Eval compute in mrange Pf2'.*)
  (* 40 -> [[-0.00013693284970087133; 0.00013693377905579768]]
     : nbh *)
  (* 50 -> [[-1.9056106884527256e-05; 1.9056119656310886e-05]]
     : nbh *)
  (* 60 -> [[-1.506830039134505e-06; 1.5068300324731668e-06]]
     : nbh *)
  (* 100 -> [[-3.298760757089546e-09; 3.298759813399975e-09]]
     : nbh  
   Time exec ~ 5 min *)
  (* 120 -> [[-5.8430719814984113e-11; 5.843060879268165e-11]]
     : nbh 7 min *)

 Definition oval_valid n : E Model :=
   @mpolyn_eq nbh Bf 13 n 10 F2 s_init (divZ 1 (fromZ 1)).
 
 (*Time Eval compute in oval_valid 20.*) (*[[-0.015069843634262801; 0.0150698436342628]]; / 24 s*)
 Time Eval compute in oval_valid 25. (* [[-0.0031384950293210315; 0.0031384950293210311]]; / 48s s*)
 (*Time Eval compute in oval_valid 30.*) (* [[-0.0010775659050942326; 0.0010775659050942324]] / 71 s *)
 Time Eval compute in oval_valid 35. (* [[-0.00043869723080766903; 0.00043869723080766898]] / 122 s *)
 (*Time Eval compute in oval_valid 40.*) (* [[-0.00015525289736369543; 0.00015525289736369541]] / 169 s *)
 Time Eval compute in oval_valid 45. (* [[-6.1553068275257869e-05; 6.1553068275257855e-05]] / 264 s *)
 (*Time Eval compute in oval_valid 50.*)(* [[-2.5468849730489291e-05; 2.5468849730489287e-05]] / 354 s *)
 Time Eval compute in oval_valid 60. (* [[-3.9777846581784549e-06; 3.9777846581784541e-06]] / 704 s *)
 Time Eval compute in oval_valid 80. (* [[-1.2660417643661427e-07; 1.2660417643661424e-07]] / 2020 s *)
 (*Time Eval compute in oval_valid 100.*)
  (*Time Eval compute in oval_valid 120.*)
 
End testfourier.

  

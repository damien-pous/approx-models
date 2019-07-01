(** * Various tests *)

Require Import approx rescale intervals.
Require chebyshev taylor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope RO_scope. 

Definition close a b p x := Rabs (x - IZR a / IZR b) <= 1 / IZR p.

Lemma rec (e: I) (P: Prop): Prop. exact P. Qed.
Lemma recE e P: rec e P <-> P. Admitted.
Lemma recT e: rec e True. by rewrite recE. Qed.
Hint Resolve recT. 

Let INBH := INBH 64.            (* precision *)

Lemma prove_close a b p (x: R) (X: @II INBH):
  contains X x -> 
  match mag (X - fromZ a / fromZ b) with
  | Some e => if is_lt e (1/fromZ p) then rec e True else rec e False
  | None => False
  end
  -> close a b p x.
Proof.
  intros Hx. case magE => [E e Ee H|[]].
  lapply (H (x - fromZ a / fromZ b)) =>[{H} H |]; last rel.
  case is_ltE => [L|]; rewrite recE =>//.
  lapply (L _ (1/fromZ p) Ee) =>[{L} L _ |]; last rel.
  unfold close. simpl in *. lra.
Qed.


Goal close 1 3 100000000000000 (RInt (fun x => x*x) 0 1).
  eapply prove_close.
  (* NOTE: comme on a une existentielle, [apply rmintegrate] utilise automatiquement la seule base valide qu'il connait: chebyshev (sur -1;1)
     on peut préciser explicitement la base sur ces exemples (B:=...)
     sur des exemples où l'on construirait le modèle explicitement ce pb n'apparaît pas car la base est marquée dans le type des modèles
   *)
  apply rmintegrate. apply rmmul; apply rmid.
  intros. apply continuity_pt_mult; apply continuity_pt_id. 
  apply rfromZ. 
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.
  apply rfromZ. 
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.
  by vm_compute.                   (* good! *)
Qed.

Goal close 405465108108 1000000000000 10000 (RInt (fun x => 1/(1+1+x)) 0 1). 
  eapply prove_close.
  apply rmintegrate. apply (rmdiv 10). apply rmcst. rel.
  apply rmadd. apply rmadd; apply rmcst; rel.
  apply rmid. 
  intros x Hx. apply continuity_pt_div. by apply continuity_pt_const.
  apply continuity_pt_plus. by apply continuity_pt_const.
  apply continuity_pt_id.
  revert Hx. rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.
  apply rfromZ. 
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.  
  apply rfromZ. 
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.
  by vm_compute.                   (* good! *)
Qed.

Goal
  let f x := R_sqrt.sqrt (1+1+x) in
  close 15811388 10000000 1000000 (f (1/2)).
  intro f.
  eapply prove_close.
  apply rmeval. apply (rmsqrt 10). apply rmadd. apply rmcst; rel. apply rmid. rel. 
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra.  
  by vm_compute.                   (* good! *)
Qed.

Goal let f x := R_sqrt.sqrt x in close 12247448 10000000 10000 (f (3/2)). (* 1,22474487139 *)
  intro f.
  assert (d : IZR 1 < IZR 2) by lra. 
  eapply prove_close.
  apply (rmeval (B:=rescale (DfromZ2 d) chebyshev.basis)).
  apply (rmsqrt 10). apply rmid.
  rel.
  rewrite /dom/=. lra.
  by vm_compute.
Qed.

Goal let f x := 1/(1+x) in close 2 3 10000 (f (1/2)).
  intro f.
  assert (d : IZR 0 < IZR 1) by lra. 
  eapply prove_close.
  apply (rmeval (B:=rescale (DfromZ2 d) chebyshev.basis)).
  apply (rmdiv 10). apply rmone. apply rmadd. apply rmone. apply rmid.
  rel. 
  rewrite /dom/=. lra. 
  by vm_compute.
Qed.

Goal close 69314718056 100000000000 10000000 (RInt (fun x => 1/(1+x)) 0 1). (* 0,69314718056 *)
  assert (d : IZR 0 < IZR 1) by lra. 
  eapply prove_close.
  apply (rmintegrate (B:=rescale (DfromZ2 d) chebyshev.basis)).
  apply (rmdiv 10). apply rmone. apply rmadd. apply rmone. apply rmid.
  intros. apply continuity_pt_div. by apply continuity_pt_const.
  apply continuity_pt_plus. by apply continuity_pt_const. apply continuity_pt_id.
  rewrite /dom /= in H. simpl; lra. 
  apply rfromZ.
  rewrite /dom/=. lra. 
  apply rfromZ.
  rewrite /dom/=. lra.
  by vm_compute.
Qed.

Definition calcul (C: Ops1) (F: FunOps C): C :=
  let f: F := div' 30 1 (cst pi+id) in
  integrate f 0 1.
Definition D01: Domain. apply (@DfromZ2 0 1). lra. Defined.

Eval vm_compute in calcul (MFunOps INBH (chebyshev.basis)).
Eval vm_compute in calcul (MFunOps INBH (rescale D01 chebyshev.basis)).

Goal let f x := 1/(pi+x) in close 276350 1000000 100 (RInt f 0 1).
  intro f.
  eapply prove_close.
  apply (rmintegrate (B:=rescale D01 chebyshev.basis)).
  apply (rmdiv 30). apply rmone. apply rmadd. apply rmcst. apply rpi. apply rmid.
  intros. apply continuity_pt_div. by apply continuity_pt_const.
  apply continuity_pt_plus. by apply continuity_pt_const. apply continuity_pt_id.
  rewrite /dom /= in H. generalize Rtrigo1.PI_RGT_0. simpl. lra. 
  apply rfromZ.
  rewrite /dom/=. lra. 
  apply rfromZ.
  rewrite /dom/=. lra.
  by vm_compute.
Qed.

Definition petit_calcul (C: Ops1) (F: FunOps C) :=
  let f: F := id in
  eval f 1.

Definition super_calcul (C: Ops1) (F: FunOps C) :=
  let a: C := pow 3 (1+1) in
  let f: F := div' 10 (id + cst a) (sqrt' 5 (id+cst a)) in
  let c := integrate f 0 1 in
  c + eval f (1//2).

Goal petit_calcul RFunOps = R1.
  reflexivity. 
Abort.

Goal forall {N: NBH},
    contains (petit_calcul (MFunOps N chebyshev.basis))
             (petit_calcul RFunOps).
Proof.
  intro. 
  rewrite /petit_calcul.
  apply rmeval. apply rmid. apply rone.
  rewrite /dom/=/chebyshev.lo/chebyshev.hi/=. lra. 
Qed.

Goal forall {N: NBH},
    contains (super_calcul (MFunOps N (taylor.basis D01)))
             (super_calcul RFunOps).
Proof.
  intro. 
  rewrite /super_calcul.
  apply radd. apply rmintegrate.
  apply rmdiv. apply rmadd. apply rmid. apply rmcst. rel.
  apply rmsqrt. apply rmadd. apply rmid. apply rmcst. rel. 
  intros. admit. 
  rel.
  rewrite /dom/=. lra.
  rel. 
  rewrite /dom/=. lra.
  apply rmeval. 2: rel.
  apply rmdiv. apply rmadd. apply rmid. apply rmcst. rel.
  apply rmsqrt. apply rmadd. apply rmid. apply rmcst. rel. 
  rewrite /dom/=. lra.
Abort.

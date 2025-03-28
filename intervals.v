(** * Implementation of neighborhoods based on floating point intervals from the Coq Interval library *)

Require Export Floats.
Require Export interfaces.
From Interval Require Import Xreal Interval Float Float_full.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** slight extension of Sig.FloatOps from Coq Interval *)
Module Type FloatOps'.
  (** the main signature *)
  Include Sig.FloatOps.
  (** fixed precision *)
  Parameter p: precision.
  (** unspecified operations on floating points (used for oracles) *)
  Parameter Eadd: type -> type -> type.
  Parameter Esub: type -> type -> type.
  Parameter Emul: type -> type -> type.
  Parameter Ediv: type -> type -> type.
  Parameter Esqrt: type -> type.
  Parameter Eone: type.
End FloatOps'. 


(** building a neighborhood instance out of the above interface *)
Module Make(F : FloatOps' with Definition sensible_format := true). 
Notation F := F.type.
Notation prec := F.p.

(** intervals *)
Module I := FloatIntervalFull F.
Notation I := (f_interval F).

Definition ImulZ z x := I.mul prec (I.fromZ prec z) x.
Definition IdivZ z x := I.div prec x (I.fromZ prec z).

Canonical Structure IOps0 :=
  {| car := I;
     add := I.add prec;
     mul := I.mul prec;
     mul' _ := I.mul prec;
     sub := I.sub prec;
     zer := I.zero;
     one := I.fromZ prec 1;
     mulZ := ImulZ;
     divZ := IdivZ;
  |}.

Definition Fle a b := match F.cmp a b with Xlt | Xeq => true | _ => false end.
Definition Flt a b := match F.cmp a b with Xlt => true | _ => false end.

Definition Imax (x: I): option I :=
  match x with
  | Ibnd a b =>
    if F.real b then
      match F.classify a with
      | Sig.Freal => if F.cmp b a is Xlt then None else Some (Ibnd b b)
      | Sig.Fminfty | Sig.Fnan => Some (Ibnd b b)
      | Sig.Fpinfty => None
      end
    else None
  | _ => None
  end.

Definition Imin (x: I): option I :=
  match x with
  | Ibnd a b =>
    if F.real a then
      match F.classify b with
      | Sig.Freal => if F.cmp b a is Xlt then None else Some (Ibnd a a)
      | Sig.Fpinfty | Sig.Fnan => Some (Ibnd a a)
      | Sig.Fminfty => None
      end
    else None
  | _ => None
  end.

Definition Ile (x y: I): bool :=
  match x,y with
  | Ibnd _ a,Ibnd b _  => Fle a b
  | _,_ => false
  end.

Definition Ilt (x y: I): bool :=
  match x,y with
  | Ibnd _ a,Ibnd b _  => Flt a b
  | _,_ => false
  end.

Definition Ibnd' (x y: I): I :=
  match x,y with
  | Ibnd a _, Ibnd _ b => Ibnd a b 
  | Ibnd a _, Inai => Ibnd a F.nan
  | Inai, Ibnd _ b => Ibnd F.nan b
  | _,_ => Inan
  end.

Canonical Structure IOps1 :=
  {| ops0 := IOps0;
     div := I.div prec;
     sqrt := I.sqrt prec;
     abs := I.abs;
     fromZ := I.fromZ prec;
     cos := I.cos prec;
     sin := I.sin prec;
     pi := I.pi prec;
  |}.

Definition FmulZ z := F.Emul (F.fromZ z).
Definition FdivZ z := let z := F.fromZ z in fun x => F.Ediv x z.
Canonical Structure FOps0 :=
  {| car := F;
     add := F.Eadd;
     mul := F.Emul;
     mul' _ := F.Emul;
     sub := F.Esub;
     zer := F.zero;
     one := F.Eone;
     mulZ := FmulZ;
     divZ := FdivZ;
  |}.

(* TOTHINK: we do not need certified cos/sin/pi, is there a faster way to get these values? *)
Definition Fcos x := I.midpoint (I.cos prec (I.bnd x x)).
Definition Fsin x := I.midpoint (I.sin prec (I.bnd x x)).
Definition Fpi := I.midpoint pi.
Canonical Structure FOps1 :=
  {| ops0  := FOps0;
     div   := F.Ediv;
     sqrt  := F.Esqrt;
     abs   := F.abs;
     fromZ := F.fromZ;
     cos   := Fcos;
     sin   := Fsin;
     pi    := Fpi; |}.

#[export] Instance Imem: inRel R I := fun x i => contains (I.convert i) (Xreal x).


Lemma ImulR: mul ∈ mul.
Proof. move=>?? H?? K. apply (I.mul_correct _ _ _ _ _ H K). Qed.

Lemma IdivR: div ∈ div.
Proof.
  move => j J Hj k K Hk.
  case: (Req_dec k 0) => Hk0.
+ move: Hk; rewrite !Hk0 /inrel /Imem /= => Hk.
  have H : I.convert (I.div prec J K) = Interval.Inan.
    apply contains_Xnan; replace Xnan with (Xdiv (Xreal j) (Xreal 0)); last by apply Xdiv_0_r.
    by apply I.div_correct.
  rewrite H; constructor.
+ rewrite /inrel /Imem /=.
  have H : Xreal (j / k) = Xdiv (Xreal j) (Xreal k).
    rewrite /= /Xdiv'; case is_zero_spec => H' //.
  by rewrite H; apply I.div_correct.
Qed.

Lemma IsqrtR: sqrt ∈ sqrt. 
Proof.
  move => j J Hj /=. rewrite  /inrel /Imem.
  move: (I.sqrt_correct prec J (Xreal j) Hj).
  rewrite /= /Xsqrt'; case: (is_negative_spec j) => Hj0 // H.
Qed.

Lemma IfromZR n: fromZ n ∈ fromZ n.
Proof. by apply I.fromZ_correct. Qed.

Definition IRel1: Rel1 Imem.
Proof.
  constructor. constructor. 
  - move=>?? H?? K. apply (I.add_correct _ _ _ _ _ H K). 
  - move=>?? H?? K. apply (I.sub_correct _ _ _ _ _ H K). 
  - exact ImulR.
  - move=>?. exact ImulR. 
  - now rewrite /inrel/Imem I.zero_correct/=.
  - apply I.fromZ_correct.
  - intros. apply ImulR=>//. apply IfromZR. 
  - intros. apply IdivR=>//. apply IfromZR.
  - exact IfromZR.
  - exact IdivR.
  - exact IsqrtR. 
  - move=>?? H. apply (I.abs_correct _ _ H).
  - move=>?? H. apply (I.cos_correct _ _ _ H).
  - move=>?? H. apply (I.sin_correct _ _ _ H).
  - apply I.pi_correct. 
Qed.

Lemma ImemE: forall x X, x ∈ X <->
                 match X with
                 | Inan => True
                 | Ibnd l u =>
                   F.valid_lb l /\ F.valid_ub u /\
                   match F.toX l, F.toX u with
                   | Xnan, Xnan => True
                   | Xreal l, Xnan => l<=x
                   | Xnan, Xreal u => x<=u
                   | Xreal l,Xreal u => l<=x<=u
                   end
                 end.
Proof.
  rewrite /inrel/Imem /I.convert /contains /= => x [|l u] //.
  case andP=>H. case F.toX; case F.toX; tauto. 
  case F.toX; case F.toX; intuition lra. 
Qed.

Lemma Iconvex x y Z: x ∈ Z -> y ∈ Z -> forall z, x<=z<=y -> z ∈ Z.
Proof.
  move => X Y z. revert X Y. rewrite 3!ImemE. 
  destruct Z as [|a b] => //=.
  case F.toX; case F.toX; intuition lra. 
Qed.

Lemma IfullE x : x ∈ I.nai.
Proof. by []. Qed.

Lemma IbndE x X y Y: x ∈ X -> y ∈ Y -> forall z, x<=z<=y -> z ∈ Ibnd' X Y. 
Proof.
  rewrite /inrel/Imem.
  destruct X as [|a a']; destruct Y as [|b b'];
    rewrite /= ?I.F'.nan_correct ?I.F'.valid_lb_nan ?I.F'.valid_ub_nan /=.
  - tauto.
  - case_eq (F.valid_lb b); intro Hb=>/=; 
    case_eq (F.valid_ub b'); intro Hb'=>/=; try lra.
    case (F.toX b); case (F.toX b'); intuition lra.
  - case_eq (F.valid_lb a); intro Ha=>/=;
    case_eq (F.valid_ub a'); intro Ha'=>/=; try lra.
    case (F.toX a); case (F.toX a'); intuition lra.
  - case_eq (F.valid_lb b); intro Hb=>/=; 
    case_eq (F.valid_ub b'); intro Hb'=>/=;
    case_eq (F.valid_lb a); intro Ha=>/=; 
    case_eq (F.valid_ub a'); intro Ha'=>/=; try lra.
    case (F.toX a); case (F.toX a'); 
    case (F.toX b); case (F.toX b'); intuition lra.
Qed.

Lemma ImaxE X: minmax_spec Rle X (Imax X).
Proof.
  (* TODO: super-ugly proof, do it again... *)
  rewrite /Imax.
  destruct X as [|a b]; first by constructor.
  case_eq (F.real b)=>Hb'.
  - have Hb: F.classify b = Sig.Freal.
     rewrite F.classify_correct in Hb'. destruct (F.classify b)=>//.
    case_eq (F.classify a)=>Ha.
    -- have Ha': F.real a by rewrite F.classify_correct Ha.
        rewrite F.cmp_correct Ha Hb.
        do 2 rewrite I.F'.real_correct//=.
        case Raux.Rcompare_spec=>C.
        --- constructor=> x y; rewrite /inrel/Imem/=.
            destruct (F.valid_lb a && F.valid_ub b)=>/=. 2: lra.
            do 2 rewrite I.F'.real_correct//. lra.
        --- apply minmax_spec_some with (F.toR b) =>[||x].
            rewrite /inrel/Imem/=F.valid_lb_correct Hb F.valid_ub_correct Hb/=.
            rewrite I.F'.real_correct//. lra.
            rewrite /inrel/Imem/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
            rewrite /inrel/Imem/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
        --- apply minmax_spec_some with (F.toR b) =>[||x].
            rewrite /inrel/Imem/=F.valid_lb_correct Hb F.valid_ub_correct Hb/=.
            rewrite I.F'.real_correct//. lra.
            rewrite /inrel/Imem/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
            rewrite /inrel/Imem/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
    -- have Ha': F.real a = false by rewrite F.classify_correct Ha.
       apply minmax_spec_some with (F.toR b) =>[||x].
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Hb/=.
       rewrite I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct_false// I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct_false// I.F'.real_correct//. intuition.
    -- have Ha': F.real a = false by rewrite F.classify_correct Ha.
       apply minmax_spec_some with (F.toR b) =>[||x].
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Hb/=.
       rewrite I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct_false// I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct_false// I.F'.real_correct//. intuition.
    -- constructor=>x y.
       rewrite ImemE. 
       rewrite F.valid_lb_correct Ha. intuition discriminate.
  - constructor=>x y; rewrite 2!ImemE. 
    rewrite (I.F'.real_correct_false b)//.
    case F.toX; intuition lra.
Qed.

Lemma IminE X: minmax_spec Rge X (Imin X).
  (* TODO: super-ugly proof, do it again... *)
  rewrite /Imin.
  destruct X as [|a b]; first by constructor.
  case_eq (F.real a)=>Ha'.
  - have Ha: F.classify a = Sig.Freal.
     rewrite F.classify_correct in Ha'. destruct (F.classify a)=>//.
    case_eq (F.classify b)=>Hb.
    -- have Hb': F.real b by rewrite F.classify_correct Hb.
        rewrite F.cmp_correct Ha Hb.
        do 2 rewrite I.F'.real_correct//=.
        case Raux.Rcompare_spec=>C.
        --- constructor=> x y; rewrite 2!ImemE.
            do 2 rewrite I.F'.real_correct//. intuition lra.
        --- apply minmax_spec_some with (F.toR a) =>[||x].
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha/=.
            rewrite I.F'.real_correct//. intuition.
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
            rewrite I.F'.real_correct// I.F'.real_correct//. intuition.
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
            rewrite I.F'.real_correct// I.F'.real_correct//. intuition.
        --- apply minmax_spec_some with (F.toR a) =>[||x].
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha/=.
            rewrite I.F'.real_correct//. intuition.
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
            rewrite I.F'.real_correct// I.F'.real_correct//. intuition.
            rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
            rewrite I.F'.real_correct// I.F'.real_correct//. intuition.
    -- have Hb': F.real b = false by rewrite F.classify_correct Hb.
       apply minmax_spec_some with (F.toR a) =>[||x].
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha/=.
       rewrite I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct// I.F'.real_correct_false//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct// I.F'.real_correct_false//. intuition.
    -- constructor=>x y.
       rewrite ImemE. 
       rewrite F.valid_ub_correct Hb. intuition discriminate.
    -- have Hb': F.real b = false by rewrite F.classify_correct Hb.
       apply minmax_spec_some with (F.toR a) =>[||x].
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha/=.
       rewrite I.F'.real_correct//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct// I.F'.real_correct_false//. intuition. 
       rewrite ImemE F.valid_lb_correct F.valid_ub_correct Ha Hb/=.
       rewrite I.F'.real_correct// I.F'.real_correct_false//. intuition.
  - constructor=>x y; rewrite 2!ImemE. 
    rewrite (I.F'.real_correct_false a)//.
    case F.toX; intuition lra.
Qed.

Lemma IleE X Y: Ile X Y ~> forall x y, x ∈ X -> y ∈ Y -> x <= y.
Proof.
  destruct X as [|a b]; destruct Y as [|c d]; try constructor.
  rewrite /Ile/Fle F.cmp_correct /=.
  case_eq (F.classify b)=>Hb; try constructor;
    case_eq (F.classify c)=>Hc; try constructor=>x y.
  rewrite I.F'.real_correct/=. 2: by rewrite F.classify_correct Hb.
  rewrite I.F'.real_correct/=. 2: by rewrite F.classify_correct Hc.
  case Raux.Rcompare_spec => H; constructor=>x y.
  - rewrite 2!ImemE.
    rewrite (I.F'.real_correct b)/=. 2: by rewrite F.classify_correct Hb.
    rewrite (I.F'.real_correct c)/=. 2: by rewrite F.classify_correct Hc.
    case F.toX; case F.toX; intuition lra.
  - rewrite 2!ImemE.
    rewrite (I.F'.real_correct b)/=. 2: by rewrite F.classify_correct Hb.
    rewrite (I.F'.real_correct c)/=. 2: by rewrite F.classify_correct Hc.
    case F.toX; case F.toX; intuition lra.
  - rewrite 2!ImemE.
    rewrite (F.valid_lb_correct c) Hc. intuition discriminate.  
  - rewrite ImemE.
    rewrite (F.valid_ub_correct b) Hb. intuition discriminate.  
  - rewrite ImemE.
    rewrite (F.valid_ub_correct b) Hb. intuition discriminate.  
  - rewrite ImemE.
    rewrite (F.valid_ub_correct b) Hb. intuition discriminate.  
  - rewrite 2!ImemE.
    rewrite (F.valid_lb_correct c) Hc. intuition discriminate.  
Qed.

Lemma IltE X Y: Ilt X Y ~> forall x y, x ∈ X -> y ∈ Y -> x < y.
Proof.
  destruct X as [|a b]; destruct Y as [|c d]; try constructor.
  rewrite /Ilt/Flt F.cmp_correct /=.
  case_eq (F.classify b)=>Hb; try constructor;
    case_eq (F.classify c)=>Hc; try constructor=>x y.
  rewrite I.F'.real_correct/=. 2: by rewrite F.classify_correct Hb.
  rewrite I.F'.real_correct/=. 2: by rewrite F.classify_correct Hc.
  case Raux.Rcompare_spec => H; constructor=>x y.
  - rewrite 2!ImemE.
    rewrite (I.F'.real_correct b)/=. 2: by rewrite F.classify_correct Hb.
    rewrite (I.F'.real_correct c)/=. 2: by rewrite F.classify_correct Hc.
    case F.toX; case F.toX; intuition lra.
  - rewrite 2!ImemE.
    rewrite (F.valid_lb_correct c) Hc. intuition discriminate.  
  - rewrite ImemE.
    rewrite (F.valid_ub_correct b) Hb. intuition discriminate.  
  - rewrite ImemE.
    rewrite (F.valid_ub_correct b) Hb. intuition discriminate.  
Qed.

Definition F2I (f: F): I :=
  match F.classify f with
  | Sig.Fpinfty | Sig.Fminfty => Inan
  | _ => Ibnd f f
  end.
Definition F2R (f: F): R := F.toR f.

Definition Iwidth (x: I): F :=
  match x with
  | Ibnd a b => b-a
  | _ => F.nan
  end.

Lemma Fsingle f: F2R f ∈ F2I f.
Proof.
  rewrite ImemE /F2I.
  case_eq (F.classify f)=>Hf//;
  rewrite F.valid_lb_correct F.valid_ub_correct Hf.
  rewrite I.F'.real_correct. 2: by rewrite F.classify_correct Hf. intuition. 
  rewrite I.F'.real_correct_false//. by rewrite F.classify_correct Hf. 
Qed.

Lemma classify_fromZ a: (Z.abs a <= 256)%Z -> F.classify (F.fromZ a) = Sig.Freal.
Proof.
  move=>H.  
  have H': F.real (F.fromZ a).  
  rewrite F.real_correct F.fromZ_correct//.
  rewrite F.classify_correct in H'. revert H'.
  by case F.classify.
Qed.

Lemma IbisectE X: (fun '(Y,Z) => forall x, x ∈ X -> x ∈ Y \/ x ∈ Z) (I.bisect X).
Proof. move: (I.bisect_correct X). case I.bisect=>Y Z H x. apply H. Qed.
  
#[global] Instance nbh: NBH.
exists IOps1 Imem Ibnd' Imax Imin Inan Ilt Ile I.bisect FOps1 F2I F2R.
Proof.
  - exact IRel1. 
  - apply Iconvex.
  - abstract (by intros; eapply IbndE; eauto).
  - apply ImaxE.
  - apply IminE.
  - apply IfullE.
  - apply IltE.
  - apply IleE.
  - apply IbisectE.
  - exact I.midpoint.
  - exact Fle.
  - exact Flt.
  - exact F.abs.
  - exact F.max.
  - exact Iwidth.
  - apply Fsingle.
Defined.

End Make.


From Interval Require Import Specific_bigint Specific_ops Primitive_ops Generic_ops Specific_stdz.
Import BigZ.

Module Type FloatCarrierP.
  Include Specific_sig.FloatCarrier.
  Parameter p: exponent_type.
End FloatCarrierP. 

Module SpecificFloat(Carrier: FloatCarrierP) <: FloatOps'.
  Include Specific_ops.SpecificFloat Carrier.
  Definition p := Carrier.p. 
  Definition Eadd := add_slow Basic.rnd_NE p.
  Definition Esub x y := Eadd x (neg y).
  Definition Emul := mul Basic.rnd_NE p.
  Definition Ediv := div Basic.rnd_NE p.
  Definition Esqrt := sqrt Basic.rnd_NE p.
  Definition Eone := fromZ 1.
End SpecificFloat.

Module PrimitiveFloat <: FloatOps'.
  Include Primitive_ops.PrimitiveFloat.
  Definition p := 53%Z.
  (* TOREPORT: strange bug, 
     if the following definitions are not eta-expanded, 
     then vm_compute refuses to unfold them once packed in [FOps0/1] above (see below) *)
  Definition Eadd x y := PrimFloat.add x y.
  Definition Esub x y := PrimFloat.sub x y.
  Definition Emul x y := PrimFloat.mul x y.
  Definition Ediv x y := PrimFloat.div x y.
  Definition Esqrt x := PrimFloat.sqrt x.
  Definition Eone := PrimFloat.one.
End PrimitiveFloat.

(** encoded floating points, using Z for integers 
   (axiom-free slow) *)
Module StdZRadix2_60 <: FloatCarrierP.
  Include StdZRadix2.
  Definition p := 60%Z.
End StdZRadix2_60.
Module FStdZ60 := SpecificFloat StdZRadix2_60.
Module IStdZ60 := Make FStdZ60.

Module StdZRadix2_120 <: FloatCarrierP.
  Include StdZRadix2.
  Definition p := 120%Z.
End StdZRadix2_120.
Module FStdZ120 := SpecificFloat StdZRadix2_120.
Module IStdZ120 := Make FStdZ120.

(** half-encoded floating points, using primitive integers (int63) 
   (some axioms, intermediate) *)
Module BigInt60 <: FloatCarrierP.
  Include BigIntRadix2.
  Definition p := 60%bigZ.
End BigInt60. 
Module FBigInt60 := SpecificFloat BigInt60.
Module IBigInt60 := Make FBigInt60.

Module BigInt120 <: FloatCarrierP.
  Include BigIntRadix2.
  Definition p := 120%bigZ.
End BigInt120. 
Module FBigInt120 := SpecificFloat BigInt120.
Module IBigInt120 := Make FBigInt120.

Module BigInt300 <: FloatCarrierP.
  Include BigIntRadix2.
  Definition p := 300%bigZ.
End BigInt300. 
Module FBigInt300 := SpecificFloat BigInt300.
Module IBigInt300 := Make FBigInt300.

(** primitive (machine) floating points 
   (more axioms, fast) *)
Module IPrimFloat := Make PrimitiveFloat.


(* tests for the aformentioned bug to report *)
(*
Eval vm_compute in (PrimitiveFloat.Eadd 1 1).     (* reduces *)
Eval vm_compute in (@add IPrimFloat.FOps0 1 1).   (* blocked unless eta-expanded *)
Eval vm_compute in (@add IPrimFloat.FOps0).       (* reduces to [PrimFloat.add] *)
Eval vm_compute in (PrimFloat.add 1 1).           (* reduces *)
Eval cbv in (@add IPrimFloat.FOps0 1 1).          (* reduces *)
Eval hnf in (@add IPrimFloat.FOps0 1 1).          (* anomaly, please report (with eta-expansion or not) *)
*)  

(** canonical structures for floating point operations *)
Definition PFmulZ z x := PrimFloat.mul (PrimitiveFloat.fromZ z) x.
Definition PFdivZ z x := PrimFloat.div x (PrimitiveFloat.fromZ z).
Canonical Structure FOps0 :=
  {| car := float;
     add := PrimFloat.add;
     mul := PrimFloat.mul;
     mul' _ := PrimFloat.mul;
     sub := PrimFloat.sub;
     zer := PrimFloat.zero;
     one := PrimFloat.one;
     mulZ := PFmulZ;
     divZ := PFdivZ;
  |}.

Definition Fpi := 0x1.921fb54442d18p+1%float.
Canonical Structure FOps1 :=
  {| ops0 := FOps0;
     div := PrimFloat.div;
     sqrt := PrimFloat.sqrt;
     abs := PrimFloat.abs;
     fromZ := PrimitiveFloat.fromZ;
     cos := @cos IPrimFloat.FOps1;
     sin := @sin IPrimFloat.FOps1;
     pi := @pi IPrimFloat.FOps1;
  |}.

(* tests continued: if we simply use the above structures (not the ones generated by the functor Make),
   then it just works *)
(*
Set Printing All.
Check (sqrt (1+1): float).
Eval vm_compute in (sqrt (1+1): float). (* reduces *)
 *)

(** nice notation for intervals with primitive floating points endpoints *)
Notation "[[ a ; b ]]" := (Float.Ibnd a%float b%float). 

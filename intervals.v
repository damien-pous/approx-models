(** * Implementation of neighborhoods based on floating point intervals *)

Require Export Floats.
Require Export neighborhood.
From Interval Require Import Xreal Interval Float Float_full.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type FloatOpsP.
  Include Sig.FloatOps with Definition sensible_format := true.
  Parameter p: precision.
End FloatOpsP. 


(** floating points *)
Module Make(F : FloatOpsP). 
Notation F := F.type.
Notation prec := F.p.

(** intervals *)
Module I := FloatIntervalFull F.
Notation I := (f_interval F).

Canonical Structure IOps0 :=
  {| car := I;
     add := I.add prec;
     mul := I.mul prec;
     sub := I.sub prec;
     zer := I.zero;
     one := I.fromZ prec 1 |}.

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

Definition subseteq (X: I) (a b: R) :=
  match X with
  | Ibnd x y => match F.toX x, F.toX y with
                | Xreal x, Xreal y => a <= x /\ y <= b
                | _,_ => False
                end                 
  | _ => False
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
     pi := I.pi prec;
  |}.

Canonical Structure FOps0 := Eval hnf in 
  {| car := F;
     add := F.add_UP prec;
     mul := F.mul_UP prec;
     sub := F.sub_UP prec;
     zer := F.zero;
     one := F.fromZ 1 |}.

Definition Fcos x := I.midpoint (I.cos prec (I.bnd x x)). 
Definition Fpi := I.midpoint pi. 

Canonical Structure FOps1 := Eval hnf in
  {| ops0 := FOps0;
     div := F.div_UP prec;
     sqrt := F.sqrt_UP prec;
     abs := F.abs;
     fromZ := F.fromZ;
     cos := Fcos;
     pi := Fpi;
  |}.

Definition Icontains i x := contains (I.convert i) (Xreal x).
Local Notation Imem x i := (Icontains i x).

Lemma Iradd i x (H: Imem x i) j y (K: Imem y j): Imem (x+y) (i+j).
Proof. apply (I.add_correct _ _ _ _ _ H K). Qed.

Lemma Irmul i x (H: Imem x i) j y (K: Imem y j): Imem (x*y) (i*j).
Proof. apply (I.mul_correct _ _ _ _ _ H K). Qed.

Lemma Irsub i x (H: Imem x i) j y (K: Imem y j): Imem (x-y) (i-j).
Proof. apply (I.sub_correct _ _ _ _ _ H K). Qed.

Lemma Irzer: Imem 0 0.
Proof. unfold Icontains. now rewrite I.zero_correct. Qed.

Lemma Irone: Imem 1 1.
Proof. apply I.fromZ_correct. Qed.

Canonical Structure IRel0 :=
  {| rel := Icontains;
     radd := Iradd;
     rmul := Irmul;
     rsub := Irsub;
     rzer := Irzer;
     rone := Irone |}.

Lemma Irdiv J j: Imem j J -> forall K k, Imem k K -> Imem (j / k) (J / K).
Proof.
  move => Hj K k Hk.
  case: (Req_dec k 0) => Hk0.
+ move: Hk; rewrite !Hk0 /mem /= /Icontains => Hk.
  have H : I.convert (I.div prec J K) = Interval.Inan.
    apply contains_Xnan; replace Xnan with (Xdiv (Xreal j) (Xreal 0)); last by apply Xdiv_0_r.
    by apply I.div_correct.
  rewrite H; constructor.
+ rewrite /mem /= /Icontains.
  have H : Xreal (j / k) = Xdiv (Xreal j) (Xreal k).
    rewrite /= /Xdiv'; case is_zero_spec => H' //.
  by rewrite H; apply I.div_correct.
Qed.

Lemma Irsqrt J j: Imem j J -> Imem (sqrt j) (sqrt J).
Proof.
  move => Hj /=; rewrite /Icontains.
  move: (I.sqrt_correct prec J (Xreal j) Hj).
  rewrite /= /Xsqrt'; case: (is_negative_spec j) => Hj0 // H.
Qed.

Lemma Irabs i x (H: Imem x i): Imem (abs x) (abs i).
Proof. apply (I.abs_correct _ _ H). Qed.

Lemma Ircos i x (H: Imem x i): Imem (cos x) (cos i).
Proof. apply (I.cos_correct prec _ _ H). Qed.

Lemma IrfromZ n: Imem (fromZ n) (fromZ n).
Proof. by apply I.fromZ_correct. Qed.

Canonical Structure IRel1 :=
  {| rel0 := IRel0;
     rdiv := Irdiv;
     rsqrt := Irsqrt;
     rabs := Irabs;
     rcos := Ircos;
     rpi := I.pi_correct prec;
     rfromZ := IrfromZ |}.

Lemma ImemE: forall x X, Imem x X <->
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
  rewrite /Icontains /I.convert /contains /= => x [|l u] //.
  case andP=>H. case F.toX; case F.toX; tauto. 
  case F.toX; case F.toX; intuition lra. 
Qed.

Lemma Iconvex Z x y: Imem x Z -> Imem y Z -> forall z, x<=z<=y -> Imem z Z.
Proof.
  move => X Y z. revert X Y. rewrite 3!ImemE. 
  destruct Z as [|a b] => //=.
  case F.toX; case F.toX; intuition lra. 
Qed.

Lemma IbotE x : Imem x I.nai.
Proof. rewrite /mem /bot /= /Icontains I.nai_correct; constructor. Qed.

Lemma IbndE X x Y y: Imem x X -> Imem y Y -> forall z, x<=z<=y -> Imem z (Ibnd' X Y). 
Proof.
  unfold Icontains.
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

Lemma ImaxE X: minmax_spec Rle Icontains X (Imax X).
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
        --- constructor=> x y; rewrite /Icontains/=.
            destruct (F.valid_lb a && F.valid_ub b)=>/=. 2: lra.
            do 2 rewrite I.F'.real_correct//. lra.
        --- apply minmax_spec_some with (F.toR b) =>[||x].
            rewrite /Icontains/=F.valid_lb_correct Hb F.valid_ub_correct Hb/=.
            rewrite I.F'.real_correct//. lra.
            rewrite /Icontains/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
            rewrite /Icontains/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
        --- apply minmax_spec_some with (F.toR b) =>[||x].
            rewrite /Icontains/=F.valid_lb_correct Hb F.valid_ub_correct Hb/=.
            rewrite I.F'.real_correct//. lra.
            rewrite /Icontains/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
            do 2 rewrite I.F'.real_correct//. lra.
            rewrite /Icontains/=F.valid_lb_correct Ha F.valid_ub_correct Hb/=.
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

Lemma IminE X: minmax_spec Rge Icontains X (Imin X).
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

Lemma IleE X Y: wreflect (forall x y, Imem x X -> Imem y Y -> x <= y) (Ile X Y).
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

Lemma IltE X Y: wreflect (forall x y, Imem x X -> Imem y Y -> x < y) (Ilt X Y).
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

Definition width (x: I): F :=
  match x with
  | Ibnd a b => b-a
  | _ => F.nan
  end.

Lemma Fsingle f: Imem (F2R f) (F2I f).
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

Lemma subseteqE X a b: subseteq X a b -> forall x, Imem x X -> a <= x <= b.
Proof.
  intros H x. revert H. destruct X as [|l u]=>//=.
  rewrite ImemE. case F.toX=> l'//. case F.toX=> u'//. lra. 
Qed.

Instance nbh: NBH.
exists IOps1 IRel1 Ibnd' Imax Imin Inan Ilt Ile FOps1 F2I F2R subseteq.
Proof.
  - apply Iconvex.
  - abstract (by intros; eapply IbndE; eauto).
  - apply ImaxE.
  - apply IminE.
  - apply IbotE.
  - apply IltE.
  - apply IleE.
  - exact I.midpoint.
  - exact width.
  - apply Fsingle.
  - apply subseteqE.
Defined.

End Make.


From Interval Require Import Specific_bigint Specific_ops Primitive_ops Generic_ops Specific_stdz.
Import BigZ.

(** encoded floating points, using Z for integers 
   (axiom-free slow) *)
Module FZ <: FloatOpsP.
  Include SpecificFloat StdZRadix2.
  Definition p := 64%Z.
End FZ.
 
(** half-encoded floating points, using primitive integers (int63) 
   (some axioms, intermediate) *)
Module FBigInt <: FloatOpsP.
  Include SpecificFloat BigIntRadix2.
  Definition p := 64%bigZ.
End FBigInt. 

(** primitive (machine) floating points 
   (more axioms, fast) *)
Module Fprimitive <: FloatOpsP.
  Include PrimitiveFloat.
  Definition p := 64%Z.
End Fprimitive. 

(** corresponding implementations of intervals *)
Module IBigInt := Make FBigInt.
Module IZ := Make FZ.
Module Iprimitive := Make Fprimitive.


(** canonical structures for floating point operations *)
Canonical Structure FOps0 :=
  {| car := float;
     add := PrimFloat.add;
     mul := PrimFloat.mul;
     sub := PrimFloat.sub;
     zer := PrimFloat.zero;
     one := PrimFloat.one |}.

Definition Fpi := 0x1.921fb54442d18p+1%float.
Canonical Structure FOps1 :=
  {| ops0 := FOps0;
     div := PrimFloat.div;
     sqrt := PrimFloat.sqrt;
     abs := PrimFloat.abs;
     fromZ := PrimitiveFloat.fromZ;
     cos := @cos Iprimitive.FOps1;
     pi := @pi Iprimitive.FOps1;
  |}.

(** nice notation for intervals *)
Notation "[[ a ; b ]]" := (Float.Ibnd a%float b%float). 

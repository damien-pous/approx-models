(** * Implementation of neighborhoods based on floating point intervals *)

Require Import neighborhood.
From Bignums Require Import BigZ.
From Interval Require Import Interval_bigint_carrier Interval_definitions Interval_xreal Interval_interval Interval_interval_float Interval_interval_float_full Interval_specific_ops .
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** floating points *)
Module F := SpecificFloat BigIntRadix2.
Notation F := F.type.

(** intervals *)
Module I := FloatIntervalFull F.
Notation I := (f_interval F).

Section p.
Variable prec: bigZ.

Canonical Structure IOps0 :=
  {| car := I;
     add := I.add prec;
     mul := I.mul prec;
     sub := I.sub prec;
     zer := I.zero;
     one := I.fromZ 1 |}.

Definition Imax (x: I): option I :=
  match x with
  | Ibnd a b =>
    if F.real b then
      if F.real a then
        match F.cmp a b with Xeq | Xlt => Some (Ibnd b b) | _ => None end
      else Some (Ibnd b b)
    else None
  | _ => None
  end.

Definition Imin (x: I): option I :=
  match x with
  | Ibnd a b =>
    if F.real a then
      if F.real b then
        match F.cmp a b with Xeq | Xlt => Some (Ibnd a a) | _ => None end
      else Some (Ibnd a a)
    else None
  | _ => None
  end.

Definition Ilt (x y: I): bool :=
  match x,y with
  | Ibnd _ a,Ibnd b _  => if F.cmp a b is Xlt then true else false
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
     fromZ := I.fromZ;
     cos := I.cos prec;
     pi := I.pi prec;
  |}.

Canonical Structure FOps0 :=
  {| car := F;
     add := F.add rnd_NE prec;
     mul := F.mul rnd_NE prec;
     sub := F.sub rnd_NE prec;
     zer := F.zero;
     one := F.fromZ 1 |}.

Canonical Structure FOps1 :=
  {| ops0 := FOps0;
     div := F.div rnd_NE prec;
     sqrt := F.sqrt rnd_NE prec;
     abs := F.abs;
     fromZ := F.fromZ;
     cos x := I.midpoint (I.cos prec (I.bnd x x));
     pi := I.midpoint pi;
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
Proof. cbv. tauto. Qed.

Lemma Irone: Imem 1 1.
Proof. cbv. tauto. Qed.

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
  have H : I.convert (I.div prec J K) = Interval.Interval_interval.Inan.
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
  have H' : I.convert (I.sqrt prec J) = Interval.Interval_interval.Inan
    by apply contains_Xnan.
  rewrite H'; constructor.
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

Lemma Iconvex Z x y: Imem x Z -> Imem y Z -> forall z, x<=z<=y -> Imem z Z.
Proof.
  rewrite /Icontains. 
  destruct Z as [|a b] => //=.
  case F.toX; case F.toX; intuition lra. 
Qed.

Lemma IbotE x : Imem x I.nai.
Proof. rewrite /mem /bot /= /Icontains I.nai_correct; constructor. Qed.

Inductive Icontains': I -> R -> Prop :=
| Icontains_: forall x, Icontains' I.nai x 
| Icontains__: forall x, Icontains' (I.bnd F.nan F.nan) x 
| Icontains_l: forall l l' x, l <= x -> F.toX l' = Xreal l -> Icontains' (Ibnd l' F.nan) x 
| Icontains_r: forall r r' x, x <= r -> F.toX r' = Xreal r -> Icontains' (Ibnd F.nan r') x 
| Icontains_lr: forall l l' r r' x, l <= x <= r -> F.toX l' = Xreal l -> F.toX r' = Xreal r -> Icontains' (Ibnd l' r') x.
Lemma FtoXnan x: F.toX x = Xnan -> x = F.nan.
Proof.
  destruct x =>//. rewrite /F.toX/F.toF.
  case BigIntRadix2.mantissa_sign =>//.
Qed.
Lemma containsE i x: Icontains' i x <-> Icontains i x.
Proof.
  rewrite /Icontains. split.
  by destruct 1 as [ | |???? E|???? E|?????? E E'] => //=; rewrite ?E ?E'.   
  destruct i as [|l' r']=>/=. constructor.
  case_eq (F.toX l')=>[L|l L]; first rewrite (FtoXnan L); 
  (case_eq (F.toX r')=>[R|r R]; first rewrite (FtoXnan R)); econstructor; eauto; tauto.
Qed.

Lemma IbndE X x Y y: Imem x X -> Imem y Y -> forall z, x<=z<=y -> Imem z (Ibnd' X Y). 
Proof.
  setoid_rewrite <-containsE.
  destruct 1; destruct 1; intros=>/=; try (econstructor; eauto; lra). 
  apply Icontains_lr with l r =>//. lra. 
  apply Icontains_lr with l r =>//. lra. 
  apply Icontains_lr with l r0 =>//. lra. 
  apply Icontains_lr with l r0 =>//. lra. 
Qed.

Lemma ImaxE X: minmax_spec Rle Icontains X (Imax X).
Proof.
  rewrite /Imax.
  destruct X as [|a b]; first by constructor.
  rewrite 2!F.real_correct F.cmp_correct.
  case_eq (F.toX b) => [|b'] B;
  case_eq (F.toX a) => [|a'] A/=; 
  try (constructor => x y; rewrite /Icontains/=?A?B => //; intuition lra). 
  apply minmax_spec_some with b' =>[||?]; rewrite /Icontains/=?A?B; lra.
  case Raux.Rcompare_spec => H; try
  (apply minmax_spec_some with b' =>[||?]; rewrite /Icontains/=?A?B; lra).
  constructor => x y; rewrite /Icontains/=?A?B => //; intuition lra.
Qed.

Lemma IminE X: minmax_spec Rge Icontains X (Imin X).
Proof. 
  rewrite /Imin/Imax/=.
  destruct X as [|a b]. by constructor.
  rewrite 2!F.real_correct F.cmp_correct.
  case_eq (F.toX b) => [|b'] B;
  case_eq (F.toX a) => [|a'] A/=; 
  try (constructor => x y; rewrite /Icontains/=?A?B => //; intuition lra). 
  apply minmax_spec_some with a' =>[||?]; rewrite /Icontains/=?A?B; lra.
  case Raux.Rcompare_spec => H; try
  (apply minmax_spec_some with a' =>[||?]; rewrite /Icontains/=?A?B; lra).
  constructor => x y; rewrite /Icontains/=?A?B => //. simpl. lra.
Qed.

Lemma IltE X Y: wreflect (forall x y, Imem x X -> Imem y Y -> x < y) (Ilt X Y).
Proof.
  destruct X as [|a b]; destruct Y as [|c d]; try constructor.
  rewrite /Ilt F.cmp_correct /=.
  case_eq (F.toX b) => [|b' B]. constructor.  
  case_eq (F.toX c) => [|c' C]/=. constructor.
  case Raux.Rcompare_spec => H; constructor.
  rewrite /Icontains/= B C=> x y.
  case F.toX; case F.toX; intuition lra.
Qed.

Instance INBH: NBH :=
  {| neighborhood.contains := IRel1;
     bnd := Ibnd';
     max := Imax;
     min := Imin;
     bot := Inan;
     is_lt := Ilt;
     FF := FOps1;
     I2F := I.midpoint;
     F2I f := Ibnd f f;
     F2R := I.T.toR |}.
Proof.
  - apply Iconvex.
  - abstract (by intros; eapply IbndE; eauto).
  - apply ImaxE.
  - apply IminE.
  - apply IbotE.
  - apply IltE.
  - abstract (rewrite /=/Icontains/=/I.T.toR=>f; case F.toX=>//; split; reflexivity).
Defined.

End p.

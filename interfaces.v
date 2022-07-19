(** * Hierarchy of structures: basic operations, operations on functions, neighbourhoods *)

Require Export QArith_base Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
Require Export List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.
Require Export errors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Close Scope Q_scope.
Open Scope R_scope.

(** ** preliminary tools *)

(** instances for setoid_rewriting on Rle *)
#[export] Instance Rle_PreOrder: PreOrder Rle.
Proof. constructor; cbv; intros; lra. Qed.
#[export] Instance Rlt_PreOrder: Transitive Rlt. 
Proof. cbv; intros; lra. Qed.
#[export] Instance Rlt_Rle: subrelation Rlt Rle.
Proof. cbv. tauto. Qed.
#[export] Instance Rplus_Rle: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. repeat intro. lra. Qed.

(** a few notations for natural numbers *)
Notation "n .-1" := (Nat.pred n) (at level 2) : nat_scope.
Notation "n .+1" := (S n) (at level 2) : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2) : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2) : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2) : nat_scope.
Notation "n .+5" := n.+1.+4 (at level 2) : nat_scope.

(** injection from natural numbers to real numbers  *)
Notation INRS := S_INR.
Lemma INR0: INR O = 0. Proof. reflexivity. Qed.

(** blocking identity to document irrelevant values *)
Lemma IRRELEVANT (A: Type): A -> A.
Proof. by []. Qed. 



(** ** operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, list C, Tube C) *)
Record Ops0 := {
  car:> Type;
  add: car -> car -> car;
  sub: car -> car -> car;
  mul: car -> car -> car;
  mul': Z -> car -> car -> car;    (* (potentially) truncated multiplication *)
  zer: car;
  one: car;
  mulZ: Z -> car -> car;
  divZ: Z -> car -> car;
}.

(** extended operations *)
(** (will be instantiated on R, I, F) *)
Record Ops1 := {
  ops0:> Ops0;
  fromZ: Z -> ops0;
  div: ops0 -> ops0 -> ops0;  (** also on Tube C, but with parameters *)
  sqrt: ops0 -> ops0;         (** idem *)
  cos: ops0 -> ops0;
  sin: ops0 -> ops0;
  abs: ops0 -> ops0;
  pi: ops0;
}.

(** notations *)
Declare Scope RO_scope.
Bind Scope RO_scope with car.
Infix "+" := add: RO_scope. 
Infix "*" := mul: RO_scope.
Notation "a *[ d  ] b" := (mul' d a b) (at level 40, left associativity): RO_scope.
Infix "-" := sub: RO_scope.
Infix "/" := div: RO_scope.
Notation "0" := (zer _): RO_scope.
Notation "1" := (one _): RO_scope.
Arguments fromZ {_}. 
Arguments mulZ {_}. 
Arguments divZ {_}. 
Arguments sqrt {_}. 
Arguments cos {_}. 
Arguments sin {_}. 
Arguments abs {_}. 
Arguments pi {_}. 
Open Scope RO_scope.

(** derived operations *)
Definition fromN {C: Ops1} (n: nat): C := fromZ (Z.of_nat n). 
Definition fromQ {C: Ops1} (q: Q): C := divZ (Zpos (Qden q)) (fromZ (Qnum q)).
Definition mulN {C: Ops0} n: C -> C := mulZ (Z.of_nat n).
Definition divN {C: Ops0} n: C -> C := divZ (Z.of_nat n).
Notation "x // n" := (divN n x) (at level 40, left associativity): RO_scope .

(* TOTHINK: powN, powP? *)
Fixpoint pow (C: Ops0) n (x: C) :=
  match n with
  | O => 1
  | S n => x*pow n x
  end.


(** ** lifting to functions *)
Definition f_cst A B (b: B) (a: A) := b.
Definition f_unr A B (o: B -> B) (f: A -> B) (a: A) := o (f a).
Definition f_bin A B (o: B -> B -> B) (f g: A -> B) (a: A) := o (f a) (g a).
Canonical Structure f_Ops0 (A: Type) (C: Ops0): Ops0 := {|
  car := A -> C;
  add := f_bin (@add C);
  sub := f_bin (@sub C);
  mul := f_bin (@mul C);
  mul' z := f_bin (mul' z);
  zer := f_cst (@zer C);
  one := f_cst (@one C);
  mulZ z := f_unr (mulZ z);
  divZ z := f_unr (divZ z);
|}.

(** tagged multiplication on reals, to indicate truncated multiplication request *)
Definition Rmult' (d: Z) := Rmult.
(** other tagged identities, to indicate truncations/requested degrees *)
Definition Rtruncate (d: Z) (x: R) := x.
Definition at_degree (d: Z) [A] (x: A) := x.

(** ** instances on real numbers *)
Canonical Structure ROps0 := {|
  car := R;
  add := Rplus;
  sub := Rminus;
  mul := Rmult;
  mul' := Rmult';
  zer := R0;
  one := R1;
  mulZ z x := Rmult (IZR z) x;
  divZ z x := Rdiv x (IZR z);
|}.
Canonical Structure ROps1 := {|
  ops0 := ROps0;
  fromZ := IZR;
  div := Rdiv;
  sqrt := R_sqrt.sqrt;
  cos := Rtrigo_def.cos;
  sin := Rtrigo_def.sin;
  abs := Rabs;
  pi := Rtrigo1.PI;
|}.

Lemma RfromN: forall n, INR n = fromN n.
Proof INR_IZR_INZ.
Lemma RfromQ: forall q, Q2R q = fromQ q.
Proof. reflexivity. Qed.
Lemma RmulZ x z: IZR z * x = mulZ z x.
Proof. reflexivity. Qed.
Lemma RmulN x n: INR n * x = mulN n x.
Proof. cbn. now rewrite RfromN. Qed.
Lemma RdivZ x z: x / IZR z = divZ z x.
Proof. reflexivity. Qed.
Lemma RdivN x n: x / INR n = divN n x.
Proof. cbn. now rewrite RfromN. Qed.

Lemma Rpow n x: x^n = pow n x.
Proof. induction n=>//=. congruence. Qed.

(** ** parametricity relations *)
Record Rel0 (R S: Ops0) := {
  rel:> R -> S -> Prop;
  radd: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x+x') (y+y');
  rsub: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x-x') (y-y');
  rmul: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x*x') (y*y');
  (* note that we relate truncated multiplication to plain multiplication *)  
  rmul': forall d x y, rel x y -> forall x' y', rel x' y' -> rel (x*[d]x') (y*y'); 
  rzer: rel 0 0;
  rone: rel 1 1;
  rmulZ: forall z x y, rel x y -> rel (mulZ z x) (mulZ z y);
  rdivZ: forall z x y, rel x y -> rel (divZ z x) (divZ z y);
}.
Record Rel1 (R S: Ops1) := {
  rel0:> Rel0 R S;
  rfromZ: forall z, rel0 (fromZ z) (fromZ z);
  rdiv: forall x y, rel0 x y -> forall x' y', rel0 x' y' -> rel0 (x/x') (y/y');
  rsqrt: forall x y, rel0 x y -> rel0 (sqrt x) (sqrt y);
  rabs: forall x y, rel0 x y -> rel0 (abs x) (abs y);
  rcos: forall x y, rel0 x y -> rel0 (cos x) (cos y);
  rsin: forall x y, rel0 x y -> rel0 (sin x) (sin y);
  rpi: rel0 pi pi;
}.
Create HintDb rel discriminated.
Global Hint Resolve radd rsub rmul rmul' rfromZ rmulZ rdivZ rzer rone rdiv rsqrt rabs rcos rsin rpi: rel.
Ltac rel := by eauto 100 with rel.

(** parametricity of derived operations *)
Lemma rpow R S (T: Rel0 R S) n: forall x y, T x y -> T (pow n x) (pow n y).
Proof. induction n; simpl; rel. Qed.
Global Hint Resolve rpow: rel.

Lemma rfromN R S (T: Rel1 R S) n: T (fromN n) (fromN n).
Proof. unfold fromN; rel. Qed.
Global Hint Resolve rfromN: rel.

Lemma rfromQ R S (T: Rel1 R S) q: T (fromQ q) (fromQ q).
Proof. unfold fromQ; rel. Qed.
Global Hint Resolve rfromQ: rel.

Lemma rmulN R S (T: Rel0 R S) n x y: T x y -> T (mulN n x) (mulN n y).
Proof. apply rmulZ. Qed.
Global Hint Resolve rmulN: rel.

Lemma rdivN R S (T: Rel0 R S) n x y: T x y -> T (divN n x) (divN n y).
Proof. apply rdivZ. Qed.
Global Hint Resolve rdivN: rel.


(** ** neighborhoods (effective abstractions for real numbers) *)

(** utilities for specifications *)
Variant minmax_spec A le (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| minmax_spec_some: forall m b, contains m b -> contains a b -> (forall x, contains a x -> le x b) -> minmax_spec le contains a (Some m)
| minmax_spec_none: (forall x y, contains a x -> le x y -> contains a y)-> minmax_spec le contains a None.

Variant wreflect (P : Prop): bool -> Prop :=
 | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.
Lemma wreflectE {P b}: wreflect P b -> b -> P.
Proof. by case. Qed.

(** neighborhoods: an abstract interface for computing with floating points and intervals 
    convention: 
    - uppercase letters for intervals, lowercase letters for real numbers
    - same letter when a real is assumed to belong to an interval: 
      y: R, Y: II   often means that we also have   H: contains Y y. *)
Class NBH := {
  (** intervals *)
  II: Ops1;
  (** (parametric) containment relation *)
  contains: Rel1 II ROps1;
  (** convexity of intervals  *)
  convex: forall Z x y, contains Z x -> contains Z y -> forall z, x<=z<=y -> contains Z z;
  (** additional operations on intervals *)
  bnd: II -> II -> II;        (** `directed' convex hull *)
  max: II -> option II;    
  min: II -> option II;    
  bot: II;                   (** [[-oo;+oo]] *)
  is_lt: II -> II -> bool; 
  is_le: II -> II -> bool;
  (** specification of the above operations; 
      together with convexity, [maxE] and [minE] entail that the elements of II always represent closed intervals *)
  bndE: forall X x, contains X x -> forall Y y, contains Y y -> forall z, x<=z<=y -> contains (bnd X Y) z;
  maxE: forall X, minmax_spec Rle contains X (max X);
  minE: forall X, minmax_spec Rge contains X (min X);
  botE: forall x, contains bot x;
  is_ltE: forall X Y, wreflect (forall x y, contains X x -> contains Y y -> x<y) (is_lt X Y);
  is_leE: forall X Y, wreflect (forall x y, contains X x -> contains Y y -> x<=y) (is_le X Y);
  (** (almost unspecified) floating point operations *)
  FF: Ops1;
  I2F: II -> FF;
  F2I: FF -> II;
  Fle: FF -> FF -> bool;
  Flt: FF -> FF -> bool;
  Fabs: FF -> FF;
  Fmax: FF -> FF -> FF;
  width: II -> FF;  (** width of an interval (unspecified, just for inspection) *)
  F2R: FF -> R;   (** needed to guarantee that F2I produces non-empty intervals *)
  F2IE: forall f, contains (F2I f) (F2R f);
}.
Coercion II: NBH >-> Ops1.
Global Hint Resolve F2IE: rel.

(** derived operations and their specification *)
Definition mag {N: NBH} x: option II := max (abs x).
Definition sym {N: NBH} x: II := let x := abs x in bnd (0-x) x.

Variant mag_spec A (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| mag_spec_some: forall m b, contains m b -> (forall x, contains a x -> Rabs x <= b) -> mag_spec contains a (Some m)
| mag_spec_none: mag_spec contains a None.

Lemma magE {N: NBH} X: mag_spec contains X (mag X).
Proof. rewrite /mag. case: maxE; econstructor; eauto; rel. Qed.

Lemma symE {N: NBH} x y I: Rabs x <= y -> contains I y -> contains (sym I) x.
Proof.
  intros Hx Hy. rewrite /sym. apply bndE with (0-abs y) (abs y); try rel. 
  simpl; split_Rabs; lra.
Qed.

Definition is_ne {N: NBH} X Y := if is_lt X Y then true else is_lt Y X.
Lemma is_neE {N: NBH} X Y: wreflect (forall x y, contains X x -> contains Y y -> x<>y) (is_ne X Y).
Proof.
  rewrite /is_ne. case is_ltE=>[H|].
  constructor=>x y Xx Yy. specialize (H _ _ Xx Yy). lra.
  case is_ltE=>[H|]; constructor=> x y Xx Yy. specialize (H _ _ Yy Xx). lra.
Qed.

Definition is_ge {N: NBH} X Y := is_le Y X.
Lemma is_geE {N: NBH} X Y: wreflect (forall x y, contains X x -> contains Y y -> x>=y) (is_ge X Y).
Proof. rewrite /is_ge. case is_leE=>[H|]; constructor; auto using Rle_ge. Qed.


(** predicate for specifying bounds of integrals (see [rmintegrate] below) *)
Variant ocontains{N: NBH} x: option II -> R -> Prop :=
| ocontains_some: forall A a, contains A a -> ocontains x (Some A) a
| ocontains_none: ocontains x None x.
Global Hint Constructors ocontains: rel.
  

(** ** [Model]: abstraction for functions on real numbers *)

(** operations on models *)
Class ModelOps {N: NBH} := {
  (** pointwise operations *)
  MM: Ops0;
  (** identity (maybe an error, since the identity may not belong to the considered base)*)
  mid: E MM;
  (** sine,cosine (idem) *)
  mcos: E MM;
  msin: E MM;
  (** constant function *)
  mcst: II -> MM;
  (** evaluation may raise errors, when the argument does not belong to the considered domain *)
  meval: MM -> II -> E II;
  (** integration; missing bounds are assumed to be those of the domain *)
  mintegrate: MM -> option II -> option II -> E II;
  (** division and square root: we use an certification a posteriori, the first argument is supposed to be the interpolation degree for the oracles 
      may raise errors, in case the oracles do not provide appropriate approximations
   *)
  mdiv: Z -> MM -> MM -> E MM;
  msqrt: Z -> MM -> E MM;
  (** [truncate] acts as the identity *)
  mtruncate: Z -> MM -> MM;
  (** [mrange] returns an approximation of the range of the model on the considered domain *)
  mrange: MM -> II;
  (** nullability/positivity test, first argument is supposed to be the interpolation degree for computing the inverse of the model in order get a well-conditionned problem 
      positivity test may raise an error, in case the given model is not declared as continuous
   *)
  mne0: Z -> MM -> bool;
  mgt0: Z -> MM -> E bool;
}.
Coercion MM: ModelOps >-> Ops0.

Definition mlt `{ModelOps} z f g := mgt0 z (g-f).
Definition mne `{ModelOps} z f g := mne0 z (f-g).

(** specification of the above operations, on the domain [[lo;hi]] *)
Class Model {N: NBH} (MO: ModelOps) (lo hi: R) := {
  mcontains: Rel0 MM (f_Ops0 R ROps0);
  rmid: EP' mcontains mid id;
  rmcos: EP' mcontains mcos cos;
  rmsin: EP' mcontains msin sin;
  rmcst: forall C c, contains C c -> mcontains (mcst C) (fun _ => c);
  rmeval: forall F f, mcontains F f ->
          forall X x, contains X x -> 
                      EP' contains (meval F X) (f x);
  rmintegrate: forall F f, mcontains F f ->
               forall A a, ocontains lo A a ->
               forall C c, ocontains hi C c ->
                           EP' contains (mintegrate F A C) (RInt f a c);
  rmdiv: forall n F f, mcontains F f ->
         forall   G g, mcontains G g -> 
                       EP' mcontains (mdiv n F G) (fun x => f x / g x);
  rmsqrt: forall n F f, mcontains F f ->
                        EP' mcontains (msqrt n F) (fun x => sqrt (f x));
  rmtruncate: forall n F f, mcontains F f ->
                            mcontains (mtruncate n F) f;
  rmrange: forall F f, mcontains F f ->
           forall x, lo<=x<=hi -> contains (mrange F) (f x);
  rmne0: forall n F f, mcontains F f -> mne0 n F -> forall x, lo<=x<=hi -> f x <> 0;
  rmgt0: forall n F f, mcontains F f -> EPimpl (mgt0 n F) (forall x, lo<=x<=hi -> 0 < f x);
}.
Coercion mcontains: Model >-> Rel0.
Global Hint Resolve rmcst (* rmeval rmintegrate rmdiv rmsqrt *): rel.

Lemma rmne `{Model} n F f G g: mcontains F f -> mcontains G g -> mne n F G ->
                               forall x, lo<=x<=hi -> f x <> g x.
Proof.
  intros Ff Gg C x Dx. apply Rminus_not_eq.
  eapply (rmne0 (F:=F - G) (f:=f-g)). rel. apply C. assumption. 
Qed.

Lemma rmlt `{Model} n F f G g: mcontains F f -> mcontains G g ->
                               EPimpl (mlt n F G) (forall x, lo<=x<=hi -> f x < g x).
Proof.
  intros Ff Gg. unfold mlt. ecase rmgt0. rel. 2: constructor.
  intros b B. constructor. intros. now apply Rminus_gt_0_lt, B.
Qed.

(** two instances of [rmulZ] and [rdivZ] that need to be explicited for the [rel] tactic to work well *)
Lemma rmulZ' {N: NBH} z x y: contains x y -> contains (mulZ z x) (IZR z * y).
Proof. apply rmulZ. Qed.
Lemma rdivZ' {N: NBH} z x y: contains x y -> contains (divZ z x) (y / IZR z).
Proof. apply rdivZ. Qed.
Global Hint Resolve rmulZ' rdivZ': rel.


(** ** domains *)

Class Domain_on C := make_domain_on {
  dlo: C;
  dhi: C;
}.

Class Domain {N: NBH} := make_domain {
  DR:> Domain_on R;
  DI:> Domain_on II;
  rdlo: contains dlo dlo;
  rdhi: contains dhi dhi;
  dlohi: dlo<dhi;
}.
Global Hint Resolve rdlo rdhi: rel.

(** constructing simple domains *)
(** from relative numbers *)
Definition DfromZ2 {N: NBH}(a b: Z) (H: Z.compare a b = Lt): Domain := {|
  DR := make_domain_on (fromZ a) (fromZ b);
  DI := make_domain_on (fromZ a) (fromZ b);
  dlohi := IZR_lt _ _ (proj1 (Z.compare_lt_iff _ _) H);
  rdlo := rfromZ _ a;
  rdhi := rfromZ _ b;
|}.
Notation DZ2 a b := (@DfromZ2 _ a b eq_refl).

(** from rational numbers *)
Definition DfromQ2 {N: NBH}(a b: Q) (H: Qcompare a b = Lt): Domain := {|
  DR := make_domain_on (fromQ a) (fromQ b);
  DI := make_domain_on (fromQ a) (fromQ b);
  dlohi := Qreals.Qlt_Rlt _ _ (proj1 (Qlt_alt _ _) H);
  rdlo := rfromQ _ a;
  rdhi := rfromQ _ b;
|}.
Notation DQ2 a b := (@DfromQ2 _ a b eq_refl).

(** from floating points *)
Program Definition DfromF2 {N: NBH}(a b: FF) (H: is_lt (F2I a) (F2I b)): Domain := {|
  DR := make_domain_on (F2R a) (F2R b);
  DI := make_domain_on (F2I a) (F2I b);
  rdlo := F2IE a;
  rdhi := F2IE b;
|}.
Next Obligation.
  revert H. case is_ltE=>//H _. apply H; apply F2IE. 
Qed.
Notation DF2 a b := (@DfromF2 _ a b eq_refl).

(** from pointed intervals *)
Definition DfromI2 {N: NBH}(A B: II)(a b: R)
        (Aa: contains A a)
        (Bb: contains B b)
        (ab: is_lt A B): Domain := {|
  DR := make_domain_on a b;
  DI := make_domain_on A B;
  rdlo := Aa;
  rdhi := Bb;
  dlohi := wreflectE (is_ltE _ _) ab _ _ Aa Bb;
|}.
Notation DI2 Aa Bb := (DfromI2 Aa Bb eq_refl).


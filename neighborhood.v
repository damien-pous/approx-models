(** * Hierarchy of structures: basic operations, operations on functions, neighbourhoods *)

Require Export Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
Require Export String List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope R_scope.

(** instances for setoid_rewriting on Rle *)
Instance Rle_PreOrder: PreOrder Rle.
Proof. constructor; cbv; intros; lra. Qed.
Instance Rlt_PreOrder: Transitive Rlt. 
Proof. cbv; intros; lra. Qed.
Instance Rlt_Rle: subrelation Rlt Rle.
Proof. cbv. tauto. Qed.
Instance Rplus_Rle: Proper (Rle ==> Rle ==> Rle) Rplus.
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



(** ** Operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, list C, Model C) *)
Record Ops0 :=                  
  {
    car:> Type;
    add: car -> car -> car;
    sub: car -> car -> car;
    mul: car -> car -> car;
    zer: car;
    one: car;
  }.

(** extended operations *)
(** (will be instantiated on R, I, F) *)
Record Ops1 :=
  {
    ops0:> Ops0;
    fromZ: Z -> ops0;
    div: ops0 -> ops0 -> ops0;  (** also on Model C, but with parameters *)
    sqrt: ops0 -> ops0;         (** idem *)
    cos: ops0 -> ops0;
    abs: ops0 -> ops0;
    pi: ops0;
  }.

(** derived operations *)
Definition fromN {C: Ops1} (n: nat) := fromZ C (Z.of_nat n). 
Definition dvn {C: Ops1} n x: C := div x (fromN n).

(** notations *)
Declare Scope RO_scope.
Infix "+" := add: RO_scope. 
Infix "*" := mul: RO_scope.
Infix "-" := sub: RO_scope.
Infix "/" := div: RO_scope.
Notation "x // n" := (dvn n x) (at level 40, left associativity): RO_scope .
Notation "0" := (zer _): RO_scope.
Notation "1" := (one _): RO_scope.
Arguments fromZ {_}. 
Arguments pi {_}. 
Open Scope RO_scope.
Bind Scope RO_scope with car.

(** derived operations *)
Fixpoint pow (C: Ops0) n (x: C) :=
  match n with
  | O => 1
  | S n => x*pow n x
  end.


(** ** lifting to functions *)
Definition f_cst A B (b: B) (a: A) := b.
Definition f_unr A B (o: B -> B) (f: A -> B) (a: A) := o (f a).
Definition f_bin A B (o: B -> B -> B) (f g: A -> B) (a: A) := o (f a) (g a).
Canonical Structure f_Ops0 (A: Type) (C: Ops0): Ops0 :=
  {|
    car := A -> C;
    add := f_bin (@add C);
    sub := f_bin (@sub C);
    mul := f_bin (@mul C);
    zer := f_cst (@zer C);
    one := f_cst (@one C);
  |}.

(** ** instances on Reals *)
Canonical Structure ROps0 :=
  {|
    car := R;
    add := Rplus;
    sub := Rminus;
    mul := Rmult;
    zer := R0;
    one := R1;
  |}.
Canonical Structure ROps1 :=
  {|
    ops0 := ROps0;
    fromZ := IZR;
    div := Rdiv;
    sqrt := R_sqrt.sqrt;
    cos := Rtrigo_def.cos;
    abs := Rabs;
    pi := Rtrigo1.PI;
  |}.
Lemma RfromN: forall n, INR n = fromN n.
Proof INR_IZR_INZ.
Lemma Rpow n x: x^n = pow n x.
Proof. induction n=>//=. congruence. Qed.

(** ** parametricity relations *)
Record Rel0 (R S: Ops0) :=
  {
    rel:> R -> S -> Prop;
    radd: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x+x') (y+y');
    rsub: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x-x') (y-y');
    rmul: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x*x') (y*y');
    rzer: rel 0 0;
    rone: rel 1 1
  }.
Record Rel1 (R S: Ops1) :=
  {
    rel0:> Rel0 R S;
    rdiv: forall x y, rel0 x y -> forall x' y', rel0 x' y' -> rel0 (x/x') (y/y');
    rfromZ: forall z, rel0 (fromZ z) (fromZ z);
    rsqrt: forall x y, rel0 x y -> rel0 (sqrt x) (sqrt y);
    rabs: forall x y, rel0 x y -> rel0 (abs x) (abs y);
    rcos: forall x y, rel0 x y -> rel0 (cos x) (cos y);
    rpi: rel0 pi pi;
  }.
Global Hint Resolve radd rsub rmul rfromZ rzer rone rdiv rsqrt rabs rcos rpi: rel.
Ltac rel := by eauto 100 with rel.

(** parametricity of derived operations *)
Lemma rpow R S (T: Rel0 R S) n: forall x y, T x y -> T (pow n x) (pow n y).
Proof. induction n; simpl; rel. Qed.
Global Hint Resolve rpow: rel.

Lemma rfromN R S (T: Rel1 R S) n: T (fromN n) (fromN n).
Proof. unfold fromN; rel. Qed.
Global Hint Resolve rfromN: rel.

Lemma rdvn R S (T: Rel1 R S) n: forall x y, T x y -> T (x//n) (y//n).
Proof. rewrite /dvn; rel. Qed.
Global Hint Resolve rdvn: rel.

(** ** Neighborhoods *)

(** utilities for specifications  *)
Inductive minmax_spec A le (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| minmax_spec_some: forall m b, contains m b -> contains a b -> (forall x, contains a x -> le x b) -> minmax_spec le contains a (Some m)
| minmax_spec_none: (forall x y, contains a x -> le x y -> contains a y)-> minmax_spec le contains a None.

Inductive wreflect (P : Prop): bool -> Prop :=
 | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.

(** neighborhoods: an abstract interface for computing with floating points and intervals 
    convention: 
    - uppercase letters for intervals, lowercase letters for real numbers
    - same letter when a real is assumed to belong to an interval: 
      y: R, Y: II   often means that we also have   H: contains Y y. *)
Class NBH :=
  {
    (** intervals *)
    II: Ops1;
    (** (parametric) containment relation *)
    contains: Rel1 II ROps1;
    (** convexity of intervals  *)
    convex: forall Z x y, contains Z x -> contains Z y -> forall z, x<=z<=y -> contains Z z;
    (** additional operations on intervals *)
    bnd: II -> II -> II;
    max: II -> option II;    
    min: II -> option II;    
    bot: II;                   (** [-oo;+oo] *)
    is_lt: II -> II -> bool; 
    is_le: II -> II -> bool; 
    (** specification of the above operations *)
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
    width: II -> FF;  (** width of an interval (unspecified, just for inspection) *)
    F2R: FF -> R;   (** needed to guarantee that F2I produces non-empty intervals *)
    F2IE: forall f, contains (F2I f) (F2R f);
    (** is an interval contained within the given bounds? (needed only in the very end, for concrete examples) *)
    subseteq: II -> R -> R -> Prop; (** note that this one is in Prop  *)
    subseteqE: forall X (a b: R), subseteq X a b -> forall x, contains X x -> a <= x <= b;
  }.
Coercion II: NBH >-> Ops1.

(** derived operations and their specification *)
Definition mag {N: NBH} x: option II := max (abs x).
Definition sym {N: NBH} x: II := let x := abs x in bnd (0-x) x.

Inductive mag_spec A (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| mag_spec_some: forall m b, contains m b -> (forall x, contains a x -> Rabs x <= b) -> mag_spec contains a (Some m)
| mag_spec_none: mag_spec contains a None.

Lemma magE {N: NBH} X: mag_spec contains X (mag X).
Proof. rewrite /mag. elim: maxE; econstructor; eauto; rel. Qed.

Lemma symE {N: NBH} x y I: Rabs x <= y -> contains I y -> contains (sym I) x.
Proof.
  intros Hx Hy. rewrite /sym. apply bndE with (0-abs y) (abs y); try rel. 
  simpl; split_Rabs; lra.
Qed.


(** type for potential runtime errors *)
Definition E A := (A + string)%type.
Definition ret {A} (a: A): E A := inl a.
Definition err {A} (e: string): E A := inr e.
Definition bind {A B} (x: E A) (f: A -> E B): E B :=
  match x with inl a => f a | inr e => inr e end.
Infix ">>=" := bind (at level 30).
Inductive Ep {A} (P: A -> Prop): E A -> Prop :=
  ep_ret: forall a, P a -> Ep P (ret a).
Definition Ep' {A B} (P: A -> B -> Prop): E A -> B -> Prop :=
  fun x b => Ep (fun a => P a b) x.

(** ** abstract operations on functions *)
Record FunOps (C: Type) :=
  {
    (* pointwise operations *)
    funcar:> Ops0;
    (* operations specific to functions *)
    mid: funcar;                 
    mcst: C -> funcar;
    meval: funcar -> C -> E C;
    mintegrate: funcar -> C -> C -> E C;
    mdiv: Z -> funcar -> funcar -> E funcar;
    msqrt: Z -> funcar -> E funcar;
    (* [truncate] is the identity on reals; it makes it possible to truncate polynomials in models *)
    mtruncate: nat -> funcar -> funcar;
    (* range is meaningless on reals; it returns the range of the model otherwise *)
    mrange: funcar -> C;
  }.
Arguments mid {_ _}.
Arguments mcst {_ _}.

(** corresponding operations on [R->R] *)
Definition RFunOps: FunOps R :=
  {|
    funcar := f_Ops0 R ROps0;
    mid x := x;
    mcst c _ := c;
    meval f x := ret (f x);
    mintegrate f a b := ret (RInt f a b);
    mdiv _ f g := ret (f_bin Rdiv f g);
    msqrt _ f := ret (f_unr R_sqrt.sqrt f);
    mtruncate _ f := f;
    mrange _ := R0;
  |}.

(** validity of function operations (will probably be reworked) *)
Class ValidFunOps I (contains: I -> R -> Prop) (dom: R -> Prop) (F: FunOps I) :=
  {
    fcontains: Rel0 F RFunOps;
    rmid: fcontains mid mid;
    rmcst: forall C c, contains C c -> fcontains (mcst C) (mcst c);
    rmeval: forall F f, fcontains F f ->
            forall X x, contains X x -> 
                        Ep' contains (meval F X) (f x);
    rmintegrate: forall F f, fcontains F f -> (forall x, dom x -> continuity_pt f x) ->
                 forall A a, contains A a ->
                 forall C c, contains C c ->
                             Ep' contains (mintegrate F A C) (RInt f a c);
    rmdiv: forall n F f, fcontains F f ->
           forall   G g, fcontains G g -> 
                         Ep' fcontains (mdiv n F G) (f_bin Rdiv f g);
    rmsqrt: forall n F f, fcontains F f ->
                          Ep' fcontains (msqrt n F) (f_unr R_sqrt.sqrt f);
    rmtruncate: forall n F f, fcontains F f ->
                              fcontains (mtruncate n F) f;
    eval_mrange: forall F f, fcontains F f ->
                 forall x, dom x -> contains (mrange F) (f x);
  }.
Coercion fcontains: ValidFunOps >-> Rel0.
Global Hint Resolve rmid rmcst (* rmeval rmintegrate *) rmdiv rmsqrt: rel.

(** ** 'generic' domains *)
Class Domain :=
  { dlo: forall {C: Ops1}, C;
    dhi: forall {C: Ops1}, C;
    dlohi: dlo<dhi;
    rdlo: forall R S (T: Rel1 R S), T dlo dlo;
    rdhi: forall R S (T: Rel1 R S), T dhi dhi }.
Global Hint Resolve rdlo rdhi: rel.

Definition DfromZ2 (a b: Z) (H: Z.compare a b = Lt): Domain :=
  {| dlo C := fromZ a;
     dhi C := fromZ b;
     dlohi := IZR_lt _ _ (proj1 (Z.compare_lt_iff _ _) H);
     rdlo R S T := rfromZ T a;
     rdhi R S T := rfromZ T b |}.
Notation DZ a b := (@DfromZ2 a b eq_refl).

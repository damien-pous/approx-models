(** * Hierarchy of structures: basic operations, operations on functions, neighbourhoods *)

Require Export Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
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

(** blocking identity to document irrelevant values *)
Lemma IRRELEVANT (A: Type): A -> A.
Proof. by []. Qed. 



(** ** Operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, seq C, Model C) *)
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
    div: ops0 -> ops0 -> ops0;  (* also on Model C, but with parameters *)
    sqrt: ops0 -> ops0;         (* idem *)
    cos: ops0 -> ops0;
    abs: ops0 -> ops0;
    pi: ops0;
  }.

(** derived operations  *)
Definition fromN {C: Ops1} (n: nat) := fromZ C (Z.of_nat n). 
Definition dvn {C: Ops1} n x: C := div x (fromN n).

(** notations *)
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
Hint Resolve radd rsub rmul rfromZ rzer rone rdiv rsqrt rabs rcos rpi: rel.
Ltac rel := by ((* repeat unshelve *) eauto 100 with rel).

(** parametricity of derived operations *)
Lemma rpow R S (T: Rel0 R S) n: forall x y, T x y -> T (pow n x) (pow n y).
Proof. induction n; simpl; rel. Qed.
Hint Resolve rpow: rel.

Lemma rfromN R S (T: Rel1 R S) n: T (fromN n) (fromN n).
Proof. unfold fromN; rel. Qed.
Hint Resolve rfromN: rel.

Lemma rdvn R S (T: Rel1 R S) n: forall x y, T x y -> T (x//n) (y//n).
Proof. rewrite /dvn; rel. Qed.
Hint Resolve rdvn: rel.

(** ** Neighborhoods  *)

(** utilities for specifications  *)
Inductive minmax_spec A le (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| minmax_spec_some: forall m b, contains m b -> contains a b -> (forall x, contains a x -> le x b) -> minmax_spec le contains a (Some m)
| minmax_spec_none: (forall x y, contains a x -> le x y -> contains a y)-> minmax_spec le contains a None.

Inductive wreflect (P : Prop): bool -> Prop :=
 | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.

(** neighborhoods *)
Class NBH :=
  {
    (** intervals *)
    II:> Ops1;
    (** (parametric) containment relation *)
    contains: Rel1 II ROps1;
    (** convexity of intervals  *)
    convex: forall Z x y, contains Z x -> contains Z y -> forall z, x<=z<=y -> contains Z z;
    (** additional operations on intervals *)
    bnd: II -> II -> II;
    max: II -> option II;    
    min: II -> option II;    
    bot: II;                   (* [-oo;+oo] *)
    is_lt: II -> II -> bool; 
    (** specification of the above operations *)
    bndE: forall X x, contains X x -> forall Y y, contains Y y -> forall z, x<=z<=y -> contains (bnd X Y) z;
    maxE: forall X, minmax_spec Rle contains X (max X);
    minE: forall X, minmax_spec Rge contains X (min X);
    botE: forall x, contains bot x;
    is_ltE: forall X Y, wreflect (forall x y, contains X x -> contains Y y -> x<y) (is_lt X Y);
    (** (almost unspecified) floating point operations *)
    FF: Ops1;
    I2F: II -> FF;
    F2I: FF -> II;
    width: II -> FF;  (* width of an interval (unspecified, just for inspection) *)
    F2R: FF -> R;   (* needed to guarantee that F2I produces non-empty intervals *)
    F2IE: forall f, contains (F2I f) (F2R f);
  }.

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



(** ** abstract operations on functions *)
Record FunOps (C: Type) :=
  {
    (* pointwise operations *)
    funcar:> Ops0;
    (* operations specific to functions *)
    id: funcar;                 
    cst: C -> funcar;
    eval: funcar -> C -> C;
    integrate: funcar -> C -> C -> C;
    div': Z -> funcar -> funcar -> funcar;
    sqrt': Z -> funcar -> funcar;
    (* [truncate] is the identity on reals; it makes it possible to truncate polynomials in models *)
    truncate: nat -> funcar -> funcar;
    (* range is meaningless on reals; it returns the range of the model otherwise *)
    range: funcar -> C;
  }.
Arguments id {_ _}.
Arguments cst {_ _}.

(** corresponding operations on [R->R] *)
Canonical Structure RFunOps: FunOps R :=
  {|
    funcar := f_Ops0 R ROps0;
    id x := x;
    cst c _ := c;
    eval f x := f x;
    integrate := RInt;
    div' _ := f_bin Rdiv;
    sqrt' _ := f_unr R_sqrt.sqrt;
    truncate _ f := f;
    range _ := R0;
  |}.

(** validity of function operations (not yet used) *)
Class ValidFunOps I (contains: Rel1 I ROps1) (F: FunOps I) :=
  {
    fcontains:> Rel0 F RFunOps;
    rid: fcontains id id;                 
    rcst: forall C c, contains C c -> fcontains (cst C) (cst c);
    reval: forall F f, fcontains F f -> forall X x, contains X x -> contains (eval F X) (eval f x);
    (* dessous: would need [f] continuous and [a],[b] in the domain *)
    rintegrate: forall F f, fcontains F f ->
                forall A a, contains A a -> 
                forall C c, contains C c -> 
                            contains (integrate F A C) (integrate f a c);
    rdiv': forall n F f, fcontains F f ->
           forall G g, fcontains G g -> 
                         fcontains (div' n F G) (div' n f g);
    rsqrt': forall n F f, fcontains F f ->
                         fcontains (sqrt' n F) (sqrt' n f);
  }.
Coercion fcontains: ValidFunOps >-> Rel0.
Hint Resolve rid rcst reval rintegrate rdiv' rsqrt': rel.

(** ** 'generic' domains *)
Class Domain :=
  { dlo: forall {C: Ops1}, C;
    dhi: forall {C: Ops1}, C;
    dlohi: dlo<dhi;
    rdlo: forall R S (T: Rel1 R S), T dlo dlo;
    rdhi: forall R S (T: Rel1 R S), T dhi dhi }.

Definition DfromZ2 (a b: Z) (H: IZR a < IZR b): Domain :=
  {| dlo C := fromZ a;
     dhi C := fromZ b;
     dlohi := H;
     rdlo R S T := rfromZ T a;
     rdhi R S T := rfromZ T b |}.

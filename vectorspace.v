(** * Operations on linear combinations (generalised polynomials) *)

Require Export interfaces.

Set Universe Polymorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** linear operations *)
Section abs.
 Context {C: Ops0}.

 Definition szer: list C := [].
 
 Fixpoint sadd (P Q: list C): list C :=
   match P,Q with
   | [],C | C,[] => C
   | a::P,b::Q => (a+b)::sadd P Q
   end.
 
 Definition sopp (P: list C): list C := map (sub 0) P.
 
 Definition ssub P Q := sadd P (sopp Q).

 Definition smulZ z: list C -> list C := map (mulZ z).

 Definition sdivZ z: list C -> list C := map (divZ z).
 
 Definition sscal a: list C -> list C := map (mul a).

 Definition cons0 (p: list C) := match p with [] => p | _=>0::p end.
 
 Definition cons00 (p: list C) := match p with [] => p | _=>0::0::p end.
 
 Fixpoint split_list (n: nat) (p: list C) :=
   match n with
   | 0 => ([],p)
   | S n => match p with
             | [] => ([],[])
             | a::q => let (p,p') := split_list n q in (a::p,cons0 p')
             end
   end.

 (** [[0;...;0;1]] with [n] zeros: the nth element from the basis *)
 Fixpoint snth n: list C := match n with O => [1] | S n => 0::snth n end.

End abs.
Arguments sadd {C} !P !Q / .  

(** ** evaluation and properties of the operations on reals *)
Section e.
 Variable M: nat -> R -> R.

 (** evaluation in the given basis *)
 Fixpoint eval_ n (P: list R) (x: R): R :=
   match P with
   | [] => 0
   | a::Q => a * M n x + eval_ (S n) Q x
   end.
 Definition eval := eval_ 0.

 Lemma eval_zer (x: R): eval szer x = 0.
 Proof. reflexivity. Qed.
 Lemma eval_app_: forall P Q (x: R) n, eval_ n (P ++ Q) x = eval_ n P x + eval_ (length P + n) Q x.
 Proof.
   intros P; induction P as [|a P IH]; intros Q x n.
   - compute; ring.
   - rewrite /=IH/= plus_n_Sm. ring.
 Qed.
 Lemma eval_app: forall P Q (x: R), eval (P ++ Q) x = eval P x + eval_ (length P) Q x.
 Proof. intros; rewrite /eval eval_app_ -plus_n_O //. Qed.
 Lemma eval_add_: forall P Q (x: R) n, eval_ n (sadd P Q) x = eval_ n P x + eval_ n Q x.
 Proof. induction P as [|a P IH]; intros [|b Q] x n; rewrite /=?IH/=; ring. Qed.
 Lemma eval_add: forall P Q (x: R), eval (sadd P Q) x = eval P x + eval Q x.
 Proof. intros. apply eval_add_. Qed.
 Lemma eval_opp_: forall P (x: R) n, eval_ n (sopp P) x = -eval_ n P x.
 Proof. induction P as [|a P IH]; intros x n; rewrite /=?IH/=; ring. Qed.
 Lemma eval_opp: forall P (x: R), eval (sopp P) x = -eval P x.
 Proof. intros. apply eval_opp_. Qed.
 Lemma eval_sub_: forall P Q (x: R) n, eval_ n (ssub P Q) x = eval_ n P x - eval_ n Q x.
 Proof. intros. rewrite /ssub eval_add_ eval_opp_ /=. ring. Qed.
 Lemma eval_sub: forall P Q (x: R), eval (ssub P Q) x = eval P x - eval Q x.
 Proof. intros. apply eval_sub_. Qed.
 Lemma eval_mulZ_: forall a P (x: R) n, eval_ n (smulZ a P) x = mulZ a (eval_ n P x).
 Proof. induction P as [|b P IH]; intros; rewrite /=?IH/=; ring. Qed. 
 Lemma eval_mulZ: forall a P (x: R), eval (smulZ a P) x = mulZ a (eval P x).
 Proof. intros. apply eval_mulZ_. Qed. 
 Lemma eval_divZ_: forall a P (x: R) n, eval_ n (sdivZ a P) x = divZ a (eval_ n P x).
 Proof. induction P as [|b P IH]; intros; rewrite /=?IH/=/Rdiv; ring. Qed. 
 Lemma eval_divZ: forall a P (x: R), eval (sdivZ a P) x = divZ a (eval P x).
 Proof. intros. apply eval_divZ_. Qed. 
 Lemma eval_scal_: forall a P (x: R) n, eval_ n (sscal a P) x = a * eval_ n P x.
 Proof. induction P as [|b P IH]; intros; rewrite /=?IH/=; ring. Qed. 
 Lemma eval_scal a P (x: R): eval (sscal a P) x = a * eval P x.
 Proof. intros. apply eval_scal_. Qed. 
 Lemma eval_cons0_ n p (x: R): eval_ n (cons0 p) x = eval_ (S n) p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_cons00_ n p (x: R): eval_ n (cons00 p) x = eval_ (S (S n)) p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_split_list n: forall p x, eval p x = eval (split_list n p).1 x + eval (split_list n p).2 x.
 Proof.
   unfold eval. generalize O as m. 
   elim: n => [|n IH] m p x. simpl; lra.
   case: p => [|a p] =>/=. lra.
   rewrite IH. destruct (split_list n p) as [q q'] =>/=.
   rewrite eval_cons0_. lra.
 Qed.
 Lemma eval_nth_ n m x: eval_ m (snth n) x = M (n+m) x.
 Proof.
   move: m. elim: n=>[|n IH] m; cbn. ring.
   rewrite IH plus_n_Sm. ring.
 Qed.
 Lemma eval_nth n x: eval (snth n) x = M n x.
 Proof. by rewrite /eval eval_nth_ -plus_n_O. Qed.

 (** helpers from constructing bases with additional common properties  *)
 
 Hypothesis H: forall n x, continuity_pt (M n) x. 
 Lemma eval_cont_ P x: forall n, continuity_pt (eval_ n P) x.
 Proof.
   elim:P=>[|a Q IH] n /=. 
   + by apply continuity_pt_const. 
   + apply continuity_pt_plus=>//.
     apply continuity_pt_mult=>//.
     by apply continuity_pt_const.
 Qed.

 Lemma eval_cont_basis P x: continuity_pt (eval P) x.
 Proof. apply eval_cont_. Qed.

 (** when the basis elements are derivable *)
 Hypothesis D: forall n x, ex_derive (M n) x.
 Lemma eval_ex_derive_basis_ n P x: ex_derive (eval_ n P) x.
 Proof. elim: P n => [ | a P IHP] n /=; now auto_derive. Qed.

 Lemma eval_ex_derive_basis P x : ex_derive (eval P) x.
 Proof. apply eval_ex_derive_basis_. Qed.

 (** when there is an operation for taking primitives *)
 Variable prim: list R -> list R.
 Hypothesis P: forall p x, Derive (eval (prim p)) x = eval p x.

 Lemma integrate_prim p a b : eval (prim p) b - eval (prim p) a = RInt (eval p) a b.
 Proof.
   rewrite -(RInt_ext (Derive (eval (prim p)))). 2: by intro; rewrite P.
   rewrite RInt_Derive. by [].
   * intros t _; apply eval_ex_derive_basis.
   * intros t _; apply continuous_ext with (f:= eval p); first by intro; rewrite P.
     apply continuity_pt_filterlim; apply eval_cont_basis.
 Qed.
 
End e.


(** ** parametricity of the operations  *)

Section s.
 Context {R S: Ops0} {rel: inRel R S} {rel0: Rel0 rel}.
 Lemma saddR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> sadd x x' ∈ sadd y y'.
 Proof.
   intros P Q H. induction H. rel. 
   intros P' Q' H'. destruct H'; rel. 
 Qed.
 Lemma smulZR z: forall x y, x ∈ y -> smulZ z x ∈ smulZ z y.
 Proof. induction 1; rel.  Qed.
 Lemma sdivZR z: forall x y, x ∈ y -> sdivZ z x ∈ sdivZ z y.
 Proof. induction 1; rel.  Qed.
 Lemma sscalR a b: a ∈ b -> forall x y, x ∈ y -> sscal a x ∈ sscal b y.
 Proof. induction 2; rel.  Qed.
 Lemma soppR: forall x y, x ∈ y -> sopp x ∈ sopp y.
 Proof. induction 1; rel. Qed.
 Lemma ssubR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> ssub x x' ∈ ssub y y'.
 Proof. intros; apply saddR; auto using soppR. Qed.
 Lemma szerR: szer ∈ szer.
 Proof. rel. Qed.
 Lemma cons0R: forall x y, x ∈ y -> cons0 x ∈ cons0 y.
 Proof. destruct 1; rel. Qed.
 Lemma cons00R: forall x y, x ∈ y -> cons00 x ∈ cons00 y.
 Proof. destruct 1; rel. Qed.
 Lemma split_listR n: forall p q, p ∈ q -> split_list n p ∈ split_list n q.
 Proof.
   move: cons0R=>?.
   elim: n=>[|n IH]. rel.
   destruct 1 as [|x y p q XY PQ]; simpl. rel.
   generalize (IH _ _ PQ). case (split_list n p). case (split_list n q). 
   intros ???? []. rel.
 Qed.
 Lemma snthR n: snth n ∈ snth n.
 Proof. elim: n; rel. Qed.
End s.
Global Hint Resolve saddR smulZR sdivZR sscalR soppR ssubR szerR cons0R cons00R snthR: rel.


(** ** requirements for generating pseudo-polynomial models (in approx.v) *)

Class BasisOps_on (C: Type) := {
  lo: C;
  hi: C;
  beval: list C -> C -> C;
  bmul: list C -> list C -> list C;
  bone: list C;
  (* identity (if present in the basis) *)
  bid: E (list C);
  (* sine/cosine (if present in the basis) *)
  bcos: E (list C);
  bsin: E (list C);
  bintegrate: list C -> C -> C -> C;
  (* range is an optional operation (implemented locally if absent, e.g., for Taylor models) *)
  brange: option (list C -> C*C); 
  interpolate: Z -> (C -> C) -> list C;
}.

(** Basis operations immediately give an Ops0 structure on [list C] *)
Canonical Structure listOps0 (C: Ops1) (B: BasisOps_on C) := {|
  car := list C;
  add := sadd;
  mul := bmul;
  mul' _ := bmul;
  sub := ssub;
  zer := szer;
  one := bone;
  mulZ := smulZ;
  divZ := sdivZ;
|}.

Class BasisOps {N: NBH} := {
  (** concrete operations on intervals & floating points *)
  BI:> BasisOps_on II;
  BF:> BasisOps_on FF;
}.

(** derived operations *)
Definition dom {BO: BasisOps_on R} (x: R) := lo <= x <= hi.
Definition Dom `{BO: BasisOps} (X: II) := is_le lo X && is_le X hi.

(** requirements on basis operations *)
Class Basis {N: NBH} (B: BasisOps) := {

  (** the mathematical basis itself *)
  TT: nat -> R -> R;

  (** abstract operations on reals *)
  BR:> BasisOps_on R;

  (** the domain is non-trivial *)
  lohi: lo<hi;
  
  (** properties of BR *)
  evalE: forall p x, beval p x = eval TT p x;
  basis_cont: forall n x, continuity_pt (TT n) x; (* would make sense to require this only on the domain *)
  eval_mul: forall p q x, eval TT (bmul p q) x = eval TT p x * eval TT q x;
  eval_one: forall x, eval TT bone x = 1;
  eval_id: EP (fun bid => forall x, eval TT bid x = x) bid;
  eval_cos: EP (fun bcos => forall x, eval TT bcos x = cos x) bcos;
  eval_sin: EP (fun bsin => forall x, eval TT bsin x = sin x) bsin;
  eval_range: match brange with
               | Some range => (forall p x, dom x -> (range p).1 <= eval TT p x <= (range p).2)
               | None => True end;
  integrateE: forall p a b, bintegrate p a b = RInt (eval TT p) a b;
  
  (** link between BI and BR *)
  loR: lo ∈ lo;
  hiR: hi ∈ hi;
  bmulR: ltac:(expand (bmul ∈ bmul));
  boneR: bone ∈ bone;
  bidR: bid ∈ bid;
  bcosR: bcos ∈ bcos;
  bsinR: bsin ∈ bsin;
  bintegrateR: ltac:(expand (bintegrate ∈ bintegrate));
  bevalR: ltac:(expand (beval ∈ beval));
  brangeR: brange ∈ brange;
}.
Global Hint Resolve bmulR boneR bidR bcosR bsinR bintegrateR bevalR loR hiR: rel.


(** ** derived properties *)
Section s.
Context `{Basis}.

Lemma domlo: dom lo.
Proof. generalize lohi. split; lra. Qed.

Lemma domhi: dom hi.
Proof. generalize lohi. split; lra. Qed.

Lemma DomE X: Dom X ~> forall x, x ∈ X -> dom x.
Proof.
  apply implE. rewrite /Dom.
  case is_leE=>//Lo. 
  case is_leE=>//Hi _ x Xx.
  split; [apply Lo|apply Hi]=>//; rel.
Qed.

Lemma eval_cont p x: continuity_pt (eval TT p) x.
Proof. apply eval_cont_basis. apply basis_cont. Qed.

Lemma integrateE' p a b: is_RInt (eval TT p) a b (bintegrate p a b).
Proof.
  rewrite integrateE; apply (RInt_correct (eval TT p)).
  apply ex_RInt_Reals_1; case (Rle_dec a b) => Hab; [ | apply RiemannInt.RiemannInt_P1];
  apply RiemannInt.continuity_implies_RiemannInt; try lra;
     now intros t _; apply eval_cont.
Qed.

End s.

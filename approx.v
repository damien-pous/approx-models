(** * Rigorous approximations in a generic basis *)

Require Import String. 
Require Import vectorspace.
Require div sqrt polynom_eq.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

(** ** tubes: polynomials with a remainder (rigorous approximations) *)

(** in this file we provide an instance of [Model] on tubes, given a generic basis ([Basis]) **)

(** we use an extra bit indicating whether the approximated function is continuous
    this makes it possible to prove continuity of some functions, by computation *)
Record Tube C := { pol: list C; rem: C; cont: bool }.


(** ** operations on tubes *)
Section n.
 Context {N: NBH} {BO: BasisOps}.
 Notation Tube := (Tube (car (ops0 (@II N)))).
 Notation eval' := taylor.eval'.
 Notation derive := taylor.derive.
 (** range of a polynomial *)
 Definition srange p: II :=
   match brange with
   | None => beval p (bnd lo hi)
   | Some range => let (m,M):=range p in bnd m M
   end.

 (** model with empty remainder *)
 Definition msingle p: Tube := {| pol := p; rem := 0; cont := true |}.

 (** uninformative model  *)
 Definition mbot: Tube := {| pol := 0; rem := bot; cont := false |}.

 (** basic operations on models *)
 Definition madd (M N: Tube): Tube :=
   {| pol := pol M + pol N;
      rem := rem M + rem N;
      cont := cont M && cont N; |}.
 Definition msub (M N: Tube): Tube :=
   {| pol := pol M - pol N;
      rem := rem M - rem N;
      cont := cont M && cont N; |}.
 Definition mmulZ z (M: Tube): Tube :=
   {| pol := mulZ z (pol M);
      rem := mulZ z (rem M);
      cont := cont M; |}.
 Definition mdivZ z (M: Tube): Tube :=
   {| pol := divZ z (pol M);
      rem := divZ z (rem M);
      cont := cont M; |}.
 Definition mscal (x: II) (M: Tube): Tube :=
   {| pol := sscal x (pol M);
      rem := x * rem M;
     cont := cont M; |}.
 (* TOTHINK: should we always truncate to the max degree of the arguments? *)
 Definition mmul (M N: Tube): Tube :=
   {| pol := pol M * pol N;
      rem := srange (pol M) * rem N + srange (pol N) * rem M + rem M * rem N;
      cont := cont M && cont N; |}.
 Definition mzer: Tube := msingle 0.
 Definition mone: Tube := msingle 1.

 (** by defining this structure, we get nice notations for the above operations on models *)
Canonical Structure MOps0: Ops0 :=
   {|
     car:=Tube;
     add:=madd;
     sub:=msub;
     mul:=mmul;
     zer:=mzer;
     one:=mone;
     mulZ:=mmulZ;
     divZ:=mdivZ;
   |}.

 (** nth element of the basis *)
 Definition mnth n: Tube := msingle (snth n).
 
 (** identity *)
 Definition mid: E Tube := e_map msingle bid.

 (** sine/cosine *)
 Definition mcos: E Tube := e_map msingle bcos.
 Definition msin: E Tube := e_map msingle bsin.

 (** constant *)
 Definition mcst c: Tube := mscal c mone.

 (** integration *)
 Definition mintegrate_unsafe (M: Tube) (a b: II): II :=
   bintegrate (pol M) a b + (b-a)*rem M.
 Definition mintegrate (M: Tube) (a b: option II): E II :=
   if ~~ cont M then err "mintegrate: need a continuous function" else
   match a,b with
   | Some a, Some b =>
     if Dom a && Dom b then ret (mintegrate_unsafe M a b) else err "mintegrate: invalid bounds"
   | Some a, None =>
     if Dom a then ret (mintegrate_unsafe M a hi) else err "mintegrate: invalid lower bound"
   | None, Some b =>
     if Dom b then ret (mintegrate_unsafe M lo b) else err "mintegrate: invalid upper bound"
   | None, None =>
     ret (mintegrate_unsafe M lo hi)
   end.
 
 (** evaluation, without checking that the argument belongs to the domain *)
 Definition meval_unsafe (M: Tube) (x: II): II := beval (pol M) x + rem M.

 (** evaluation *)
 Definition meval (M: Tube) (x: II): E II :=
   if Dom x then ret (meval_unsafe M x) else err "meval: argument out of bounds".
 
 (** range *)
 Definition mrange (M: Tube): II := srange (pol M) + rem M.

 (** truncation of a model *)
 Definition mtruncate (n: nat) (M: Tube): Tube :=
   let (p,q) := split_list n (pol M) in 
   {| pol := p; rem := rem M + srange q; cont := cont M |}.

 (** asserting continuity 'by hand' (see specification [rmcontinuous] below)*)
 Definition mcontinuous (M: Tube): Tube :=
   {| pol := pol M; rem := rem M; cont := true |}.

 (** auxiliary conversion functions to perform interpolation with floating points *)
 Definition mcf (M: Tube): list FF := map I2F (pol M).
 Definition mfc (p: list FF): Tube := {| pol := map F2I p; rem := 0; cont := true |}.
 
 (** division: H and W are given by an oracle
    H ~ F/G
    W ~ 1 /G *)
 Definition mdiv_aux (F G: Tube) (H W: list FF): E Tube :=
   let H := mfc H in
   let W := mfc W in
   (* TOTHINK: truncate multiplications? *)
   let K1 := 1 - W*G in
   let K2 := W*(G*H - F) in
   match mag (mrange K1), mag (mrange K2) with
   | Some mu, Some b =>
       if is_lt mu 1 then ret {| pol := pol H;
                                 rem := rem H + sym (b / (1 - mu));
                                 cont := cont F && cont G; |}
     else err "mdiv: non contractive operator"
   | _,_ => err "mdiv: error when checking the ranges of k1/k2"
   end.

 (** square root: H and W are given by an oracle 
    H ~ sqrt F
    W ~ 1 / 2H *)
 Definition msqrt_aux (F: Tube) (H W: list FF): E Tube :=
   let H := mfc H in
   let W := mfc W in
   let x0' := (lo+hi)//2 in
   let y0' := meval_unsafe W x0' in
   if ~~ is_lt 0 y0' then err "msqrt: potentially negative value" else
   (* TOTHINK: truncate multiplications? *)
   let K1 := 1 - (mmulZ 2 (W*H)) in
   let K2 := W*(H*H - F) in
   match mag (mrange K1), mag (mrange W), mag (mrange K2) with
   | Some mu0, Some mu1, Some b =>
     let delta := pow 2 (1 - mu0) - mulZ 8 b * mu1 in
     if is_lt mu0 1 then
       if is_lt 0 delta then
         let rmin := (1 - mu0 - sqrt delta)/(mulZ 4 mu1) in
         let mu := mu0 + mulZ 2 mu1 * rmin in
         if is_lt mu 1 then ret {| pol := pol H; rem:=rem H + sym rmin; cont := cont F |}             
         else err "msqrt: missed mu<1"
       else err "msqrt: missed 0<delta"
     else err "msqrt: missed mu0<1"
   | _,_,_ => err "msqrt: error when checking the ranges of K1/W/K2"
   end.

 (** division and square root, using interpolation as oracle ; [d] is the interpolation degree *)
 Definition mdiv d (M N: Tube): E Tube :=
   let p := mcf M in
   let q := mcf N in
   mdiv_aux M N
            (interpolate d (fun x => beval p x / beval q x))
            (interpolate d (fun x => 1 / beval q x)).
 Definition msqrt d (M: Tube): E Tube :=
   let p := mcf M in
   let h := interpolate d (fun x => sqrt (beval p x)) in
   msqrt_aux M
             h
             (interpolate d (fun x => 1 / (mulZ 2 (beval h x)))).

 (** solution of polynomial equation : F is a polynom with model coefficients
     - phi, A are given by an oracle, such that F(phi) ~ 0 and A ~ 1 / DF(phi)
     - r is a radius also given by an oracle, such that the Newton operator is stable and lambda contracting on B(phi,r) *) 
 Definition mpolynom_eq_aux (F: list Tube) (phi A: list FF) (r: II): E Tube :=
   let phi := mfc phi in
   let A := mfc A in
   let phir := {| pol := pol phi ; rem := rem phi + sym r ; cont := false |} in
   (* TOTHINK: the two occurrences of [eval'] below use model multiplications -> truncate them? *)
   let DN := eval' (derive (polynom_eq.opnewton F A)) phir in
   (* degree (N-1)*(d+d') where N is the degree of F and d' its maximal inner degree *)
   let N0 := A * eval' F phi in
   (* degree (N+1)*(d+d') *)
   match mag (mrange DN) , mag (mrange N0) with
   | Some lambda , Some d =>
     if is_lt lambda 1 then
       if is_le (d + lambda * r) r then
         let eps := d / (1 - lambda) in
         ret {| pol := pol phi; rem := rem phi + sym eps; cont := false |}
       else err "mpolyn_eq : missed (d+lambda*r)<=r"
     else err "mpolyn_eq : missed lambda<1"
   | _,_ => err "mpolyn_eq: error when checking the ranges of DN/N0"
   end.

 (** oracle for solutions of polynomial equations:
     by interpolation, using Newton's method to approximate the solution at the interpolation points
     - [d] is the interpolation degree / number of interpolation points
     - [n] is the number of Newton iterations for each point
     - [phi0] is a preliminary candidate
  *)
 Definition polynom_eq_oracle d n (F: list (list FF)) (phi0: list FF): list FF :=
   let newton n f f' u0 :=
     Zfold (fun _ u => u - eval' f u / eval' f' u) n u0
   in
   let f t :=
     let P := map (fun f => beval f t) F in
     newton n P (derive P) (beval phi0 t)
   in
   interpolate d f.
 
 (** putting everything together, we obtain the following function for computing solutions of polynomial functional equations.
     - [d] is the interpolation degree
     - [n] is the number of Newton iterations to be used at each point
     - [radius] is a heuristic to find a radius (see below)
     - [phi0] is a temptative solution (from which Newton iterations start with)
     [radius c lambda] should return [l] such that there is a radius [r] with 0<=r, l=lambda(r)<1 and c+lr<=r (we do not need the radius in itself, but it must exist)
     NOTE: here we inline the relevant part of [mpolynom_eq_aux]: assuming the radius heuristic is correct, this makes it possible to avoid duplicate computations (see correctness proof below)
  *)
 Definition mpolynom_eq d n
            (radius: II -> (II -> option II) -> E II)
            (F: list Tube) (phi0: list FF): E Tube :=
   let F' := map mcf F in
   let phi := polynom_eq_oracle d n F' phi0 in
   (* TOTHINK: truncate multiplications (calls to eval', etc)? *)
   let DF := eval' (derive F') phi in
   let A := mfc (interpolate d (fun x => 1 / beval DF x)) in
   let phi := mfc phi in
   match mag (mrange (A * eval' F phi)) with
   | None => err "mpolynom_eq: could not bound the range of A*F(phi)"
   | Some c =>         
       let L := derive (polynom_eq.opnewton F A) in
       let lambda r :=
         let phir := {| pol := pol phi; rem := rem phi + sym r; cont := false |} in
         mag (mrange (eval' L phir))
       in
       LET l ::= radius c lambda IN
       let eps := c / (1 - l) in
       ret {| pol := pol phi; rem := rem phi + sym eps; cont := false |}
   end.

 (** trivial heuristic, where the radius is fixed *)
 Definition fixed_radius r c lambda :=
   let r := F2I r in
   match lambda r with
   | Some l =>
       if is_le 0 r && is_lt l 1 && is_le (c + l * r) r then ret l
       else err "invalid (fixed) radius"
   | None => err "lambda could not be bound for the given (fixed) radius"
   end.

 (** exploration heuristic: 
     tries to find a radius between [r1] and [r2], 
     doing at most [2^k] calls to [lambda]
  *)
 Fixpoint find_radius k r1 r2 c lambda :=
   match k with
   | 0 => err "could not find a radius (fuel exhausted)"
   | S k =>
       let r := F2I r2 in
       if is_le 0 r then 
       match lambda r with
       | Some l =>
           if is_lt l 1 then
             if is_le (c + l * r) r then ret l
             else
               let m := divZ 2 (r1+r2) in
               TRY find_radius k r1 m c lambda
               CATCH find_radius k m r2 c lambda
               (* below, departing from Louis' code: 
                  if lambda(r) is not below 1, we chose the lower branch *)
           else find_radius k r1 (divZ 2 (r1+r2)) c lambda
       | None => find_radius k r1 (divZ 2 (r1+r2)) c lambda
       end
       else err "radius should be positive"
   end.           

 (** testing nullability, [d] is the interpolation degree used for conditionning the problem *)
 Definition mne0 d (M: Tube): bool :=
   let p := mcf M in
   let q := interpolate d (fun x: FF => 1 / beval p x) in
   is_ne 0 (mrange (M * mfc q)).
 
 (** testing positivity, [d] is the interpolation degree used for conditionning the problem  *)
 Definition mgt0 d (M: Tube): E bool :=
   if ~~ cont M then err "mgt0: need a continuous model" else
     (* TOTHINK: in orthogonal bases, sufficient to look at the constant coefficient rather than evaluating at some point (here [lo]) *)
   if ~~ is_lt 0 (meval_unsafe M lo) then ret false
   else ret (mne0 d M).
 
 (** ** correctness of the above operations in valid bases *)

 Context {B: Basis BO}.
 
 Notation eval := (vectorspace.eval TT).
 
 (** containment relation for models *)
 Definition mcontains (M: Tube) (f: R -> R) :=
   wreflect (forall x, dom x -> continuity_pt f x) (cont M)
   /\
   exists p, scontains (pol M) p /\ forall x, dom x -> contains (rem M) (f x - eval p x).

 Lemma mcont M f: cont M -> mcontains M f -> forall x, dom x -> continuity_pt f x.
 Proof. move=>? [C _]. by apply (wreflectE C). Qed. 

 (** extensionality of [mcontains] *)
 (* TOTHINK: is there a way to assume only pointwise equality on the domain in this lemma? *)
 Lemma mcontains_ext M f g : (forall x, (* dom x -> *) f x = g x) -> mcontains M f -> mcontains M g.
 Proof.
   move => Hfg [Cf [f0 [Hf0 Hf]]]. split.
   - elim: Cf=>[Cf|]; constructor=>x Dx. 
     eapply continuity_pt_ext_loc. 2: apply Cf. 2: apply Dx.
     by exists posreal_one.     (* works because HFg is not constrained to the domain *)
   - exists f0; split => // x Hx.
     rewrite -Hfg; auto.
 Qed.
 
 (** *** basic operations *)
 
 Lemma rmeval_unsafe (M: Tube) f:
   mcontains M f -> forall X x, contains X x -> dom x -> contains (meval_unsafe M X) (f x).
 Proof.
   intros [_ (p&Hp&H)] X x Xx HX. rewrite /meval.
   replace (f x) with (eval p x + (f x - eval p x)) by (simpl; ring).
   apply radd; auto. rewrite -evalE. by apply rbeval. 
 Qed.

 Lemma rmeval (M: Tube) f:
   mcontains M f -> forall X x, contains X x -> EP' contains (meval M X) (f x).
 Proof.
   intros Mf X x Xx. rewrite /meval.
   case DomE=>// H. constructor.
   now apply rmeval_unsafe; auto. 
 Qed.
   
 Lemma rdom x: dom x -> contains (bnd lo hi) x.
 Proof. rewrite /dom /Dom. apply bndE. apply rlo. apply rhi. Qed.

 Lemma eval_srange P p x: scontains P p -> dom x -> contains (srange P) (eval p x).
 Proof.
   rewrite /srange => Pp Hx. 
   generalize (rbrange). generalize (eval_range). unfold BI; simpl.
   case brange=>[rangeR eval_rangeR|_]; case brange=>[rangeI rrange|] =>//.
   - generalize (rrange _ _ Pp).
     generalize (eval_rangeR p _ Hx).
     destruct (rangeI P) as [A C].
     simpl (car (ops0 ROps1)).
     destruct (rangeR p) as [a c] =>/=.
     intros E [Aa Cc]. eapply bndE; eauto.
   - move=>_. rewrite -evalE. apply rbeval=>//. by apply rdom. 
 Qed.   

 Lemma eval_mrange M f : mcontains M f -> forall x, dom x -> contains (mrange M) (f x).
 Proof.
   move => [_ [p [Hp Hf]]] x Hx.
   rewrite /mrange; replace (f x) with (eval p x + (f x - eval p x)); last by rewrite /=; ring.
   apply radd; auto. by apply eval_srange. 
 Qed.
 
 Lemma rmadd: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (madd M P) (f+g).
 Proof.
   move=> M f [Cf [p [Hp Hf]]] P g [Cg [q [Hq Hg]]]. split.
   cbn. elim:Cf=>[Cf|]; elim:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_plus; auto. 
   exists (p+q); split. by apply rsadd.
   move=> x Hx. replace (_-_) with ((f x - eval p x) + (g x - eval q x)).
   apply radd; auto. rewrite eval_add/=/f_bin; ring. 
 Qed.
 
 Lemma rmsub: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (msub M P) (f-g).
 Proof.
   move=> M f [Cf [p [Hp Hf]]] P g [Cg [q [Hq Hg]]]. split.
   cbn. elim:Cf=>[Cf|]; elim:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_minus; auto. 
   exists (p-q); split. by apply rssub.
   move=> x Hx. replace (_-_) with ((f x - eval p x) - (g x - eval q x)).
   apply rsub; auto. rewrite eval_sub/=/f_bin; ring. 
 Qed.

 Lemma rmscal: forall C c, contains C c -> forall M f, mcontains M f -> mcontains (mscal C M) (fun x => c * f x). 
 Proof.
   move=> C c Hc M f [Cf [p [Hp Hf]]]. split.
   cbn. elim:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (sscal c p); split. by apply rsscal.
   move=> x Hx. replace (_-_) with (c*(f x - eval p x)).
   apply rmul; auto. rewrite eval_scal/=; ring. 
 Qed.

 Lemma rmmulZ: forall z M f, mcontains M f -> mcontains (mmulZ z M) (mulZ z f). 
 Proof.
   move=> z M f [Cf [p [Hp Hf]]]. split.
   cbn. elim:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (smulZ z p); split. by apply rsmulZ.
   move=> x Hx. replace (_-_) with (mulZ z (f x - eval p x)).
   apply rmulZ; auto. rewrite eval_mulZ/=/f_unr. ring. 
 Qed.

 Lemma rmdivZ: forall z M f, mcontains M f -> mcontains (mdivZ z M) (divZ z f). 
 Proof.
   move=> z M f [Cf [p [Hp Hf]]]. split.
   cbn. elim:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (sdivZ z p); split. by apply rsdivZ.
   move=> x Hx. replace (_-_) with (divZ z (f x - eval p x)).
   apply rdivZ; auto. rewrite eval_divZ/=/f_unr/Rdiv. ring. 
 Qed.
 
 Lemma rmmul: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (mmul M P) (f*g).
 Proof.
   move=> M f [Cf [p [Hp Hf]]] P g [Cg [q [Hq Hg]]]. split.
   cbn. elim:Cf=>[Cf|]; elim:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_mult; auto. 
   exists (p*q); split. by apply rbmul.
   move=> x Hx.
   replace (_-_) with
       (eval p x * (g x - eval q x) + eval q x * (f x - eval p x) + (f x - eval p x) * (g x - eval q x)) by (rewrite eval_mul/=/f_bin; ring).
   apply radd. apply radd.
   - apply rmul. by apply eval_srange. by apply Hg. 
   - apply rmul. by apply eval_srange. by apply Hf. 
   - rel. 
 Qed.
 
 Lemma rmsingle P p: scontains P p -> mcontains (msingle P) (eval p).
 Proof.
   intros. split. constructor=>x Dx. apply eval_cont.
   exists p. split=>// x Hx.
   replace (_-_) with R0 by (simpl; ring). 
   apply rzer.
 Qed.

 Lemma rmsingle' P p f: scontains P p -> (forall x, (* dom x -> *) eval p x = f x) -> mcontains (msingle P) f.
 Proof. intros Pp H. apply (mcontains_ext H). by apply rmsingle. Qed.
 
 Lemma rmzer: mcontains mzer 0.
 Proof. eapply rmsingle'. constructor. reflexivity. Qed.
 
 Lemma rmone: mcontains mone 1.
 Proof. eapply rmsingle'. apply rbone. apply eval_one. Qed.
 
 Lemma rmid: EP' mcontains mid ssrfun.id.
 Proof.
   unfold mid. generalize eval_id. case rbid. 2: constructor.    
   intros bid bid' rbid H. inversion_clear H. constructor.
   eapply rmsingle'; eauto.
 Qed.
 
 Lemma rmcos: EP' mcontains mcos (@cos _).
 Proof.
   unfold mcos. generalize eval_cos. case rbcos. 2: constructor.    
   intros bcos bcos' rbcos H. inversion_clear H. constructor.
   eapply rmsingle'; eauto.
 Qed.
 
 Lemma rmsin: EP' mcontains msin (@sin _).
 Proof.
   unfold msin. generalize eval_sin. case rbsin. 2: constructor.    
   intros bsin bsin' rbsin H. inversion_clear H. constructor.
   eapply rmsingle'; eauto.
 Qed.
 
 Lemma rmnth n: mcontains (mnth n) (TT n).
 Proof. eapply rmsingle'. apply rsnth. apply eval_nth. Qed.
 
 Lemma rmcst C (c : R): contains C c -> mcontains (mcst C) (f_cst c).
 Proof.
   move=>H. eapply mcontains_ext. 2: apply rmscal. 2: apply H. 2: apply rmone.
   cbv. move=>_. ring.
 Qed.
 
 Lemma rmbot f: mcontains mbot f.
 Proof.
   split. constructor. 
   exists 0; split. apply rszer.
   intros. apply botE.
 Qed.

 Canonical Structure mcontains_Rel0: Rel0 MOps0 (f_Ops0 R ROps0) :=
   {|
     rel := mcontains;
     radd := rmadd;
     rsub := rmsub;
     rmul := rmmul;
     rzer := rmzer;
     rone := rmone;    
     rmulZ := rmmulZ;
     rdivZ := rmdivZ;
   |}.

 Lemma rmtruncate n: forall F f, mcontains F f -> mcontains (mtruncate n F) f.
 Proof.
   intros F f [Cf (p&Hp&H)]. unfold mtruncate.
   generalize (rsplit_list n Hp).
   generalize (eval_split_list TT n p).  
   simpl. case split_list=> p1 p2.
   case split_list=> P1 P2. simpl. 
   intros E [R1 R2]. split. exact Cf. 
   exists p1. split=>//. 
   intros x Hx.  
   replace (_-_) with ((f x - eval p x) + eval p2 x) by (rewrite E; simpl; ring).
   apply radd. by apply H. by apply eval_srange.
 Qed.

 Lemma rmcontinuous: forall F f,
     (forall x, dom x -> continuity_pt f x) -> mcontains F f -> mcontains (mcontinuous F) f.
 Proof.
   intros F f Cf Ff. split. constructor. exact Cf. apply Ff. 
 Qed.

 Definition model_ops: ModelOps := {|
   MM := MOps0;
   interfaces.mid := mid;
   interfaces.mcos := mcos;
   interfaces.msin := msin;
   interfaces.mcst := mcst;
   interfaces.meval := meval;
   interfaces.mintegrate := mintegrate;
   interfaces.mdiv := mdiv;
   interfaces.msqrt := msqrt;
   interfaces.mtruncate := mtruncate;
   interfaces.mrange := mrange;
   interfaces.mne0 := mne0;               
   interfaces.mgt0 := mgt0;               
 |}.

   (** *** integration *)

 Lemma RInt_min a d u f:
   a<d -> (forall x, a<=x<=d -> u <= f x) -> ex_RInt f a d ->
   u <= RInt f a d / (d-a).
 Proof.
   intros ad Hu Hf. apply Rle_div_r. lra.
   transitivity (RInt (fun _ => u) a d).
   rewrite RInt_const Rmult_comm. apply Rle_refl. 
   apply RInt_le=>//. lra. apply ex_RInt_const.
   intros. apply Hu. lra.
 Qed.

 Lemma RInt_max a d v f:
   a<d -> (forall x, a<=x<=d -> f x <= v) -> ex_RInt f a d ->
   RInt f a d / (d-a) <= v.
 Proof.
   intros ad Hv Hf. apply Rle_div_l. lra.
   transitivity (RInt (fun _ => v) a d).
   apply RInt_le=>//. lra. apply ex_RInt_const.
   intros. apply Hv. lra.
   rewrite RInt_const Rmult_comm. apply Rle_refl. 
 Qed.   

 Lemma cont_ex_RInt a d f: dom a -> dom d -> (forall x, dom x -> continuity_pt f x) -> ex_RInt f a d.
 Proof.
   rewrite /dom=> A D H.
   apply ex_RInt_Reals_1; case: (Rle_dec a d) => Hab; [ | apply RiemannInt.RiemannInt_P1];
     apply RiemannInt.continuity_implies_RiemannInt=>//; try lra; move => t Ht; apply H; lra.
 Qed.   
 
 Lemma rmintegrate_unsafe: forall M f, 
     mcontains M f -> (forall x, dom x -> continuity_pt f x) ->
     forall A a, contains A a -> dom a ->
     forall D d, contains D d -> dom d -> contains (mintegrate_unsafe M A D) (RInt f a d).
 Proof.
   move => M f [_ [p [Hp Hf]]] Hfcont A a Ha HA D d Hd HD; rewrite /mintegrate.
   have Hfint : ex_RInt f a d by apply cont_ex_RInt. 
   have Hpint : ex_RInt (eval p) a d by apply cont_ex_RInt; last (intros; apply eval_cont).
   have Hfpint : ex_RInt (f - eval p) a d by apply @ex_RInt_minus with (V:=R_NormedModule).
   rewrite (RInt_ext _ (eval p+(f-eval p))); last by (move => x _; rewrite /=/f_bin; lra).
   rewrite RInt_plus => //; first apply radd.
   rewrite -integrateE. rel. 
   case (Req_dec a d) => ad.
   destruct ad. replace (RInt _ _ _) with (RInt (fun _ => f a - eval p a) a a).
     by rewrite RInt_const; apply rmul; rel.
     apply RInt_ext. intro. unfold Rmin, Rmax. lra.
   replace (RInt _ _ _) with ((d-a) * (RInt (f-eval p) a d / (d-a))) by (simpl; field; lra).
   apply rmul. rel.   
   clear - ad HA HD Hfpint Hf.
   wlog: a d ad HA HD Hfpint / a < d.
   destruct (total_order_T a d) as [[ad'|ad']|ad'] => H.
   - apply H=>//.
   - congruence. 
   - rewrite -opp_RInt_swap; last by apply ex_RInt_swap.
     replace (_/_) with ((RInt (f-eval p) d a / (a-d))) by (rewrite /opp/=; field; lra).
     apply H=>//. congruence. by apply ex_RInt_swap.
   move=>{ad}=>ad. 
   
   case (minE (rem M)) => [U u Uu rMu|] Hu.
   have Hu': forall x, dom x -> u <= f x - eval p x. by intros; apply Rge_le, Hu, Hf.
   have Hu'': u <= RInt (f-eval p) a d / (d-a).
     apply RInt_min=>//. intros. apply Hu'. unfold dom in * ; lra. 
   case (maxE (rem M)) => [V v Vv rMv|] Hv.
   have Hv': forall x, dom x -> f x - eval p x <= v. by intros; apply Hv, Hf.
   have Hv'': RInt (f-eval p) a d / (d-a) <= v.
     apply RInt_max=>//. intros. apply Hv'. unfold dom in * ; lra. 
   apply convex with u v =>//. 
   eapply Hv. apply rMu. apply Hu''.
   case (maxE (rem M)) => [V v Vv rMv|] Hv.
   have Hv': forall x, dom x -> f x - eval p x <= v. by intros; apply Hv, Hf.
   have Hv'': RInt (f-eval p) a d / (d-a) <= v.
     apply RInt_max=>//. intros. apply Hv'. unfold dom in * ; lra. 
   eapply Hu. apply rMv. apply Rle_ge, Hv''.
   specialize (Hf _ HA).
   case (Rle_lt_dec (RInt (f-eval p) a d/(d-a)) (f a-eval p a))=>E.  
   eapply Hu. apply Hf. by apply Rle_ge. 
   eapply Hv. apply Hf. by apply Rlt_le. 
 Qed.

 (** here we deduce the requirements of [rmintegrate_unsafe] from purely computational assumptions 
     it might be useful to use directly [mintegrate_unsafe] and [rmintegrate_unsafe] depending on the target application
  *)

 Lemma rmintegrate: forall M f, 
     mcontains M f -> 
     forall A a, ocontains lo A a -> 
     forall D d, ocontains hi D d -> EP' contains (mintegrate M A D) (RInt f a d).
 Proof.
   intros M f Mf A a Aa D d Dd.
   rewrite /mintegrate.
   elim:(proj1 Mf)=>[Cf|]. 2: constructor.
   destruct Aa as [Aa|]; destruct Dd as [Dd|].
   - case DomE=>//= Da. case DomE=>//= Db. 
     constructor. now apply rmintegrate_unsafe; auto.
   - case DomE=>//= Da.
     constructor. apply rmintegrate_unsafe; try rel. apply domhi.
   - case DomE=>//= Db.
     constructor. apply rmintegrate_unsafe; try rel. apply domlo.
   - constructor. apply rmintegrate_unsafe; try rel. apply domlo. apply domhi.
 Qed.

 (** auxiliary lemma for operations involving interpolation *)
 Lemma rmfc p: mcontains (mfc p) (eval (map F2R p)).
 Proof. apply rmsingle, list_rel_map, F2IE. Qed.
 
 (** *** division *)
 
 Lemma rmdiv_aux F G f g H W:
   mcontains F f -> mcontains G g ->
   EP' mcontains (mdiv_aux F G H W) (f_bin Rdiv f g).
 Proof.
   move => Hf Hg. rewrite /mdiv_aux.
   case magE => [Mu mu MU Hm|]=>//. 
   case magE => [b c bc Hc|]=>//.
   case is_ltE => [Hmu|]=>//.
   specialize (Hmu _ 1 MU (rone _)).
   pose proof (Hh := rmfc H). set (h := eval (map F2R H)) in *.
   pose proof (HW := rmfc W). set (w := eval (map F2R W)) in *.
   destruct (ssrfun.id Hh) as [_ [p [Hp Hh']]].
   have L: forall x, dom x -> g x <> 0 /\ Rabs (h x - f x / g x) <= c / (R1 - mu).
     move=> x Dx; refine (div.newton _ _ _ _ Dx) => //.
     + move => t Ht; apply Hm.
       apply eval_mrange with (f := 1-w*g) =>//.
         by apply rmsub; [apply rmone|apply rmmul].
     + move => t Ht; apply Hc. 
       apply eval_mrange with (f := w*(g*h-f)) =>//.
         by apply rmmul; last (apply rmsub; first apply rmmul).
     + lapply (fun H => Hm _ (eval_mrange (f:=1-w*g) H Dx)).
       move => E; split =>//. rewrite <-E. apply Rabs_pos.
       apply rmsub. apply rmone. by apply rmmul.
     + lapply (fun H => Hc _ (eval_mrange (f:=w*(g*h-f)) H Dx)).
       intros <-. apply Rabs_pos.
       apply rmmul=>//. apply rmsub=>//. by apply rmmul.
   constructor. split.
   - elim:(proj1 Hf)=>[Cf|]; elim:(proj1 Hg)=>[Cg|]; constructor=>x Dx.
     apply continuity_pt_div; auto. by apply L. 
   - exists p; split=>//=.
     move => x Hx. rewrite /f_bin.
     replace (_-_) with ((h x - eval p x) + -(h x - f x / g x)); last by rewrite /=; ring.
     apply radd. by apply Hh'.
     apply symE with (c / (1 - mu)) => /=; last by rel. 
     rewrite Rabs_Ropp. by apply L. 
 Qed.

 Lemma rmdiv d:
   forall M f, mcontains M f ->
   forall N g, mcontains N g -> EP' mcontains (mdiv d M N) (f_bin Rdiv f g).
 Proof. intros; by apply rmdiv_aux. Qed.

 (** *** square root *)

 Lemma rmsqrt_aux F f H W:
   mcontains F f -> 
   EP' mcontains (msqrt_aux F H W) (fun x => R_sqrt.sqrt (f x)).
 Proof.
   move => Hf. rewrite /msqrt_aux.
   pose proof (Hh := rmfc H). set (h := eval (map F2R H)) in *.
   pose proof (Hw := rmfc W).
   pose proof (Hwcont := eval_cont (map F2R W)). set (w := eval (map F2R W)) in *.
   set (x0:=(lo+hi)//2).
   have domx0: dom ((lo+hi)/2) by generalize domlo; generalize domhi; rewrite /dom; lra. 
   have rx0: contains x0 ((lo+hi)/2) by rel.
   case is_ltE => [Hwx0|]=>[|//=]. 
   specialize (Hwx0 _ _ (rzer _) (rmeval_unsafe Hw rx0 domx0)).
   simpl negb.
   case magE => [Mu0 mu0 MU0 Hmu0|]=>[|//=]. 
   case magE => [Mu1 mu1 MU1 Hmu1|]=>[|//=].
   case magE => [BB b Bb Hb|]=>[|//=].
   case is_ltE =>// Hmu01. specialize (Hmu01 _ _ MU0 (rone _)).
   case is_ltE =>// Hmu0b. 
   destruct (ssrfun.id Hh) as [_ [p [Hp Hh']]].
   case is_ltE => [Hmu|] =>//.
   lapply (fun H x Hx => Hmu0 _ (eval_mrange (x:=x) (f:=fun x => 1 - 2 * (w x*h x)) H Hx)); last first.
    apply rmsub. apply rmone. apply rmmulZ. by apply rmmul.
    intro Hmu0'. 
   pose proof (fun x Hx => Hmu1 _ (eval_mrange (x:=x) Hw Hx))as Hmu1'.
   lapply (fun H x Hx => Hb _ (eval_mrange (x:=x) (f:=w*(h*h-f)) H Hx));
     last by apply rmmul => //; apply rmsub => //; apply rmmul.
   intro Hb'. 
   have L: forall x, dom x -> 0 <= f x /\ Rabs (h x - sqrt (f x)) <= sqrt.rmin b mu0 mu1.
     (unshelve eapply (sqrt.newton (w:=w) _ _ _ _ _ _ _ _ _ _ _)) =>//.
     + move => t Ht; rewrite Rmult_assoc. by apply Hmu0'.
     + move => t Ht /=; rewrite Rmult_1_r. by apply Hb'.
     + split=>//. rewrite <-(Hmu0' _ domx0). apply Rabs_pos. 
     + apply Rlt_le_trans with (Rabs (w ((lo+hi)/2))); eauto.
       clear -Hwx0. split_Rabs; simpl in *; lra.
     + rewrite <- (Hb' _ domx0). apply Rabs_pos.
     + apply Rlt_le, Hmu0b; rel. 
     + apply Hmu; rel. 
     + unfold dom. clear. intros; simpl in *; lra. 
     + exists ((lo+hi)/2). split. apply domx0. apply Hwx0. 
   constructor. split. 
   - elim:(proj1 Hf)=>[Cf|]; constructor=>x Dx.
     apply (continuity_pt_comp f). apply Cf, Dx. 
     apply continuity_pt_sqrt. by apply L. 
   - exists p; split =>// x Hx.
     replace (_-_) with ((h x - eval p x) + -(h x - R_sqrt.sqrt (f x))); last by rewrite /=; ring.
     apply radd; first by apply Hh'.
     set rmin := sqrt.rmin b mu0 mu1.
     eapply symE with rmin; first last. rel. 
     rewrite Rabs_Ropp. by apply L.       
 Qed.

 Lemma rmsqrt d M f: 
   mcontains M f -> EP' mcontains (msqrt d M) (f_unr R_sqrt.sqrt f).
 Proof. by apply rmsqrt_aux. Qed.

 (** *** solutions of polynomial functional equations *)

 Lemma rmpolynom_eq_aux
       (F': list Tube) (phi' A': list FF) (r': II)
       (F: list (R->R)) (r: R):
   list_rel mcontains F' F ->
   contains r' r ->
   0 <= r ->
   EP (fun M => exists f, mcontains M f /\ forall t, dom t ->  eval' F f t = 0) (mpolynom_eq_aux F' phi' A' r').  
 Proof.
   move => HF Hr0. rewrite /mpolynom_eq_aux.
   pose proof (Hphi := rmfc phi'). set (phi := eval (map F2R phi')) in *.
   pose proof (HA := rmfc A'). set (A := eval (map F2R A')) in *.
   case magE => [lambda' lambda clambda Hlambda | ] => [ | //].
   case magE => [ d' d cd Hd | ] => [ | //].
   case is_ltE => [Hl1|]=>[|//].
   case is_leE => [Hdlr|] => [|//]. constructor.
   move : (id Hphi) => [ _ [ p [ Hp1 Hp2 ]]]. 
   have Hnewton : exists f, forall t, dom t ->  eval' F f t = 0 /\ Rabs ( f t - phi t ) <= d / (1 - lambda).
   apply polynom_eq.newton with A r.
   + move => s Hs t Dt.
     apply Hlambda, eval_mrange => //. apply taylor.reval. apply taylor.rderive. rel.
     split; first constructor.
     exists p; split => //.
     move => x Dx /=.
     replace ( _ - _) with ( (phi x - eval p x ) + ( s x - phi x) ) by (simpl;ring).
     apply radd. apply Hp2 => //.
     apply symE with r => //. rewrite Rabs_minus_sym. apply Hs => //. 
   + move => t Dt.
     apply Hd.
     move : t Dt. apply eval_mrange, rmmul => //. apply taylor.reval => //.
   + split. 2 : apply Hl1 => //; rel.
     apply Rle_trans with (Rabs ( eval' (derive (polynom_eq.opnewton F A)) phi hi)).
     apply Rabs_pos.   
     apply Hlambda, eval_mrange. apply taylor.reval. apply taylor.rderive => //. rel.
     split ; first constructor.
     exists p; split => //=.
     move => x Dx /=.
     replace ( _ - _) with ( (phi x - eval p x ) + 0 ) by (simpl;ring).
     apply radd. apply Hp2 => //. apply symE with r => //. by rewrite Rabs_R0. apply domhi.
   + eapply Rle_trans with (Rabs _). 
     apply Rabs_pos. apply Hd, eval_mrange. apply rmmul. rel.
     apply taylor.reval. apply HF. apply Hphi. apply domhi.
   + by [].
   + apply Hdlr; rel.

   move : Hnewton => [ f Hnewton].
   exists f; split. 2 : apply Hnewton.
   split; first constructor.
   exists p; split => //.
   move => x Dx /=.
   replace (_ - _) with ((phi x - eval p x) +  (f x - phi x )) by (simpl;ring).
   apply radd. by apply Hp2.
   eapply symE. 2: rel.
   by apply Hnewton.
 Qed.

 Definition correct_radius (radius: II -> (II -> option II) -> E II) :=
   forall c lambda, EP (fun l => exists r rr, contains r rr /\ lambda r = Some l /\ 0<=rr /\ is_lt l 1 /\ is_le (c+l*r) r)
                  (radius c lambda).

 (** [mpolynom_eq] essentially is an instance of [mpolynom_eq_aux] *)
 Lemma mpolynom_eq_link d n radius F phi0:
   correct_radius radius ->
   EP (fun M => exists phi A r' r, ret M = mpolynom_eq_aux F phi A r' /\ contains r' r /\ 0 <= r)
      (mpolynom_eq d n radius F phi0).
 Proof.
   move => HR. rewrite /mpolynom_eq.
   set (A' := interpolate _ _). set (A := mfc _).
   set (phi' := polynom_eq_oracle _ _ _ _). set (phi := mfc _).
   set (m := mag _). case_eq m=>//c Hc. case HR=>//= l.
   intros (r&rr&Hr&Hl&Hrr&Hl1&Hlr). constructor.
   unfold mpolynom_eq_aux.
   exists phi', A', r, rr. 
   rewrite -/A -/phi -/m Hc Hl Hl1 Hlr.
   eauto using rmfc. 
 Qed.

 (** whence its correctness *)
 Lemma rmpolynom_eq d n radius F' F phi0:
   correct_radius radius ->
   list_rel mcontains F' F ->  
   EP (fun M => exists f, mcontains M f /\ forall t, dom t ->  eval' F f t = 0)
      (mpolynom_eq d n radius F' phi0).
 Proof.
   move => HR HF. case (mpolynom_eq_link _ _ _ _ HR)=>//M.
   intros (phi&A&R&r&->&?&?). eapply rmpolynom_eq_aux; eauto. 
 Qed.

 (** correctness of the heuristics for finding radiuses *)
 Lemma correct_fixed_radius r: correct_radius (fixed_radius r).
 Proof.
   intros c lambda. unfold fixed_radius.
   case_eq (lambda (F2I r))=>//l.
   set (P := _ && _). case_eq P=>// HP Hl. constructor.
   do 2 eexists. split. apply F2IE. split. eassumption.
   subst P. move:HP=>/andP[/andP[Hr Hl1] Hcl]. intuition.
   move:Hr. case is_leE=>//H _. apply H. rel. apply F2IE.
 Qed.

 Lemma correct_find_radius k r1 r2:
   correct_radius (find_radius k r1 r2).
 Proof.
   intros c lambda. revert r1 r2. 
   induction k=>/=r1 r2. constructor.
   case is_leE=>//. move=>Hr2.
   case_eq (lambda (F2I r2))=>//l Hl.
   case_eq (is_lt l 1)=>//Hl1.
   case_eq (is_le (c + l * F2I r2) (F2I r2))=>Hcl.
   - constructor.
     exists (F2I r2). eexists. split. apply F2IE. intuition.
     apply Hr2. rel. apply F2IE.
   - case IHk=>//=. by constructor.  
 Qed. 

 (** *** non-nullability test *)
 Lemma rmne0 n M f: mcontains M f -> mne0 n M -> forall x, dom x -> f x <> 0.
 Proof.
   rewrite /mne0=>Mf H x Hx E. 
   set M' := interpolate _ _ in H. 
   set f' := eval (map F2R M').
   have E': (f x * f' x = 0) by rewrite E/=; ring. revert E'.
   move: H. case is_neE=>// H _.
   apply nesym. apply H. rel. 
   apply (eval_mrange (f:=fun x => f x * f' x))=>//. apply rmmul=>//.
   apply rmfc.
 Qed.

 (** *** positivity test *)
 
 Lemma continuous_gt0 f:
   (forall x, dom x -> continuity_pt f x) ->
   (forall x, dom x -> f x <> 0) ->
   forall x0, dom x0 -> 0 < f x0 ->
   forall x, dom x -> 0 < f x.
 Proof.
   move=>Cf H y Dy Hy x Dx.
   apply Rnot_ge_lt=>Hx'.
   have Hx: f x < 0. move: (H _ Dx); cbn; lra. clear Hx'.
   wlog xy: f Cf H x y Dx Dy Hx Hy / (x < y).
    case (Rtotal_order x y)=>[xy|[xy|xy]].
    eauto. subst; lra. move=>E. apply (E (fun x => - f x)) with y x=>//; try lra.
    - move=>*. by apply continuity_pt_opp, Cf. 
    - move=>z Dz. move: (H z Dz). cbn; lra. 
   unfold dom in *.
   case (Ranalysis5.IVT_interv f x y)=>//.
    intros; apply Cf; lra.
   move=> z [Dz Hz]. apply H in Hz; lra. 
 Qed.
 
 Lemma rmgt0 n M f: mcontains M f -> EPimpl (mgt0 n M) (forall x, dom x -> 0 < f x).
 Proof.
   rewrite /mgt0. case_eq (cont M)=>Cf Mf. 2: constructor.
   case is_ltE; constructor=>// H'. apply continuous_gt0 with lo.
   - by eapply mcont; eauto.
   - eapply rmne0; eassumption.
   - exact domlo.
   - apply H. rel. apply rmeval_unsafe=>//. rel.
     exact domlo.
 Qed.

 (** packing all operations together *)
 Program Definition model: Model model_ops lo hi := {|
   interfaces.mcontains := mcontains_Rel0;
   interfaces.rmid := rmid;
   interfaces.rmcos := rmcos;
   interfaces.rmsin := rmsin;
   interfaces.rmcst := rmcst;
   interfaces.rmeval := rmeval;
   interfaces.rmintegrate := rmintegrate;
   interfaces.rmdiv := rmdiv;
   interfaces.rmsqrt := rmsqrt;
   interfaces.rmtruncate := rmtruncate;
   interfaces.rmrange := eval_mrange;               
   interfaces.rmne0 := rmne0;               
   interfaces.rmgt0 := rmgt0;               
 |}.

End n.
Arguments model_ops {_} _.
Arguments model {_ _} _.

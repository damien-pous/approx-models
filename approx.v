(** * Rigorous approximations in a generic basis *)

Require Import String. 
Require Import vectorspace.
Require div sqrt polynom_eq.
Require Import utils.

From ReductionEffect Require Import PrintingEffect.

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
 Notation Tube := (Tube (@car (@ops0 (@II N)))).
 Notation eval' := taylor.eval't.
 Notation derive := taylor.derive.
 
 (** range of a polynomial *)
 Definition srange p: II :=
   match brange with
   | None => beval p (interval lo hi)
   | Some range => let (m,M):=range p in interval m M
   end.
 (** corresponding function in (unspecified) flating points *)
 Definition frange p: E (FF*FF) :=
   match brange with
   | None =>
       let r := beval (map F2I p) (interval lo hi) in
       match min r,max r with
       | Some m, Some M => ret (I2F m, I2F M)
       | _,_ => err "could not estimate the range"
       end
   | Some range => ret (range p)
   end.
 
 (** truncation of a model *)
 Definition mtruncate (n: nat) (M: Tube): Tube :=
   let (p,q) := split_list n (pol M) in 
   {| pol := p; rem := rem M + srange q; cont := cont M |}.

 (** model with empty remainder *)
 Definition msingle p: Tube := {| pol := p; rem := 0; cont := true |}.

 (** uninformative model  *)
 Definition mfull: Tube := {| pol := 0; rem := full; cont := false |}.

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
 Definition mmul (M N: Tube): Tube :=
   {| pol := pol M * pol N;
      rem := srange (pol M) * rem N + srange (pol N) * rem M + rem M * rem N;
      cont := cont M && cont N; |}.
 Definition mzer: Tube := msingle 0.
 Definition mone: Tube := msingle 1.
 Definition mmul' d M N := mtruncate d (mmul M N).

 (** by defining this structure, we get nice notations for the above operations on models *)
 Canonical Structure MOps0: Ops0 :=
   {|
     car:=Tube;
     add:=madd;
     sub:=msub;
     mul:=mmul;
     mul':=mmul';
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

 (** infinite norm *)
 Definition mnorm (M: Tube): E II :=
   match mag (mrange M) with Some m => ret m | None => err "not bounded" end.

 (** same function on floating points (unspecified)  *)
 (* Definition fnorm M := e_map I2F (mnorm (mcf M)). *)
 Definition fnorm (P: list FF): E FF :=
   elet '(m,M) := frange P in ret (Fmax (Fabs m) (Fabs M)).

 (** asserting continuity 'by hand' (see specification [rmcontinuous] below)*)
 Definition mcontinuous (M: Tube): Tube :=
   {| pol := pol M; rem := rem M; cont := true |}.

 (** auxiliary conversion functions to perform interpolation with floating points *)
 Definition mcf (M: Tube): list FF := map I2F (pol M).
 Definition mfc (p: list FF): Tube := {| pol := map F2I p; rem := 0; cont := true |}.
 
 (** division: H and W are given by an oracle
     [t] is the truncation degree
     H ~ F/G
     W ~ 1/G *)
 Definition mdiv_aux (t: option nat) (H W: list FF) (F G: Tube): E Tube :=
   let H := mfc H in
   let W := mfc W in
   let K1 := 1 - W*G in
   let K2 := W*(G*[.t]H - F) in
   elet mu := mnorm K1 in
   elet b := mnorm K2 in
   if is_lt mu 1 then ret {| pol := pol H; rem := sym (b / (1 - mu)); cont := cont F && cont G; |}
   else err "mdiv: missed mu<1".

 (** square root: H and W are given by an oracle 
     [t] is the truncation degree
     H ~ sqrt F
     W ~ 1 / 2H *)
 Definition msqrt_aux (t: option nat) (H W: list FF) (F: Tube): E Tube :=
   let H := mfc H in
   let W := mfc W in
   let x0' := (lo+hi)//2 in
   let y0' := meval_unsafe W x0' in
   if ~~ is_lt 0 y0' then err "msqrt: potentially negative value" else
   let K1 := 1 - (mmulZ 2 (W*H)) in
   (* TOTHINK: better way to compute (truncated) H^2 ? *)
   let K2 := W*(H*[.t]H - F) in
   elet mu0 := mnorm K1 in
   elet mu1 := mnorm W in
   elet b := mnorm K2 in
   let delta := pow 2 (1 - mu0) - mulZ 8 b * mu1 in
     if is_lt mu0 1 then
       if is_lt 0 delta then
         let rmin := (1 - mu0 - sqrt delta)/(mulZ 4 mu1) in
         let mu := mu0 + mulZ 2 mu1 * rmin in
         if is_lt mu 1 then ret {| pol := pol H; rem:=sym rmin; cont := cont F |}             
         else err "msqrt: missed mu<1"
       else err "msqrt: missed 0<delta"
     else err "msqrt: missed mu0<1".

 (** division and square root, using interpolation as oracle ; 
     [d] is the interpolation degree, 
     [t] is the truncation degree *)
 Definition mdiv d t (M N: Tube): E Tube :=
   (* partial application of [beval] enables precomputation and sharing of potential list reversals *)
   let p := beval (mcf M) in    
   let q := beval (mcf N) in
   mdiv_aux t (interpolate d (fun x => p x / q x)) (interpolate d (fun x => 1 / q x)) M N.
 Definition msqrt d t (M: Tube): E Tube :=
   (* partial application of [beval] enables precomputation and sharing of potential list reversals *)
   let p := beval (mcf M) in
   let h := interpolate d (fun x => sqrt (p x)) in
   let h' := beval h in
   msqrt_aux t h (interpolate d (fun x => 1 / (mulZ 2 (h' x)))) M.

 (** solution of polynomial equation : F is a polynom with model coefficients
     - [t] is the truncation degree
     - [phi], [A] are given by an oracle, such that F(phi) ~ 0 and A ~ 1 / DF(phi)
     - [r] is a radius also given by an oracle, such that the Newton operator is stable and lambda contracting on B(phi,r) *) 
 Definition mpolynom_eq_aux t (F: list Tube) (phi A: list FF) (r: FF): E Tube :=
   let phi := mfc phi in
   let A := mfc A in
   let r := F2I r in 
   let phir := {| pol := pol phi ; rem := sym r ; cont := false |} in
   elet lambda := mnorm (eval' t (derive (polynom_eq.opnewton F A)) phir) in
   elet c := mnorm (A * eval' t F phi) in
   if is_lt lambda 1 then
     if is_le (c + lambda * r) r then
       let eps := c / (1 - lambda) in
       ret {| pol := pol phi; rem := sym eps; cont := false |}
     else err "mpolynom_eq_aux : missed (d+lambda*r)<=r"
   else err "mpolynom_eq_aux : missed lambda<1".

 (** Newton method for finding a root of a function [f] with derivative [f'] *)
 Definition Newton_basic s f f' :=
   let w := fromQ 0.000001 in    (* expected precision *)
   let k := 10%Z in              (* maximal number of iterations *)
   (fix iter n x :=
      match n with
      | O => err (append "Newton: could not find a root" s)
      | S n =>
          let d := f x / f' x in
          if Fle (Fabs d) w then ret x
          else iter n (x-d)
      end) 10%nat.
 
 (** improved(?) version:
     - look for a reasonable candidate with k=10 iterations (|f x| <= 0.001 = w)
     - then iterate until there was no improvement for m=5 iterations in a row
     - fail if those iterations seem to diverge (move more than i=10 times away from best solution)
  *)
 Definition Newton s f f' :=
   let k := 10%nat in             (* number of iterations to find a first candidate *)
   let w := fromQ 0.001 in       (* treshold for absolute value of [f] on first candidate *)
   let m := 5%nat in              (* maximal number of non-improving iterations *)
   let i := 10%Z in              (* treshold for detecting instability *)
   let optimise :=
     Fix (fun iter n x fx xbest best =>
            match n with
            | O => ret xbest
            | S n =>
                let d := fx / f' x in
                let x := x - d in
                let fx := f x in
                let afx := Fabs fx in
                if Flt afx best then iter m x fx x afx (* found a better point *)
                else if Fle afx (mulZ i best) then iter n x fx xbest best (* not better, but there is hope *)
                else err (append "Newton: computation seems unstable" s)
            end) (fun _ _ _ _ _ => err "assert false") m
   in
   (fix iter n x :=
      match n with
      | O => err (append "Newton: not close to a root after 10 iterations (" s)
      | S n =>
          let fx := f x in
          let d := fx / f' x in
          if Fle (Fabs d) w then optimise x fx x (Fabs fx)
          else iter n (x-d)
      end) k.
 
 (** special case of a polynomial *)
 Definition Newton_poly s p :=
   let p' := derive p in
   Newton s (taylor.eval' p) (taylor.eval' p').
 
 (** oracle for solutions of polynomial equations:
     by interpolation, using Newton's method to approximate the solution at the interpolation points
     - [d] is the interpolation degree 
     - [phi0] is a preliminary candidate *)
 Definition polynom_eq_oracle d (F: list (list FF)) (phi0: list FF): list FF :=
   let f t :=
     let p := map (fun f => beval f t) F in
     let x0 := beval phi0 t in
     match Newton_poly "(oracle)" p x0 with
     | ret x => x
     | err _ => x0
     end
   in
   interpolate d f.

 Fixpoint taylorise n fn l: list FF :=
   match l with
   | [] => []
   | x::q =>
       let n := Z.succ n in 
       divZ fn x :: taylorise n (Z.mul n fn) q
   end.
 (* Eval simpl in fun a b c d => xtaylorise 0 1 [a;b;c;d]. *)
 
 (** || L(phi+r) || = || \sum_i L^(i)(phi)/!i r^i || <= \sum_i ||L^(i)(phi)/!i|| r^i 
     rather fine, but O(d^2) model multiplications,
     and possibly too fine (finer than what is used in validation, cf. oval example at degree 20)
  *)
 Definition polynom_for_lambda1 t (L: list (list FF)) (phi: list FF): E (list FF) :=
   elet l :=
     Fix (fun lambda L => 
       match L with
       | [] => ret []
       | _ => elet r := fnorm (eval' t L phi) in
              elet q := lambda (derive L) in
              ret (r::q)
       end) (fun _ => err "assert false") L
   in ret (taylorise 0 1 l).

 (** ... <= ||L(phi)|| + \sum_i>0 ||L||^(i)(||phi||)/!i r^i 
     only O(d) model multiplications, and probably closer to the estimation used during validation
  *)
 Definition polynom_for_lambda2 t (L: list (list FF)) (phi: list FF): E (list FF) :=
   elet l0 := fnorm (eval' t L phi) in
   elet Nphi := fnorm phi in
   elet NL := emap fnorm L in
   let l' :=
     Fix (fun lambda NL => 
       match NL with
       | [] => []
       | _ => eval' t NL Nphi :: lambda (derive NL)
       end) (fun _ => 0) (derive NL)
   in ret (l0 :: taylorise 1 1 l'). 

 Definition polynom_for_lambda := polynom_for_lambda2. (* vs 1 *)
 
 Definition find_radius_alamano (c: FF) (l: list FF): E FF :=
   let w := fromQ 0.0000001 in
   (* l is a polynomial with positive coefficients; d is positive; thus p is convex *)
   let p := c::(l-[1]) in
   let _ := print p in
   let p' := derive p in
   (* BELOW: replace with a simpler Newton method ? *)
   (* a value such that 0<=p'(max) *)
   let max :=
     Fix (fun find_max m =>
            if Fle 0 (taylor.eval' p' m) then m
            else find_max (mulZ 2 m)) id 1 in
   (* a value such that p(r)<=0, close to the root of p', if any *)
   let _ := print max in
   elet r :=
     Fix (fun get_close a b =>     (* [a;b] contains and gets close to the root of p' *)
            if Fle (taylor.eval' p a) 0 then ret a else
            if Fle (b-a) w then err "could not find a radius" else
            let c := divZ 2 (a+b) in
            if Fle 0 (taylor.eval' p' c) then get_close a c else get_close c b
         ) (fun _ _ => err "assert false") 0 max
   in
   let _ := print r in
   (* optimisation of the above value *)
   elet r :=
   Fix (fun optimise a b =>        (* [a;b] contains and gets close to the first root of p *)
          if Fle (b-a) w then ret b else 
          let c := divZ 2 (a+b) in
          if Fle (taylor.eval' p c) 0 then optimise a c else optimise c b
       ) (fun _ _ => err "assert false") 0 r
   in
   let _ := print "final radius and associated bound on lambda"%string in
   let _ := print (r, taylor.eval' l r) in
   ret r.

 Definition find_radius_newton (c: FF) (l: list FF): E FF :=
   (* l is a polynomial with positive coefficients; d is positive; thus p is convex *)
   let p := c::(l-[1]) in
   Newton_poly "(radius)" p 0.

 Definition find_radius_newton' (c: FF) (l: list FF): E FF :=
   (* l is a polynomial with positive coefficients; d is positive; thus p is convex *)
   let p := c::(l-[1]) in
   let p' := derive p in
   (* mimimal point of p *)
   elet m := Newton_poly "(radius, min)" p' 0 in
   if Fle 0 (taylor.eval' p m) then err "no root for the radius" else
   (* first root of p *)
   elet r := Newton "(radius)" (taylor.eval' p) (taylor.eval' p') 0 in
   (* move slightly to the right of r to help validation *)
   ret (divZ 100 (mulZ 99 r + m)).

 Definition find_radius := find_radius_newton'. (* vs _alamano *)
 
 (** putting everything together, we obtain the following function for computing solutions of polynomial functional equations.
     - [d] is the interpolation degree
     - [t] is the trucnation degree
     - [phi0] is a temptative solution (from which Newton iterations start with)
     NOTE: here we inline the relevant part of [mpolynom_eq_aux]: this makes it possible to avoid duplicate computations (see correctness proof below)
  *)
 Definition mpolynom_eq d t (F: list Tube) (phi0: list FF): E Tube :=
   let F' := map mcf F in
   let phi' := polynom_eq_oracle d F' phi0 in
   (* partial application of [beval] enables precomputation and sharing of potential list reversals *)
   let DF := beval (eval' t (derive F') phi') in
   let A' := interpolate d (fun x => 1 / DF x) in
   let A := mfc A' in
   let phi := mfc phi' in
   elet c := mnorm (A * eval' t F phi) in
   let L := derive (polynom_eq.opnewton F A) in
   let L' := map (fun M => map I2F (pol M)) L in
   elet l := polynom_for_lambda t L' phi' in
   elet r' := find_radius (I2F c) l in
   let r := F2I r' in
   if negb (is_le 0 r) then err "mpolynom_eq: negative radius" else
   let phir := {| pol := pol phi; rem := sym r; cont := false |} in
   elet lambda := mnorm (eval' t L phir) in
   let _ := print "validated lambda"%string in
   let _ := print lambda in
   if is_lt lambda 1 then
     if is_le (c + lambda * r) r then
       let eps := c / (1 - lambda) in ret {| pol := pol phi; rem := sym eps; cont := false |}
     else err "mpolynom_eq : missed (d+lambda*r)<=r"
   else err "mpolynom_eq : missed lambda<1".
 
 (** testing nullability, [d] is the interpolation degree used for conditionning the problem *)
 Definition mne0 d (M: Tube): bool :=
   (* partial application of [beval] enables precomputation and sharing of potential list reversals *)
   let p := beval (mcf M) in
   let q := interpolate d (fun x => 1 / p x) in
   is_ne 0 (mrange (M * mfc q)).
 
 (** testing positivity, [d] is the interpolation degree used for conditionning the problem  *)
 Definition mgt0 d (M: Tube): E bool :=
   if ~~ cont M then err "mgt0: need a continuous model" else
     (* TOTHINK: in orthogonal bases, sufficient to look at the constant coefficient rather than evaluating at some point (here [lo]) *)
   if ~~ is_lt 0 (meval_unsafe M lo) then ret false
   else ret (mne0 d M).
 
 (** ** correctness of the above operations *)

 Context {B: Basis BO}.
 
 Notation eval := (vectorspace.eval TT).
 
 (** membership relation for models *)
 Global Instance mmem: inRel (R->R) Tube :=
   fun f M =>
   (cont M ~> forall x, dom x -> continuity_pt f x)
   /\
   exists p, p ∈ pol M /\ forall x, dom x -> f x - eval p x ∈ rem M.

 Lemma mcont M: cont M ~> forall f, f ∈ M -> forall x, dom x -> continuity_pt f x.
 Proof. apply implE. move=>cM f [C _]. rewrite implE in C. auto. Qed. 

 (** extensionality of [mmem] *)
 (* TOTHINK: is there a way to assume only pointwise equality on the domain in this lemma? *)
 Lemma mmem_ext M f g : (forall x, (* dom x -> *) f x = g x) -> f ∈ M -> g ∈ M.
 Proof.
   move => Hfg [Cf [f0 [Hf0 Hf]]]. split.
   - case: Cf=>[Cf|]; constructor=>x Dx. 
     eapply continuity_pt_ext_loc. 2: apply Cf. 2: apply Dx.
     by exists posreal_one.     (* works because HFg is not constrained to the domain *)
   - exists f0; split => // x Hx.
     rewrite -Hfg; auto.
 Qed.
 
 (** *** basic operations *)
 
 Lemma meval_unsafeE f M: f ∈ M -> forall x X, x ∈ X -> dom x -> f x ∈ meval_unsafe M X.
 Proof.
   intros [_ (p&Hp&H)] x X xX Hx. rewrite /meval.
   replace (f x) with (eval p x + (f x - eval p x)) by (simpl; ring).
   apply addR; auto. rewrite -evalE. rel. 
 Qed.

 Lemma mevalR f M: f ∈ M -> forall x X, x ∈ X -> f x ∈ meval M X.
 Proof.
   intros fM x X xX. rewrite /meval.
   case DomE=>//H/=. apply meval_unsafeE; auto.
 Qed.
   
 Lemma domE x: dom x -> x ∈ interval lo hi.
 Proof. apply intervalE; rel. Qed.

 Lemma eval_srange p P x: p ∈ P -> dom x -> eval p x ∈ srange P.
 Proof.
   rewrite /srange => Pp Hx. 
   generalize brangeR. generalize eval_range. unfold BI; simpl.
   case brange=>[rangeR eval_rangeR|_]; case brange=>[rangeI rrange|] =>//.
   - generalize (rrange _ _ Pp).
     generalize (eval_rangeR p _ Hx).
     destruct (rangeI P) as [A C].
     simpl (@car (@ops0 ROps1)).
     destruct (rangeR p) as [a c] =>/=.
     intros E [Aa Cc]. eapply intervalE; eauto.
   - move=>_. rewrite -evalE. apply bevalR=>//. by apply domE. 
 Qed.

 Lemma mrangeE f M : f ∈ M -> forall x, dom x -> f x ∈ mrange M.
 Proof.
   move => [_ [p [Hp Hf]]] x Hx.
   rewrite /mrange; replace (f x) with (eval p x + (f x - eval p x)); last by rewrite /=; ring.
   apply addR; auto. by apply eval_srange. 
 Qed.

 Lemma mnormE f M: f ∈ M ->
                   EP' (fun Y => exists y, y ∈ Y /\ forall x, dom x -> Rabs (f x) <= y) (mnorm M).
 Proof.
   rewrite /mnorm=>Mf. apply EPV.
   case magE=>//= I b Ib H.
   eexists; split. eassumption.
   intros. by apply H, mrangeE.
 Qed.
 Arguments mnormE [_]. 
 
 Lemma maddR: add ∈ madd.
 Proof.
   move=> f M [Cf [p [Hp Hf]]] g P [Cg [q [Hq Hg]]]. split.
   cbn. case:Cf=>[Cf|]; case:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_plus; auto. 
   exists (p+q); split. by apply saddR.
   move=> x Hx. replace (_-_) with ((f x - eval p x) + (g x - eval q x)).
   apply addR; auto. rewrite eval_add/=/f_bin; ring. 
 Qed.
 
 Lemma msubR: ltac:(expand (sub ∈ msub)).
 Proof.
   move=> f M [Cf [p [Hp Hf]]] g P [Cg [q [Hq Hg]]]. split.
   cbn. case:Cf=>[Cf|]; case:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_minus; auto. 
   exists (p-q); split. by apply ssubR.
   move=> x Hx. replace (_-_) with ((f x - eval p x) - (g x - eval q x)).
   apply subR; auto. rewrite eval_sub/=/f_bin; ring. 
 Qed.

 Lemma mscalR: (fun c f (x: R) => c * f x) ∈ mscal.
 Proof.
   move=> c C Hc f M [Cf [p [Hp Hf]]]. split.
   cbn. case:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (sscal c p); split. by apply sscalR.
   move=> x Hx. replace (_-_) with (c*(f x - eval p x)).
   apply mulR; auto. rewrite eval_scal/=; ring. 
 Qed.

 Lemma mmulZR z: ltac:(expand (mulZ z ∈ mmulZ z)).
 Proof.
   move=> f M [Cf [p [Hp Hf]]]. split.
   cbn. case:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (smulZ z p); split. by apply smulZR.
   move=> x Hx. replace (_-_) with (mulZ z (f x - eval p x)).
   apply mulZR; auto. rewrite eval_mulZ/=/f_unr. ring. 
 Qed.

 Lemma mdivZR z: divZ z ∈ mdivZ z.
 Proof.
   move=> f M [Cf [p [Hp Hf]]]. split.
   cbn. case:Cf=>[Cf|]; constructor=>x Dx.
   apply continuity_pt_mult; auto. now apply continuity_pt_const.
   exists (sdivZ z p); split. by apply sdivZR.
   move=> x Hx. replace (_-_) with (divZ z (f x - eval p x)).
   apply divZR; auto. rewrite eval_divZ/=/f_unr/Rdiv. ring. 
 Qed.
 
 Lemma mmulR: ltac:(expand (mul ∈ mmul)).
 Proof.
   move=> f M [Cf [p [Hp Hf]]] g P [Cg [q [Hq Hg]]]. split.
   cbn. case:Cf=>[Cf|]; case:Cg=>[Cg|]; constructor=>x Dx.
   now apply continuity_pt_mult; auto. 
   exists (p*q); split. by apply bmulR.
   move=> x Hx.
   replace (_-_) with
       (eval p x * (g x - eval q x) + eval q x * (f x - eval p x) + (f x - eval p x) * (g x - eval q x)) by (rewrite eval_mul/=/f_bin; ring).
   apply addR. apply addR.
   - apply mulR. by apply eval_srange. by apply Hg. 
   - apply mulR. by apply eval_srange. by apply Hf. 
   - rel. 
 Qed.
 
 Lemma msingleR: eval ∈ msingle.
 Proof.
   intros p P H. split. constructor=>x Dx. apply eval_cont.
   exists p. split=>// x Hx.
   replace (_-_) with R0 by (simpl; ring). 
   apply zerR.
 Qed.

 Lemma msingleR' p P f: p ∈ P -> (forall x, (* dom x -> *) eval p x = f x) -> f ∈ msingle P.
 Proof. intros pP H. apply (mmem_ext H). by apply msingleR. Qed.
 
 Lemma mzerR: 0 ∈ mzer.
 Proof. eapply msingleR'. constructor. reflexivity. Qed.
 
 Lemma moneR: 1 ∈ mone.
 Proof. eapply msingleR'. apply boneR. apply eval_one. Qed.
 
 Lemma midR: id ∈ mid.
 Proof.
   unfold mid. generalize eval_id.
   case (proj2 (ERV _ _ _) bidR)=>//=*.
   eapply msingleR'; eauto.
 Qed.
 
 Lemma mcosR: cos ∈ mcos.
 Proof.
   unfold mcos. generalize eval_cos.
   case (proj2 (ERV _ _ _) bcosR)=>//=*.
   eapply msingleR'; eauto.
 Qed.
 
 Lemma msinR: sin ∈ msin.
 Proof.
   unfold msin. generalize eval_sin.
   case (proj2 (ERV _ _ _) bsinR)=>//=*.
   eapply msingleR'; eauto.
 Qed.
 
 Lemma mnthR n: TT n ∈ mnth n.
 Proof. eapply msingleR'. apply snthR. apply eval_nth. Qed.
 
 Lemma mcstR: @f_cst R R ∈ mcst.
 Proof.
   move=>c C H. eapply mmem_ext.
   2: { apply mscalR. apply H. apply moneR. }
   cbv; move=>_. ring.
 Qed.
 
 Lemma mfullE f: f ∈ mfull.
 Proof.
   split. constructor. 
   exists 0; split. apply szerR.
   intros. apply fullE.
 Qed.

 Lemma mtruncateR n: id ∈ mtruncate n.
 Proof.
   rewrite /mtruncate=>f F [Cf [p [Hp H]]].
   generalize (split_listR n Hp).
   generalize (eval_split_list TT n p).  
   simpl. case split_list=> p1 p2.
   case split_list=> P1 P2. simpl. 
   intros E [R1 R2]. split. exact Cf. 
   exists p1. split=>//. 
   intros x Hx.  
   replace (_-_) with ((f x - eval p x) + eval p2 x) by (rewrite E; simpl; ring).
   apply addR. by apply H. by apply eval_srange.
 Qed.

 Lemma mmul'R d: ltac:(expand (mul ∈ mmul' d)).
 Proof. repeat intro. by apply mtruncateR, mmulR. Qed.

 Instance mmem_Rel0: Rel0 mmem :=
   {|
     addR := maddR;
     subR := msubR;
     mulR := mmulR;
     mul'R := mmul'R;
     zerR := mzerR;
     oneR := moneR;    
     mulZR := mmulZR;
     divZR := mdivZR;
   |}.

 Lemma mmul''R t: ltac:(expand (mul ∈ mul'' t)).
 Proof. apply: mul''R. Qed.
 
 Lemma mcontinuousE: forall f F,
     (forall x, dom x -> continuity_pt f x) -> f ∈ F -> f ∈ mcontinuous F.
 Proof.
   intros f F Cf Ff. split. constructor. exact Cf. apply Ff. 
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
 
 Lemma rmintegrate_unsafe: forall f M, 
     f ∈ M -> (forall x, dom x -> continuity_pt f x) ->
     forall a A, a ∈ A -> dom a ->
     forall d D, d ∈ D -> dom d -> RInt f a d ∈ mintegrate_unsafe M A D.
 Proof.
   move => f M [_ [p [Hp Hf]]] Hfcont a A Ha HA d D Hd HD.
   have Hfint : ex_RInt f a d by apply cont_ex_RInt. 
   have Hpint : ex_RInt (eval p) a d by apply cont_ex_RInt; last (intros; apply eval_cont).
   have Hfpint : ex_RInt (f - eval p) a d by apply @ex_RInt_minus with (V:=R_NormedModule).
   rewrite (RInt_ext _ (eval p+(f-eval p))); last by (move => x _; rewrite /=/f_bin; lra).
   rewrite RInt_plus => //; first apply addR.
   rewrite -integrateE. rel. 
   case (Req_dec a d) => ad.
   destruct ad. replace (RInt _ _ _) with (RInt (fun _ => f a - eval p a) a a).
     by rewrite RInt_const; apply mulR; rel.
     apply RInt_ext. intro. unfold Rmin, Rmax. lra.
   replace (RInt _ _ _) with ((d-a) * (RInt (f-eval p) a d / (d-a))) by (simpl; field; lra).
   apply mulR. rel.   
   clear - ad HA HD Hfpint Hf.
   wlog: a d ad HA HD Hfpint / a < d.
   destruct (total_order_T a d) as [[ad'|ad']|ad'] => H.
   - apply H=>//.
   - congruence. 
   - rewrite -opp_RInt_swap; last by apply ex_RInt_swap.
     replace (_/_) with ((RInt (f-eval p) d a / (a-d))) by (rewrite /opp/=; field; lra).
     apply H=>//. congruence. by apply ex_RInt_swap.
   move=>{ad}=>ad. 
   
   case (minE (rem M)) => [u U Uu rMu|] Hu.
   have Hu': forall x, dom x -> u <= f x - eval p x. by intros; apply Rge_le, Hu, Hf.
   have Hu'': u <= RInt (f-eval p) a d / (d-a).
     apply RInt_min=>//. intros. apply Hu'. unfold dom in * ; lra. 
   case (maxE (rem M)) => [v V Vv rMv|] Hv.
   have Hv': forall x, dom x -> f x - eval p x <= v. by intros; apply Hv, Hf.
   have Hv'': RInt (f-eval p) a d / (d-a) <= v.
     apply RInt_max=>//. intros. apply Hv'. unfold dom in * ; lra. 
   apply convex with u v =>//. 
   eapply Hv. apply rMu. apply Hu''.
   case (maxE (rem M)) => [v V Vv rMv|] Hv.
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

 Lemma mintegrateR: 
   forall f M, f ∈ M -> 
   forall a A, omem lo a A -> 
   forall d D, omem hi d D -> RInt f a d ∈ mintegrate M A D.
 Proof.
   intros f M Mf a A Aa d D Dd.
   rewrite /mintegrate.
   case:(proj1 Mf)=>[Cf|]. 2: constructor.
   destruct Aa as [Aa|]; destruct Dd as [Dd|].
   - case DomE=>//= Da. case DomE=>//= Db. 
     now apply rmintegrate_unsafe; auto.
   - case DomE=>//= Da.
     apply rmintegrate_unsafe=>//; try rel. apply domhi.
   - case DomE=>//= Db.
     apply rmintegrate_unsafe=>//; try rel. apply domlo.
   - apply rmintegrate_unsafe=>//; try rel. apply domlo. apply domhi.
 Qed.

 (** auxiliary lemma for operations involving interpolation *)
 Lemma mfcE p: eval (map F2R p) ∈ mfc p.
 Proof. apply msingleR, mapR, F2IE. Qed.
 
 (** *** division *)
 
 Lemma mdiv_auxR t H W: div ∈ mdiv_aux t H W.
 Proof.
   rewrite /mdiv_aux=>f F Hf g G Hg. 
   pose proof (Hh := mfcE H).
   set p := map F2R H in Hh. set h := eval p in Hh.
   have Hp: p ∈ map F2I H by apply mapR; rel.
   pose proof (HW := mfcE W). set (w := eval (map F2R W)) in *.
   ecase mnormE=>//=; [by eauto using msubR,moneR,mmulR|]=>Mu [mu [MU Hm]]. 
   ecase mnormE=>//=; [by eauto using msubR,moneR,mmulR,mmul''R|]=>C [c [Cc Hc]].
   case is_ltE => [Hmu|]=>//.
   specialize (Hmu _ 1 MU oneR).
   have L: forall x, dom x -> g x <> 0 /\ Rabs (h x - f x / g x) <= c / (R1 - mu).
     move=>x Dx; refine (div.newton _ _ _ _ Dx)=>//.
     + by intros; apply Hm.
     + by intros; apply Hc. 
     + split=>//. rewrite <- (Hm _ Dx). apply Rabs_pos.
     + rewrite <- (Hc _ Dx). apply Rabs_pos.
   split.
   - case:(proj1 Hf)=>[Cf|]; case:(proj1 Hg)=>[Cg|]; constructor=>x Dx.
     apply continuity_pt_div; auto. by apply L. 
   - exists p; split=>//.
     move => x Hx. rewrite /f_bin.
     apply symE with (c / (1 - mu)) => /=; last by rel. 
     rewrite Rabs_minus_sym. by apply L.
 Qed.

 Lemma mdivR d t: div ∈ mdiv d t. 
 Proof. repeat intro. by apply mdiv_auxR. Qed.

 (** *** square root *)

 Lemma msqrt_auxR d H W: sqrt ∈ msqrt_aux d H W.
 Proof.
   rewrite /msqrt_aux=>f F Hf.
   pose proof (Hh := mfcE H).
   set p := map F2R H in Hh. set h := eval p in Hh.
   have Hp: p ∈ map F2I H by apply mapR; rel.
   pose proof (Hw := mfcE W).
   pose proof (Hwcont := eval_cont (map F2R W)). set (w := eval (map F2R W)) in *.
   set (x0:=(lo+hi)//2).
   have domx0: dom ((lo+hi)/2) by generalize domlo; generalize domhi; rewrite /dom; lra. 
   have rx0: (lo+hi)/2 ∈ x0 by rel.
   case is_ltE => [Hwx0|]=>[|//=]. 
   specialize (Hwx0 _ _ zerR (meval_unsafeE Hw rx0 domx0)).
   simpl negb.
   ecase mnormE=>//=; [by eauto using msubR,moneR,mmulR,mmulZR|]=>Mu0 [mu0 [MU0 Hmu0]]. 
   ecase mnormE=>//=; [by eauto using msubR,mmulR|]=>Mu1 [mu1 [MU1 Hmu1]]. 
   ecase mnormE=>//=; [by eauto using msubR,mmulR,mmul''R|]=>BB [b [Bb Hb]]. 
   case is_ltE =>// Hmu01. specialize (Hmu01 _ _ MU0 oneR).
   case is_ltE =>// Hmu0b. 
   case is_ltE => [Hmu|] =>//.
   have L: forall x, dom x -> 0 <= f x /\ Rabs (h x - sqrt (f x)) <= sqrt.rmin b mu0 mu1.
     (unshelve eapply (sqrt.newton (w:=w) _ _ _ _ _ _ _ _ _ _ _)) =>//.
     + move => t Ht; rewrite Rmult_assoc. by apply Hmu0.
     + move => t Ht /=; rewrite Rmult_1_r. by apply Hb.
     + split=>//. rewrite <-(Hmu0 _ domx0). apply Rabs_pos. 
     + apply Rlt_le_trans with (Rabs (w ((lo+hi)/2))); eauto.
       clear -Hwx0. split_Rabs; simpl in *; lra.
     + rewrite <- (Hb _ domx0). apply Rabs_pos.
     + apply Rlt_le, Hmu0b; rel. 
     + apply Hmu; rel. 
     + unfold dom. clear. intros; simpl in *; lra. 
     + exists ((lo+hi)/2). split. apply domx0. apply Hwx0. 
   split. 
   - case:(proj1 Hf)=>[Cf|]; constructor=>x Dx.
     apply (continuity_pt_comp f). apply Cf, Dx. 
     apply continuity_pt_sqrt. by apply L. 
   - exists p; split =>// x Hx.
     set rmin := sqrt.rmin b mu0 mu1.
     eapply symE with rmin; first last. rel. 
     rewrite Rabs_minus_sym. by apply L.
 Qed.

 Lemma msqrtR d t: sqrt ∈ msqrt d t.
 Proof. repeat intro. by apply msqrt_auxR. Qed.

 (** *** solutions of polynomial functional equations *)

 Lemma mpolynom_eq_auxR t
       (F': list Tube) (phi' A': list FF) (r': FF)
       (F: list (R->R)):
   F ∈ F' ->
   0 <= F2R r' ->
   EP (fun M => exists f, f ∈ M /\ forall x, dom x ->  taylor.eval' F f x = 0) (mpolynom_eq_aux t F' phi' A' r').  
 Proof.
   move => HF Hr0. rewrite /mpolynom_eq_aux/=.
   pose proof (Hphi := mfcE phi'). 
   pose proof (HA := mfcE A'). 
   set r := F2R r'. 
   set p := map F2R phi' in Hphi. 
   set phi := eval p in Hphi.
   set A := eval (map F2R A') in HA.
   have Hp: p ∈ map F2I phi' by apply mapR; rel. 
   unfold mnorm at 1. case magE=>[lambda lambda' clambda Hlambda|]=>//=.
   ecase mnormE=>//=; [by apply mmulR; try apply taylor.eval'tR; try eassumption|]=>c' [c [cc Hc]].
   case is_ltE => [Hl1|]=>//.
   case is_leE => [Hdlr|]=>//. cbn. 
   have Hnewton : exists f, forall t, dom t ->  taylor.eval' F f t = 0 /\ Rabs ( f t - phi t ) <= c / (1 - lambda).
   apply polynom_eq.newton with A r.
   + move => s Hs y Dy.
     apply Hlambda, mrangeE => //=.
     apply taylor.eval'tR. apply taylor.deriveR. apply: ssubR.
     apply: taylor.sidR.  apply: sscalR; rel.
     split; first constructor.
     exists p; split => //. 
     move => x Dx /=.
     apply symE with r =>//. rewrite Rabs_minus_sym. apply Hs => //. rel. 
   + by intros; apply Hc.
   + split. 2 : apply Hl1 => //; rel.
     apply Rle_trans with (Rabs (taylor.eval' (derive (polynom_eq.opnewton F A)) phi hi)).
     apply Rabs_pos.   
     apply Hlambda, mrangeE.
     apply taylor.eval'tR. apply taylor.deriveR. apply: ssubR.
     apply: taylor.sidR.  apply: sscalR; rel.
     split ; first constructor.
     exists p; split => //=.
     move => x Dx /=.
     replace ( _ - _) with 0%R by (rewrite /phi/=; ring).
     apply symE with r => //. by rewrite Rabs_R0. rel. apply domhi.
   + rewrite <-(Hc _ domhi). apply Rabs_pos. 
   + by [].
   + apply Hdlr; rel. 

   move: Hnewton=>[f Hnewton].
   exists f; split. 2 : apply Hnewton.
   split; first constructor.
   exists p; split => //.
   move => x Dx /=.
   eapply symE. 2: rel.
   by apply Hnewton.
 Qed.

 (** [mpolynom_eq] essentially is an instance of [mpolynom_eq_aux] *)
 Lemma mpolynom_eq_link d t F phi0:
   EP' (fun M => exists phi A r, ret M = mpolynom_eq_aux t F phi A r /\ 0 <= F2R r)
      (mpolynom_eq d t F phi0).
 Proof.
   rewrite /mpolynom_eq. apply EPV. 
   set A' := interpolate _ _. set A := mfc _.
   set phi' := polynom_eq_oracle _ _ _. set phi := mfc _.
   set m := mnorm _. case_eq m=>//= c Hc.
   case polynom_for_lambda=>//= l'.
   case find_radius=>//= r'.
   case is_leE=>//= Hr. 
   set lambda := mnorm _. case_eq lambda=>//=l Hl.
   case_eq (is_lt l 1)=>//= Hl1.
   set r := F2I r'.
   case_eq (is_le (c+l*r) r)=>//= Hlr.
   exists phi', A', r'. split. 
   unfold mpolynom_eq_aux.
   by rewrite -/A -/phi -/m -/lambda Hc Hl /= Hl1 Hlr.
   apply Hr; rel. 
 Qed.

 (** whence its correctness *)
 Lemma mpolynom_eqR d t F' F phi0:
   F ∈ F' ->  
   EP' (fun M => exists f, f ∈ M /\ forall t, dom t ->  taylor.eval' F f t = 0)
       (mpolynom_eq d t F' phi0).
 Proof.
   move=> HF. apply EPV. case mpolynom_eq_link=>//M.
   intros (phi&A&r&->&Hr). eapply mpolynom_eq_auxR; eauto. 
 Qed.
 
 (** *** non-nullability test *)
 Lemma mne0E n M: mne0 n M ~> forall f, f ∈ M -> (forall x, dom x -> f x <> 0).
 Proof.
   rewrite /mne0 implE.
   case is_neE=>//=H _ f Hf x Hx E. 
   set M' := interpolate _ _ in H. 
   set f' := eval (map F2R M').
   have E': (f x * f' x = 0) by rewrite E/=; ring. revert E'.
   apply nesym. apply H. rel. 
   apply (mrangeE (f:=fun x => f x * f' x))=>//. apply mmulR=>//.
   apply mfcE.
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
 
 Lemma mgt0E n M: mgt0 n M ~~> forall f, f ∈ M -> (forall x, dom x -> 0 < f x).
 Proof.
   rewrite /mgt0 EimplV. case_eq (cont M)=>//=Cf. 
   case is_ltE=>//=H'. 
   case mne0E=>//= H'' _ f Hf. 
   apply continuous_gt0 with lo=>//; eauto.
   - revert Cf. case (mcont M)=>//; eauto.
   - exact domlo.
   - apply H'. rel. apply meval_unsafeE=>//. rel. exact domlo.
 Qed.

 (** packing all operations together *)
 Program Definition model: Model model_ops lo hi := {|
   interfaces.mmem := mmem;
   interfaces.midR := midR;
   interfaces.mcosR := mcosR;
   interfaces.msinR := msinR;
   interfaces.mcstR := mcstR;
   interfaces.mevalR := mevalR;
   interfaces.mintegrateR := mintegrateR;
   interfaces.mdivR := mdivR;
   interfaces.msqrtR := msqrtR;
   interfaces.mtruncateR := mtruncateR;
   interfaces.mrangeE := mrangeE;               
   interfaces.mne0E := mne0E;               
   interfaces.mgt0E := mgt0E;               
 |}.

End n.
Arguments model_ops {_} _.
Arguments model {_ _} _.

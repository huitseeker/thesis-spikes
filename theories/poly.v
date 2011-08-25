(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg binomial.

(******************************************************************************)
(* This file provides a library for univariate polynomials over ring          *)
(* structures; it also provides an extended theory for polynomials whose      *)
(* coefficients range over commutative rings and integral domains.            *)
(*                                                                            *)
(*           {poly R} == the type of polynomials with coefficients of type R, *)
(*                       represented as lists with a non zero last element    *)
(*                       (big endian representation); the coeficient type R   *)
(*                       must have a canonical ringType structure cR. In fact *)
(*                       {poly R} denotes the concrete type polynomial cR; R  *)
(*                       is just a phantom argument that lets type inference  *)
(*                       reconstruct the (hidden) ringType structure cR.      *)
(*          p : seq R == the big-endian sequence of coefficients of p, via    *)
(*                       the coercion polyseq : polynomial >-> seq.           *)
(*             Poly s == the polynomial with coefficient sequence s (ignoring *)
(*                       trailing zeroes).                                    *)
(* \poly_(i < n) E(i) == the polynomial of degree at most n - 1 whose         *)
(*                       coefficients are given by the general term E(i)      *)
(*  0, 1, - p, p + q, == the usual ring operations: {poly R} has a canonical  *)
(* p * q, p ^+ n, ...    ringType structure, which is commutative / integral  *)
(*                       when R is commutative / integral, respectively.      *)
(*      polyC c, c%:P == the constant polynomial c                            *)
(*                 'X == the (unique) variable                                *)
(*               'X^n == a power of 'X; 'X^0 is 1, 'X^1 is convertible to 'X  *)
(*               p`_i == the coefficient of 'X^i in p; this is in fact just   *)
(*                       the ring_scope notation generic seq-indexing using   *)
(*                       nth 0%R, combined with the polyseq coercion.         *)
(*            coefp i == the linear function p |-> p`_i (self-exapanding).    *)
(*             size p == 1 + the degree of p, or 0 if p = 0 (this is the      *)
(*                       generic seq function combined with polyseq).         *)
(*        lead_coef p == the coefficient of the highest monomial in p, or 0   *)
(*                       if p = 0 (hence lead_coef p = 0 iff p = 0)           *)
(*            monic p == p is monic, i.e., lead_coef p = 1 (0 is not monic)   *)
(*             p.[x]  == the evaluation of a polynomial p at a point x using  *)
(*                       the Horner scheme                                    *)
(*                   *** The multi-rule horner_lin (resp. horner_lin_comm)    *)
(*                       unwinds horner evaluation of a polynomial expression *)
(*                       (resp. in a non commutative ring, under appropriate  *)
(*                       assumptions).                                        *)
(*             p^`()  == formal derivative of p                               *)
(*             p^`(n) == formal n-derivative of p                             *)
(*            p^`N(n) == formal n-derivative of p divided by n!               *)
(*            p \Po q == polynomial composition                               *)
(*                       \sum(i < size p) p`_i *: q ^+ i                      *)
(*      comm_poly p x == x and p.[x] commute; this is a sufficient condition  *)
(*                       for evaluating (q * p).[x] as q.[x] * p.[x] when R   *)
(*                       is not commutative.                                  *)
(*      comm_coef p x == x commutes with all the coefficients of p (clearly,  *)
(*                       this implies comm_poly p x).                         *)
(*           root p x == x is a root of p, i.e., p.[x] = 0                    *)
(*    n.-unity_root x == x is an nth root of unity, i.e., a root of 'X^n - 1  *)
(* n.-primitive_root x == x is a primitive nth root of unity, i.e., n is the  *)
(*                       least positive integer m > 0 such that x ^+ m = 1.   *)
(*                   *** The submodule poly.UnityRootTheory can be used to    *)
(*                       import selectively the part of the theory of roots   *)
(*                       of unity that doesn't mention polynomials explicitly *)
(*       map_poly f p == the image of the polynomial by the function f (which *)
(*                       should be a ring morphism).                          *)
(*     comm_ringM f u == u commutes with the image of f (i.e., with all f x)  *)
(*   horner_morph f u == the function mapping p to the value of map_poly f p  *)
(*                       at u; this is a morphism from {poly R} to the image  *)
(*                       ring of f when f is a morphism and comm_ringM f u.   *)
(*     diff_roots x y == x and y are distinct roots; if R is a field, this    *)
(*                       just means x != y, but this concept is generalized   *)
(*                       to the case where R is only a ring with units (i.e., *)
(*                       a unitRingType); in which case it means that x and y *)
(*                       commute, and that the difference x - y is a unit     *)
(*                       (i.e., has a multiplicative inverse) in R.           *)
(*                       to just x != y).                                     *)
(*       uniq_roots s == s is a sequence or pairwise distinct roots, in the   *)
(*                       sense of diff_roots p above.                         *)
(*   *** We only show that these operations and properties are transferred by *)
(*       morphisms whose domain is a field (thus ensuring injectivity).       *)
(* We prove the factor_theorem, and the max_poly_roots inequality relating    *)
(* the number of distinct roots of a polynomial and its size.                 *)
(*   The some polynomial lemmas use following suffix interpretation :         *)
(*   C - constant polynomial (as in polyseqC : a%:P = nseq (a != 0) a).       *)
(*   X - the polynomial variable 'X (as in coefX : 'X`_i = (i == 1%N)).       *)
(*   Xn - power of 'X (as in monicXn : monic 'X^n).                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "{ 'poly' T }" (at level 0, format "{ 'poly'  T }").
Reserved Notation "c %:P" (at level 2, format "c %:P").
Reserved Notation "'X" (at level 0).
Reserved Notation "''X^' n" (at level 3, n at level 2, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").
Reserved Notation "a ^`N ( n )" (at level 8, format "a ^`N ( n )").
Reserved Notation "n .-unity_root" (at level 2, format "n .-unity_root").
Reserved Notation "n .-primitive_root"
  (at level 2, format "n .-primitive_root").

Local Notation simp := Monoid.simpm.

Section Polynomial.

Variable R : ringType.

(* Defines a polynomial as a sequence with <> 0 last element *)
Record polynomial := Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

Canonical polynomial_subType :=
  Eval hnf in [subType for polyseq by polynomial_rect].
Definition polynomial_eqMixin := Eval hnf in [eqMixin of polynomial by <:].
Canonical polynomial_eqType := Eval hnf in EqType polynomial polynomial_eqMixin.
Definition polynomial_choiceMixin := [choiceMixin of polynomial by <:].
Canonical polynomial_choiceType :=
  Eval hnf in ChoiceType polynomial polynomial_choiceMixin.

Lemma poly_inj : injective polyseq. Proof. exact: val_inj. Qed.

Definition poly_of of phant R := polynomial.
Identity Coercion type_poly_of : poly_of >-> polynomial.

Definition coefp_head h i (p : poly_of (Phant R)) := let: tt := h in p`_i.

End Polynomial.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with poly_of.
Bind Scope ring_scope with polynomial.
Arguments Scope polyseq [_ ring_scope].
Arguments Scope poly_inj [_ ring_scope ring_scope _].
Arguments Scope coefp_head [_ _ nat_scope ring_scope _].
Notation "{ 'poly' T }" := (poly_of (Phant T)).
Notation coefp i := (coefp_head tt i).

Section PolynomialTheory.

Variable R : ringType.
Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Canonical poly_subType := Eval hnf in [subType of {poly R}].
Canonical poly_eqType := Eval hnf in [eqType of {poly R}].
Canonical poly_choiceType := Eval hnf in [choiceType of {poly R}].

Definition lead_coef p := p`_(size p).-1.
Lemma lead_coefE p : lead_coef p = p`_(size p).-1. Proof. by []. Qed.

Definition poly_nil := @Polynomial R [::] (nonzero1r R).
Definition polyC c : {poly R} := insubd poly_nil [:: c].

Local Notation "c %:P" := (polyC c).

(* Remember the boolean (c != 0) is coerced to 1 if true and 0 if false *)
Lemma polyseqC c : c%:P = nseq (c != 0) c :> seq R.
Proof. by rewrite val_insubd /=; case: (c == 0). Qed.

Lemma size_polyC c : size c%:P = (c != 0).
Proof. by rewrite polyseqC size_nseq. Qed.

Lemma coefC c i : c%:P`_i = if i == 0%N then c else 0.
Proof. by rewrite polyseqC; case: i => [|[]]; case: eqP. Qed.

Lemma polyCK : cancel polyC (coefp 0).
Proof. by move=> c; rewrite [coefp 0 _]coefC. Qed.

Lemma polyC_inj : injective polyC.
Proof. by move=> c1 c2 eqc12; have:= coefC c2 0; rewrite -eqc12 coefC. Qed.

Lemma lead_coefC c : lead_coef c%:P = c.
Proof. by rewrite /lead_coef polyseqC; case: eqP. Qed.

(* Extensional interpretation (poly <=> nat -> R) *)
Lemma polyP p q : nth 0 p =1 nth 0 q <-> p = q.
Proof.
split=> [eq_pq | -> //]; apply: poly_inj.
without loss lt_pq: p q eq_pq / size p < size q.
  move=> IH; case: (ltngtP (size p) (size q)); try by move/IH->.
  move/(@eq_from_nth _ 0); exact.
case: q => q nz_q /= in lt_pq eq_pq *; case/eqP: nz_q.
by rewrite (last_nth 0) -(subnKC lt_pq) /= -eq_pq nth_default ?leq_addr.
Qed.

Lemma size1_polyC p : size p <= 1 -> p = (p`_0)%:P.
Proof.
move=> le_p_1; apply/polyP=> i; rewrite coefC.
by case: i => // i; rewrite nth_default // (leq_trans le_p_1).
Qed.

(* Builds a polynomial by extension. *)
Definition poly_cons c p : {poly R} :=
  if p is Polynomial ((_ :: _) as s) ns then
    @Polynomial R (c :: s) ns
  else c%:P.

Lemma polyseq_cons c p :
  poly_cons c p = (if ~~ nilp p then c :: p else c%:P) :> seq R.
Proof. by case: p => [[]]. Qed.

Lemma size_poly_cons c p :
  size (poly_cons c p) = (if nilp p && (c == 0) then 0%N else (size p).+1).
Proof. by case: p => [[|c' s] _] //=; rewrite size_polyC; case: eqP. Qed.

Lemma coef_cons c p i : (poly_cons c p)`_i = if i == 0%N then c else p`_i.-1.
Proof.
by case: p i => [[|c' s] _] [] //=; rewrite polyseqC; case: eqP => //= _ [].
Qed.

(* Build a polynomial directly from a list of coefficients. *)
Definition Poly := foldr poly_cons 0%:P.

Lemma PolyK c s : last c s != 0 -> Poly s = s :> seq R.
Proof.
case: s => {c}/= [_ |c s]; first by rewrite polyseqC eqxx.
elim: s c => /= [|a s IHs] c nz_c; rewrite polyseq_cons ?{}IHs //.
by rewrite !polyseqC !eqxx nz_c.
Qed.

Lemma polyseqK p : Poly p = p.
Proof. by apply: poly_inj; exact: PolyK (valP p). Qed.

Lemma size_Poly s : size (Poly s) <= size s.
Proof.
elim: s => [|c s IHs] /=; first by rewrite polyseqC eqxx.
by rewrite polyseq_cons; case: ifP => // _; rewrite size_polyC; case: (~~ _).
Qed.

Lemma coef_Poly s i : (Poly s)`_i = s`_i.
Proof.
by elim: s i => [|c s IHs] /= [|i]; rewrite !(coefC, eqxx, coef_cons) /=.
Qed.

(* Build a polynomial from an infinite sequence of coefficients and a bound. *)
Definition poly := locked (fun n E => Poly (mkseq E n)).

Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Lemma polyseq_poly n E :
  E n.-1 != 0 -> \poly_(i < n) E i = mkseq [eta E] n :> seq R.
Proof.
unlock poly; case: n => [|n] nzEn; first by rewrite polyseqC eqxx.
by rewrite (@PolyK 0) // -nth_last nth_mkseq size_mkseq.
Qed.

Lemma size_poly n E : size (\poly_(i < n) E i) <= n.
Proof. by unlock poly; rewrite (leq_trans (size_Poly _)) ?size_mkseq. Qed.

Lemma size_poly_eq n E : E n.-1 != 0 -> size (\poly_(i < n) E i) = n.
Proof. by move/polyseq_poly->; exact: size_mkseq. Qed.

Lemma coef_poly n E k : (\poly_(i < n) E i)`_k = (if k < n then E k else 0).
Proof.
unlock poly; rewrite coef_Poly.
have [lt_kn | le_nk] := ltnP k n; first by rewrite nth_mkseq.
by rewrite nth_default // size_mkseq.
Qed.

Lemma lead_coef_poly n E :
  n > 0 -> E n.-1 != 0 -> lead_coef (\poly_(i < n) E i) = E n.-1.
Proof.
by case: n => // n _ nzE; rewrite /lead_coef size_poly_eq // coef_poly leqnn.
Qed.

Lemma coefK p : \poly_(i < size p) p`_i = p.
Proof.
by apply/polyP=> i; rewrite coef_poly; case: ltnP => // /(nth_default 0)->.
Qed.

(* Zmodule structure for polynomial *)
Definition add_poly p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).

Definition opp_poly p := \poly_(i < size p) - p`_i.

Fact coef_add_poly p q i : (add_poly p q)`_i = p`_i + q`_i.
Proof.
rewrite coef_poly; case: leqP => //; rewrite leq_maxl => /andP[le_p_i le_q_i].
by rewrite !nth_default ?add0r.
Qed.

Fact coef_opp_poly p i : (opp_poly p)`_i = - p`_i.
Proof.
by rewrite coef_poly /=; case: leqP => // le_p_i; rewrite nth_default ?oppr0.
Qed.

Fact add_polyA : associative add_poly.
Proof. by move=> p q r; apply/polyP=> i; rewrite !coef_add_poly addrA. Qed.

Fact add_polyC : commutative add_poly.
Proof. by move=> p q; apply/polyP=> i; rewrite !coef_add_poly addrC. Qed.

Fact add_poly0 : left_id 0%:P add_poly.
Proof.
by move=> p; apply/polyP=> i; rewrite coef_add_poly coefC if_same add0r.
Qed.

Fact add_poly_opp : left_inverse 0%:P opp_poly add_poly.
Proof.
move=> p; apply/polyP=> i.
by rewrite coef_add_poly coef_opp_poly coefC if_same addNr.
Qed.

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_poly_opp.

Canonical poly_zmodType := Eval hnf in ZmodType {poly R} poly_zmodMixin.
Canonical polynomial_zmodType :=
  Eval hnf in ZmodType (polynomial R) poly_zmodMixin.

(* Properties of the zero polynomial *)
Lemma polyC0 : 0%:P = 0 :> {poly R}. Proof. by []. Qed.

Lemma polyseq0 : (0 : {poly R}) = [::] :> seq R.
Proof. by rewrite polyseqC eqxx. Qed.

Lemma size_poly0 : size (0 : {poly R}) = 0%N.
Proof. by rewrite polyseq0. Qed.

Lemma coef0 i : (0 : {poly R})`_i = 0.
Proof. by rewrite coefC if_same. Qed.

Lemma lead_coef0 : lead_coef 0 = 0 :> R. Proof. exact: lead_coefC. Qed.

Lemma size_poly_eq0 p : (size p == 0%N) = (p == 0).
Proof. by rewrite size_eq0 -polyseq0. Qed.

Lemma nil_poly p : nilp p = (p == 0).
Proof. exact: size_poly_eq0. Qed.

Lemma poly0Vpos p : {p = 0} + {size p > 0}.
Proof. by rewrite lt0n size_poly_eq0; exact: eqVneq. Qed.

Lemma polySpred p : p != 0 -> size p = (size p).-1.+1.
Proof. by rewrite -size_poly_eq0 -lt0n => /prednK. Qed.

Lemma lead_coef_eq0 p : (lead_coef p == 0) = (p == 0).
Proof.
rewrite -nil_poly /lead_coef nth_last.
by case: p => [[|x s] /= /negbTE // _]; rewrite eqxx.
Qed.

Lemma polyC_eq0 (c : R) : (c%:P == 0) = (c == 0).
Proof. by rewrite -nil_poly polyseqC; case: (c == 0). Qed.

Lemma size1P p : reflect (exists2 c, c != 0 & p = c%:P) (size p == 1%N).
Proof.
apply: (iffP eqP) => [pC | [c nz_c ->]]; last by rewrite size_polyC nz_c.
have def_p: p = (p`_0)%:P by rewrite -size1_polyC ?pC.
by exists p`_0; rewrite // -polyC_eq0 -def_p -size_poly_eq0 pC.
Qed.

(* Size, leading coef, morphism properties of coef *)
Lemma leq_size_coef p i : (forall j, i <= j -> p`_j = 0) -> size p <= i.
Proof.
move=> p_i_0; case: leqP => lt_i_p //; have p1_1 := ltn_predK lt_i_p.
have: p != 0 by rewrite -size_poly_eq0 -p1_1.
by rewrite -lead_coef_eq0 lead_coefE p_i_0 ?eqxx // -ltnS p1_1.
Qed.

Lemma leq_coef_size p i : p`_i != 0 -> i < size p.
Proof. by rewrite ltnNge; apply: contra => /(nth_default 0)->. Qed.

Lemma coefD p q i : (p + q)`_i = p`_i + q`_i.
Proof. exact: coef_add_poly. Qed.

Lemma coefN p i : (- p)`_i = - p`_i.
Proof. exact: coef_opp_poly. Qed.

Lemma coef_sub p q i : (p - q)`_i = p`_i - q`_i.
Proof. by rewrite coefD coefN. Qed.

Canonical coefp_additive i :=
  Additive ((fun p => (coef_sub p)^~ i) : additive (coefp i)).

Lemma coefMn p n i : (p *+ n)`_i = p`_i *+ n.
Proof. exact: (raddfMn (coefp_additive i)). Qed.

Lemma coefMNn p n i : (p *- n)`_i = p`_i *- n.
Proof. by rewrite coefN coefMn. Qed.

Lemma coef_sum I (r : seq I) (P : pred I) (F : I -> {poly R}) k :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. exact: (raddf_sum (coefp_additive k)). Qed.

Lemma polyC_add : {morph polyC : a b / a + b}.
Proof. by move=> a b; apply/polyP=> [[|i]]; rewrite coefD !coefC ?addr0. Qed.

Lemma polyC_opp : {morph polyC : c / - c}.
Proof. by move=> c; apply/polyP=> [[|i]]; rewrite coefN !coefC ?oppr0. Qed.

Lemma polyC_sub : {morph polyC : a b / a - b}.
Proof. by move=> a b; rewrite polyC_add polyC_opp. Qed.

Canonical polyC_additive := Additive polyC_sub.

Lemma polyC_natmul n : {morph polyC : c / c *+ n}.
Proof. exact: raddfMn. Qed.

Lemma size_opp p : size (- p) = size p.
Proof. by apply/eqP; rewrite eqn_leq -{3}(opprK p) !size_poly. Qed.

Lemma lead_coef_opp p : lead_coef (- p) = - lead_coef p.
Proof. by rewrite /lead_coef size_opp coefN. Qed.

Lemma size_add p q : size (p + q) <= maxn (size p) (size q).
Proof. exact: size_poly. Qed.

Lemma size_addl p q : size p > size q -> size (p + q) = size p.
Proof.
move=> ltqp; rewrite size_poly_eq maxnl 1?ltnW //.
by rewrite addrC nth_default ?simp ?nth_last //; case: p ltqp => [[]].
Qed.

Lemma size_sum I (r : seq I) (P : pred I) (F : I -> {poly R}) :
  size (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) size (F i).
Proof.
elim/big_rec2: _ => [|i p q _ IHp]; first by rewrite size_poly0.
by rewrite -(maxnr IHp) maxnA leq_maxr size_add.
Qed.

Lemma lead_coef_addl p q : size p > size q -> lead_coef (p + q) = lead_coef p.
Proof.
move=> ltqp; rewrite /lead_coef coefD size_addl //.
by rewrite addrC nth_default ?simp // -ltnS (ltn_predK ltqp).
Qed.

(* Polynomial ring structure. *)

Definition mul_poly (p q : {poly R}) :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).

Fact coef_mul_poly p q i :
  (mul_poly p q)`_i = \sum_(j < i.+1) p`_j * q`_(i - j)%N.
Proof.
rewrite coef_poly -subn1 -ltn_add_sub add1n; case: leqP => // le_pq_i1.
rewrite big1 // => j _; have [lq_q_ij | gt_q_ij] := leqP (size q) (i - j).
  by rewrite [q`__]nth_default ?mulr0.
rewrite nth_default ?mul0r // -(leq_add2r (size q)) (leq_trans le_pq_i1) //.
by rewrite -leq_sub_add ltn_subS.
Qed.

Fact coef_mul_poly_rev p q i :
  (mul_poly p q)`_i = \sum_(j < i.+1) p`_(i - j)%N * q`_j.
Proof.
rewrite coef_mul_poly (reindex_inj rev_ord_inj) /=.
by apply: eq_bigr => j _; rewrite (sub_ordK j).
Qed.

Fact mul_polyA : associative mul_poly.
Proof.
move=> p q r; apply/polyP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
pose coef3 j k := p`_j * (q`_(i - j - k)%N * r`_k).
transitivity (\sum_(j < i.+1) \sum_(k < i.+1 | k <= i - j) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coef_mul_poly_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep predT) //=; apply: eq_bigr => k _.
transitivity (\sum_(j < i.+1 | j <= i - k) coef3 j k).
  apply: eq_bigl => j; rewrite -ltnS -(ltnS j) -!leq_subS ?leq_ord //.
  by rewrite -subn_gt0 -(subn_gt0 j) !subn_sub addnC.
rewrite (big_ord_narrow_leq (leq_subr _ _)) coef_mul_poly big_distrl /=.
by apply: eq_bigr => j _; rewrite /coef3 !subn_sub addnC mulrA.
Qed.

Fact mul_1poly : left_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Fact mul_poly1 : right_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Fact mul_poly_addl : left_distributive mul_poly +%R.
Proof.
move=> p q r; apply/polyP=> i; rewrite coefD !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coefD mulr_addl.
Qed.

Fact mul_poly_addr : right_distributive mul_poly +%R.
Proof.
move=> p q r; apply/polyP=> i; rewrite coefD !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coefD mulr_addr.
Qed.

Fact nonzero_poly1 : 1%:P != 0 :> {poly R}.
Proof. by rewrite polyC_eq0 nonzero1r. Qed.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_poly_addl mul_poly_addr
            nonzero_poly1.

Canonical poly_ringType := Eval hnf in RingType {poly R} poly_ringMixin.
Canonical polynomial_ringType :=
  Eval hnf in RingType (polynomial R) poly_ringMixin.

Lemma polyC1 : 1%:P = 1 :> {poly R}. Proof. by []. Qed.

Lemma polyseq1 : (1 : {poly R}) = [:: 1] :> seq R.
Proof. by rewrite polyseqC nonzero1r. Qed.

Lemma size_poly1 : size (1 : {poly R}) = 1%N.
Proof. by rewrite polyseq1. Qed.

Lemma coef1 i : (1 : {poly R})`_i = (i == 0%N)%:R.
Proof. by case: i => [|i]; rewrite polyseq1 /= ?nth_nil. Qed.

Lemma lead_coef1 : lead_coef 1 = 1 :> R. Proof. exact: lead_coefC. Qed.

Lemma coefM p q i : (p * q)`_i = \sum_(j < i.+1) p`_j * q`_(i - j)%N.
Proof. exact: coef_mul_poly. Qed.

Lemma coefMr p q i : (p * q)`_i = \sum_(j < i.+1) p`_(i - j)%N * q`_j.
Proof. exact: coef_mul_poly_rev. Qed.

Lemma size_mul p q : size (p * q) <= (size p + size q).-1.
Proof. exact: size_poly. Qed.

Lemma mul_lead_coef p q :
  lead_coef p * lead_coef q = (p * q)`_(size p + size q).-2.
Proof.
pose dp := (size p).-1; pose dq := (size q).-1.
have [-> | nz_p] := eqVneq p 0; first by rewrite lead_coef0 !mul0r coef0.
have [-> | nz_q] := eqVneq q 0; first by rewrite lead_coef0 !mulr0 coef0.
have ->: (size p + size q).-2 = (dp + dq)%N.
  by do 2! rewrite polySpred // addSn addnC.
have lt_p_pq: dp < (dp + dq).+1 by rewrite ltnS leq_addr.
rewrite coefM (bigD1 (Ordinal lt_p_pq)) ?big1 ?simp ?addKn //= => i.
rewrite -val_eqE neq_ltn /= => /orP[lt_i_p | gt_i_p]; last first.
  by rewrite nth_default ?mul0r //; rewrite -polySpred in gt_i_p.
rewrite [q`__]nth_default ?mulr0 //= -subSS -{1}addnS -polySpred //.
by rewrite addnC -addn_subA ?leq_addr.
Qed.

Lemma size_proper_mul p q :
  lead_coef p * lead_coef q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
apply: contraNeq; rewrite mul_lead_coef eqn_leq size_mul -ltnNge => lt_pq.
by rewrite nth_default // -subn1 -(leq_add2l 1) -leq_sub_add leq_sub2r.
Qed.

Lemma lead_coef_proper_mul p q :
  let c := lead_coef p * lead_coef q in c != 0 -> lead_coef (p * q) = c.
Proof. by move=> /= nz_c; rewrite mul_lead_coef -size_proper_mul. Qed.

Lemma size_prod (I : finType) (P : pred I) (F : I -> {poly R}) :
  size (\prod_(i | P i) F i) <= (\sum_(i | P i) size (F i)).+1 - #|P|.
Proof.
rewrite -sum1_card.
elim/big_rec3: _ => [|i n m p _ IHp]; first by rewrite size_poly1.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 size_poly0.
rewrite (leq_trans (size_mul _ _)) // -predn_sub -!subn1 leq_sub2r // -addnS.
rewrite -addn_subA ?leq_add2l // ltnW // -subn_gt0 (leq_trans _ IHp) //.
by rewrite polySpred.
Qed.

Lemma coefCM c p i : (c%:P * p)`_i = c * p`_i.
Proof.
rewrite coefM big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma coefMC c p i : (p * c%:P)`_i = p`_i * c.
Proof.
rewrite coefMr big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma polyC_mul : {morph polyC : a b / a * b}.
Proof. by move=> a b; apply/polyP=> [[|i]]; rewrite coefCM !coefC ?simp. Qed.

Fact polyC_multiplicative : multiplicative polyC.
Proof. by split; first exact: polyC_mul. Qed.
Canonical polyC_rmorphism := AddRMorphism polyC_multiplicative.

Lemma polyC_exp n : {morph polyC : c / c ^+ n}.
Proof. exact: rmorphX. Qed.

Lemma size_exp p n : size (p ^+ n) <= ((size p).-1 * n).+1.
Proof.
elim: n => [|n IHn]; first by rewrite size_poly1.
have [-> | nzp] := poly0Vpos p; first by rewrite exprS mul0r size_poly0.
rewrite exprS (leq_trans (size_mul _ _)) //.
by rewrite -{1}(prednK nzp) mulnS -addnS leq_add2l.
Qed.

Lemma size_sign_mul p n : size ((-1) ^+ n * p) = size p.
Proof.
by rewrite -signr_odd; case: (odd n); rewrite ?mul1r // mulN1r size_opp.
Qed.

Fact coefp0_multiplicative : multiplicative (coefp 0 : {poly R} -> R).
Proof.
split=> [p q|]; last by rewrite polyCK.
by rewrite [coefp 0 _]coefM big_ord_recl big_ord0 addr0.
Qed.

Canonical coefp0_rmorphism := AddRMorphism coefp0_multiplicative.

(* Algebra structure of polynomials. *)
Definition scale_poly a (p : {poly R}) := \poly_(i < size p) (a * p`_i).

Fact scale_polyE a p : scale_poly a p = a%:P * p.
Proof.
apply/polyP=> n; rewrite coef_poly coefCM.
by case: leqP => // le_p_n; rewrite nth_default ?mulr0.
Qed.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
Proof. by rewrite !scale_polyE mulrA polyC_mul. Qed.

Fact scale_1poly : left_id 1 scale_poly.
Proof. by move=> p; rewrite scale_polyE mul1r. Qed.

Fact scale_poly_addr a : {morph scale_poly a : p q / p + q}.
Proof. by move=> p q; rewrite !scale_polyE mulr_addr. Qed.

Fact scale_poly_addl p : {morph scale_poly^~ p : a b / a + b}.
Proof. by move=> a b /=; rewrite !scale_polyE raddfD mulr_addl. Qed.

Fact scale_poly_mull a p q : scale_poly a (p * q) = scale_poly a p * q.
Proof. by rewrite !scale_polyE mulrA. Qed.

Definition poly_lmodMixin :=
  LmodMixin scale_polyA scale_1poly scale_poly_addr scale_poly_addl.

Canonical poly_lmodType :=
  Eval hnf in LmodType R {poly R} poly_lmodMixin.
Canonical polynomial_lmodType :=
  Eval hnf in LmodType R (polynomial R) poly_lmodMixin.
Canonical poly_lalgType :=
  Eval hnf in LalgType R {poly R} scale_poly_mull.
Canonical polynomial_lalgType :=
  Eval hnf in LalgType R (polynomial R) scale_poly_mull.

Lemma mul_polyC a p : a%:P * p = a *: p.
Proof. by rewrite -scale_polyE. Qed.

Lemma scale_poly1 a : a *: 1 = a%:P :> {poly R}.
Proof. by rewrite -mul_polyC mulr1. Qed.

Lemma coefZ a p i : (a *: p)`_i = a * p`_i.
Proof.
by rewrite coef_poly; case: leqP => // le_p_n; rewrite nth_default ?mulr0.
Qed.

Canonical coefp_linear i :=
  AddLinear ((fun a => (coefZ a) ^~ i) : scalable (coefp i : {poly R} -> R^o)).

(* The indeterminate, at last! *)
Definition polyX : {poly R} := locked Poly [:: 0; 1].

Local Notation "'X" := polyX.

Lemma polyseqX : 'X = [:: 0; 1] :> seq R.
Proof. by unlock polyX; rewrite !polyseq_cons nil_poly eqxx /= polyseq1. Qed.

Lemma size_polyX : size 'X = 2. Proof. by rewrite polyseqX. Qed.

Lemma coefX i : 'X`_i = (i == 1%N)%:R.
Proof. by case: i => [|[|i]]; rewrite polyseqX //= nth_nil. Qed.

Lemma lead_coefX : lead_coef 'X = 1.
Proof. by rewrite /lead_coef polyseqX. Qed.

Lemma commr_polyX p : GRing.comm p 'X.
Proof.
apply/polyP=> i; rewrite coefMr coefM.
by apply: eq_bigr => j _; rewrite coefX commr_nat.
Qed.

Lemma coefMX p i : (p * 'X)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof.
rewrite coefMr big_ord_recl coefX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl polyseqX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite nth_nil !simp.
Qed.

Lemma coefXM p i : ('X * p)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof. by rewrite -commr_polyX coefMX. Qed.

Lemma poly_cons_def p a : poly_cons a p = p * 'X + a%:P.
Proof.
apply/polyP=> i; rewrite coef_cons coefD coefMX coefC.
by case: ifP; rewrite !simp.
Qed.

Lemma poly_ind (K : {poly R} -> Type) :
  K 0 -> (forall p c, K p -> K (p * 'X + c%:P)) -> (forall p, K p).
Proof.
move=> K0 Kcons p; rewrite -[p]polyseqK.
elim: {p}(p : seq R) => //= p c IHp; rewrite poly_cons_def; exact: Kcons.
Qed.

Lemma seq_factor a : 'X - a%:P = [:: - a; 1] :> seq R.
Proof.
by rewrite -['X]mul1r -polyC_opp -poly_cons_def polyseq_cons polyseq1.
Qed.

Lemma size_factor a : size ('X - a%:P) = 2%N.
Proof. by rewrite seq_factor. Qed.

Lemma lead_coef_factor a : lead_coef ('X - a%:P) = 1.
Proof. by rewrite lead_coefE seq_factor. Qed.

Lemma factor_eq0 a : ('X - a%:P == 0) = false.
Proof. by rewrite -nil_poly seq_factor. Qed.

Lemma size_amulX p c :
  size (p * 'X + c%:P) = (if (p == 0) && (c == 0) then 0%N else (size p).+1).
Proof. by rewrite -poly_cons_def size_poly_cons nil_poly. Qed.

Lemma polyseq_mulX p : p != 0 -> p * 'X = 0 :: p :> seq R.
Proof.
by move=> nz_p; rewrite -[p * _]addr0 -poly_cons_def polyseq_cons nil_poly nz_p.
Qed.

Lemma lead_coef_mulX p : lead_coef (p * 'X) = lead_coef p.
Proof.
have [-> | nzp] := eqVneq p 0; first by rewrite mul0r.
by rewrite /lead_coef !nth_last polyseq_mulX.
Qed.

Local Notation "''X^' n" := ('X ^+ n).

Lemma coefXn n i : 'X^n`_i = (i == n)%:R.
Proof.
by elim: n i => [|n IHn] [|i]; rewrite ?coef1 // exprS coefXM ?IHn.
Qed.

Lemma polyseqXn n : 'X^n = rcons (nseq n 0) 1 :> seq R.
Proof.
elim: n => [|n IHn]; rewrite ?polyseq1 // exprSr.
by rewrite polyseq_mulX -?size_poly_eq0 IHn ?size_rcons.
Qed.

Lemma size_polyXn n : size 'X^n = n.+1.
Proof. by rewrite polyseqXn size_rcons size_nseq. Qed.

Lemma commr_polyXn p n : GRing.comm p 'X^n.
Proof. by apply: commr_exp; exact: commr_polyX. Qed.

Lemma lead_coefXn n : lead_coef 'X^n = 1.
Proof. by rewrite /lead_coef nth_last polyseqXn last_rcons. Qed.

Lemma polyseq_mulXn n p : p != 0 -> p * 'X^n = ncons n 0 p :> seq R.
Proof.
case: n => [|n] nz_p; first by rewrite mulr1.
elim: n => [|n IHn]; first exact: polyseq_mulX.
by rewrite exprSr mulrA polyseq_mulX -?nil_poly IHn.
Qed.

Lemma coefMXn n p i : (p * 'X^n)`_i = if i < n then 0 else p`_(i - n).
Proof.
have [-> | /polyseq_mulXn->] := eqVneq p 0; last exact: nth_ncons.
by rewrite mul0r !coef0 if_same.
Qed.

Lemma coefXnM n p i : ('X^n * p)`_i = if i < n then 0 else p`_(i - n).
Proof. by rewrite -commr_polyXn coefMXn. Qed.

(* Expansion of a polynomial as an indexed sum *)
Lemma poly_def n E : \poly_(i < n) E i = \sum_(i < n) E i *: 'X^i.
Proof.
unlock poly; elim: n => [|n IHn] in E *; first by rewrite big_ord0.
rewrite big_ord_recl /= poly_cons_def addrC expr0 scale_poly1.
congr (_ + _); rewrite (iota_addl 1 0) -map_comp IHn big_distrl /=.
by apply: eq_bigr => i _; rewrite -scaler_mull exprSr.
Qed.

(* Monic predicate *)
Definition monic p := lead_coef p == 1.

Lemma monicP p : reflect (lead_coef p = 1) (monic p).
Proof. exact: eqP. Qed.

Lemma monic1 : monic 1. Proof. by rewrite /monic lead_coef1. Qed.
Lemma monicX : monic 'X. Proof. by rewrite /monic lead_coefX. Qed.
Lemma monicXn n : monic 'X^n. Proof. by rewrite /monic lead_coefXn. Qed.

Lemma monic_neq0 p : monic p -> p != 0.
Proof. by rewrite -lead_coef_eq0 => /eqP->; exact: nonzero1r. Qed.

Lemma lead_coef_monic_mul p q : monic p -> lead_coef (p * q) = lead_coef q.
Proof.
have [-> | nz_q] := eqVneq q 0; first by rewrite mulr0.
by move/monicP=> mon_p; rewrite lead_coef_proper_mul mon_p mul1r ?lead_coef_eq0.
Qed.

Lemma lead_coef_mul_monic p q : monic q -> lead_coef (p * q) = lead_coef p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite mul0r.
by move/monicP=> mon_q; rewrite lead_coef_proper_mul mon_q mulr1 ?lead_coef_eq0.
Qed.

Lemma size_monic_mul p q :
  monic p -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move/monicP=> mon_p nz_q.
by rewrite size_proper_mul // mon_p mul1r lead_coef_eq0.
Qed.

Lemma size_mul_monic p q :
  p != 0 -> monic q -> size (p * q) = (size p + size q).-1.
Proof.
move=> nz_p /monicP mon_q.
by rewrite size_proper_mul // mon_q mulr1 lead_coef_eq0.
Qed.

Lemma monic_mull p q : monic p -> monic (p * q) = monic q.
Proof. by move=> mon_p; rewrite /monic lead_coef_monic_mul. Qed.

Lemma monic_mulr p q : monic q -> monic (p * q) = monic p.
Proof. by move=> mon_q; rewrite /monic lead_coef_mul_monic. Qed.

Lemma monic_exp p n : monic p -> monic (p ^+ n).
Proof.
by move=> mon_p; elim: n => [|n IHn]; rewrite ?monic1 // exprS monic_mull.
Qed.

(* Some facts about regular elements. *)

Lemma lreg_lead p : GRing.lreg (lead_coef p) ->  GRing.lreg p.
Proof.
move/mulrI_eq0=> reg_p; apply: mulrI0_lreg => q /eqP; apply: contraTeq => nz_q.
by rewrite -lead_coef_eq0 lead_coef_proper_mul reg_p lead_coef_eq0.
Qed.

Lemma rreg_lead p : GRing.rreg (lead_coef p) ->  GRing.rreg p.
Proof.
move/mulIr_eq0=> reg_p; apply: mulIr0_rreg => q /eqP; apply: contraTeq => nz_q.
by rewrite -lead_coef_eq0 lead_coef_proper_mul reg_p lead_coef_eq0.
Qed.

Lemma lreg_lead0 p : GRing.lreg (lead_coef p) -> p != 0.
Proof. by move/lreg_neq0; rewrite lead_coef_eq0. Qed.

Lemma rreg_lead0 p : GRing.rreg (lead_coef p) -> p != 0.
Proof. by move/rreg_neq0; rewrite lead_coef_eq0. Qed.

Lemma lreg_size c p : GRing.lreg c ->  size (c *: p) = size p.
Proof.
move=> reg_c; have [-> | nz_p] := eqVneq p 0; first by rewrite scaler0.
rewrite -mul_polyC size_proper_mul; first by rewrite size_polyC lreg_neq0.
by rewrite lead_coefC mulrI_eq0 ?lead_coef_eq0.
Qed.

Lemma lreg_scale0 c p : GRing.lreg c -> (c *: p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /lreg_size->. Qed.

Lemma rreg_size c p : GRing.rreg c ->  size (p * (c%:P)) =  size p.
Proof.
move=> reg_c; have [-> | nz_p] := eqVneq p 0; first by rewrite mul0r.
rewrite size_proper_mul; first by rewrite size_polyC rreg_neq0 ?addn1.
by rewrite lead_coefC mulIr_eq0 ?lead_coef_eq0.
Qed.

Lemma rreg_scale0 c p : GRing.rreg c -> (p * c%:P == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /rreg_size->. Qed.

Lemma rreg_div0 q r d :
    GRing.rreg (lead_coef d) -> size r < size d ->
  (q * d + r == 0) = (q == 0) && (r == 0).
Proof.
move=> reg_d lt_r_d; rewrite addrC addr_eq0.
have [-> | nz_q] := altP (q =P 0); first by rewrite mul0r oppr0.
apply: contraTF lt_r_d => /eqP->; rewrite -leqNgt size_opp.
rewrite size_proper_mul ?mulIr_eq0 ?lead_coef_eq0 //.
by rewrite (polySpred nz_q) leq_addl.
Qed.

Lemma monic_comreg p :
  monic p -> GRing.comm p (lead_coef p)%:P /\ GRing.rreg (lead_coef p).
Proof. by move/monicP->; split; [exact: commr1 | exact: rreg1]. Qed.

(* Horner evaluation of polynomials *)
Implicit Types s rs : seq R.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

Local Notation "p .[ x ]" := (horner p x) : ring_scope.

Lemma horner0 x : (0 : {poly R}).[x] = 0.
Proof. by rewrite /horner polyseq0. Qed.

Lemma hornerC c x : (c%:P).[x] = c.
Proof. by rewrite /horner polyseqC; case: eqP; rewrite /= ?simp. Qed.

Lemma hornerX x : 'X.[x] = x.
Proof. by rewrite /horner polyseqX /= !simp. Qed.

Lemma horner_pcons p c x : (poly_cons c p).[x] = p.[x] * x + c.
Proof.
rewrite /horner polyseq_cons; case: nilP => //= ->.
by rewrite !simp -/(_.[x]) hornerC.
Qed.

Lemma horner_coef0 p : p.[0] = p`_0.
Proof. by rewrite /horner; case: (p : seq R) => //= c p'; rewrite !simp. Qed.

Lemma horner_amulX p c x : (p * 'X + c%:P).[x] = p.[x] * x + c.
Proof. by rewrite -poly_cons_def horner_pcons. Qed.

Lemma horner_mulX p x : (p * 'X).[x] = p.[x] * x.
Proof. by rewrite -[p * 'X]addr0 horner_amulX addr0. Qed.

Lemma horner_Poly s x : (Poly s).[x] = horner_rec s x.
Proof. by elim: s => [|a s /= <-]; rewrite (horner0, horner_pcons). Qed.

Lemma horner_coef p x : p.[x] = \sum_(i < size p) p`_i * x ^+ i.
Proof.
rewrite /horner.
elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_ord0.
rewrite big_ord_recl simp addrC big_distrl /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite -mulrA exprSr.
Qed.

Lemma horner_coef_wide n p x :
  size p <= n -> p.[x] = \sum_(i < n) p`_i * x ^+ i.
Proof.
move=> le_p_n.
rewrite horner_coef (big_ord_widen n (fun i => p`_i * x ^+ i)) // big_mkcond.
by apply: eq_bigr => i _; case: ltnP => // le_p_i; rewrite nth_default ?simp.
Qed.

Lemma horner_poly n E x : (\poly_(i < n) E i).[x] = \sum_(i < n) E i * x ^+ i.
Proof.
rewrite (@horner_coef_wide n) ?size_poly //.
by apply: eq_bigr => i _; rewrite coef_poly ltn_ord.
Qed.

Lemma horner_opp p x : (- p).[x] = - p.[x].
Proof.
rewrite horner_poly horner_coef -sumr_opp /=.
by apply: eq_bigr => i _; rewrite mulNr.
Qed.

Lemma horner_add p q x : (p + q).[x] = p.[x] + q.[x].
Proof.
rewrite horner_poly; set m := maxn _ _.
rewrite !(@horner_coef_wide m) ?leq_maxr ?leqnn ?orbT // -big_split /=.
by apply: eq_bigr => i _; rewrite -mulr_addl.
Qed.

Lemma horner_factor a x : ('X - a%:P).[x] = x - a.
Proof. by rewrite horner_add horner_opp hornerC hornerX. Qed.

Lemma horner_sum I (r : seq I) (P : pred I) F x :
  (\sum_(i <- r | P i) F i).[x] = \sum_(i <- r | P i) (F i).[x].
Proof. by elim/big_rec2: _ => [|i _ p _ <-]; rewrite (horner0, horner_add). Qed.

Lemma horner_Cmul a p x : (a%:P * p).[x] = a * p.[x].
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(mulr0, horner0).
by rewrite mulr_addr mulrA -polyC_mul !horner_amulX IHp mulr_addr mulrA.
Qed.

Lemma horner_scaler c p x : (c *: p).[x] = c * p.[x].
Proof. by rewrite -mul_polyC horner_Cmul. Qed.

Lemma horner_mulrn n p x : (p *+ n).[x] = p.[x] *+ n.
Proof. by elim: n => [| n IHn]; rewrite ?horner0 // !mulrS horner_add IHn. Qed.

Definition comm_coef p x := forall i, p`_i * x = x * p`_i.

Definition comm_poly p x := x * p.[x] = p.[x] * x.

Lemma comm_coef_poly p x : comm_coef p x -> comm_poly p x.
Proof.
move=> cpx; rewrite /comm_poly !horner_coef big_distrl big_distrr /=.
by apply: eq_bigr => i _; rewrite /= mulrA -cpx -!mulrA commr_exp.
Qed.

Lemma comm_poly0 x : comm_poly 0 x.
Proof. by rewrite /comm_poly !horner0 !simp. Qed.

Lemma comm_poly1 x : comm_poly 1 x.
Proof. by rewrite /comm_poly !hornerC !simp. Qed.

Lemma comm_polyX x : comm_poly 'X x.
Proof. by rewrite /comm_poly !hornerX. Qed.

Lemma horner_mul_comm p q x : comm_poly q x -> (p * q).[x] = p.[x] * q.[x].
Proof.
move=> comm_qx.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(simp, horner0).
rewrite mulr_addl horner_add horner_Cmul -mulrA -commr_polyX mulrA horner_mulX.
by rewrite {}IHp -mulrA -comm_qx mulrA -mulr_addl horner_amulX.
Qed.

Lemma horner_exp_comm p x n : comm_poly p x -> (p ^+ n).[x] = p.[x] ^+ n.
Proof.
move=> comm_px; elim: n => [|n IHn]; first by rewrite hornerC.
by rewrite !exprSr -IHn horner_mul_comm.
Qed.

Lemma hornerXn x n : ('X^n).[x] = x ^+ n.
Proof. by rewrite horner_exp_comm /comm_poly hornerX. Qed.

Definition horner_lin_comm :=
  (horner_add, horner_opp, hornerX, hornerC, horner_pcons,
   simp, horner_Cmul, horner_scaler,
   (fun p x => horner_mul_comm p (comm_polyX x))).

Lemma factor0 c : ('X - c%:P).[c] = 0.
Proof. by rewrite !horner_lin_comm addrN. Qed.

Lemma monic_factor c : monic ('X - c%:P).
Proof. by rewrite /monic /lead_coef seq_factor. Qed.

Definition root p : pred R := fun x => p.[x] == 0.

Lemma mem_root p x : x \in root p = (p.[x] == 0).
Proof. by []. Qed.

Lemma rootE p x : (root p x = (p.[x] == 0)) * ((x \in root p) = (p.[x] == 0)).
Proof. by []. Qed.

Lemma rootP p x : reflect (p.[x] = 0) (root p x).
Proof. exact: eqP. Qed.

Lemma rootPt p x : reflect (p.[x] == 0) (root p x).
Proof. exact: idP. Qed.

Lemma rootPf p x : reflect ((p.[x] == 0) = false) (~~ root p x).
Proof. exact: negPf. Qed.

Lemma rootC a x : root a%:P x = (a == 0).
Proof. by rewrite rootE hornerC. Qed.

Lemma root0 x : root 0 x.
Proof. by rewrite rootC. Qed.

Lemma root1 x : ~~ root 1 x.
Proof. by rewrite rootC oner_eq0. Qed.

Lemma rootX x : root 'X x = (x == 0).
Proof. by rewrite rootE hornerX. Qed.

Lemma root_opp p x : root (- p) x = root p x.
Proof. by rewrite rootE horner_opp oppr_eq0. Qed.

Lemma root_factor a x : root ('X - a%:P) x = (x == a).
Proof. by rewrite rootE horner_factor subr_eq0. Qed.

Lemma root_addX a x : root ('X + a%:P) x = (x == - a).
Proof. by rewrite -root_factor rmorphN opprK. Qed.

Theorem factor_theorem p a : reflect (exists q, p = q * ('X - a%:P)) (root p a).
Proof.
apply: (iffP eqP) => [pa0 | [q ->]]; last first.
  by rewrite horner_mul_comm /comm_poly factor0 ?simp.
exists (\poly_(i < size p) horner_rec (drop i.+1 p) a).
apply/polyP=> i; rewrite mulr_subr coef_sub coefMX coefMC !coef_poly.
apply: canRL (addrK _) _; rewrite addrC; have [le_p_i | lt_i_p] := leqP.
  rewrite nth_default // !simp drop_oversize ?if_same //.
  exact: leq_trans (leqSpred _).
case: i => [|i] in lt_i_p *; last by rewrite ltnW // (drop_nth 0 lt_i_p).
by rewrite drop1 /= -{}pa0 /horner; case: (p : seq R) lt_i_p.
Qed.

Lemma monic_prod_factors rs : monic (\prod_(z <- rs) ('X - z%:P)).
Proof.
by elim/big_rec: _ => [|i p _ IHp]; rewrite !(monic1, monic_factor, monic_mull).
Qed.

Lemma size_prod_factors rs : size (\prod_(z <- rs) ('X - z%:P)) = (size rs).+1.
Proof.
elim: rs => [|z rs IHrs]; rewrite (big_nil, big_cons) ?size_poly1 //.
by rewrite size_monic_mul ?monic_factor -?size_poly_eq0 ?IHrs ?seq_factor.
Qed.

Lemma size_Xn_sub_1 n : n > 0 -> size ('X^n - 1 : {poly R}) = n.+1.
Proof.
by move=> n_gt0; rewrite size_addl size_polyXn // size_opp size_poly1.
Qed.

Lemma monic_Xn_sub_1 n : n > 0 -> monic ('X^n - 1 : {poly R}).
Proof.
move=> n_gt0; rewrite /monic lead_coefE size_Xn_sub_1 // coef_sub.
by rewrite coefXn coef1 eqxx eqn0Ngt n_gt0 subr0.
Qed.

Definition root_of_unity n : pred R := root ('X^n - 1).
Local Notation "n .-unity_root" := (root_of_unity n) : ring_scope.

Lemma unity_rootE n z : n.-unity_root z = (z ^+ n == 1).
Proof.
by rewrite /root_of_unity rootE horner_add horner_opp hornerXn hornerC subr_eq0.
Qed.

Lemma unity_rootP n z : reflect (z ^+ n = 1) (n.-unity_root z).
Proof. by rewrite unity_rootE; exact: eqP. Qed.

Definition primitive_root_of_unity n z :=
  (n > 0) && (forallb i : 'I_n, i.+1.-unity_root z == (i.+1 == n)).
Local Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.

Lemma prim_order_exists n z :
  n > 0 -> z ^+ n = 1 -> {m | m.-primitive_root z & (m %| n)}.
Proof.
move=> n_gt0 zn1.
have: exists m, (m > 0) && (z ^+ m == 1) by exists n; rewrite n_gt0 /= zn1.
case/ex_minnP=> m /andP[m_gt0 /eqP zm1] m_min.
exists m.
  apply/andP; split=> //; apply/forallP=> i; apply/eqP; case: i => i /=.
  rewrite leq_eqVlt unity_rootE.
  case: eqP => [-> _ | _]; first by rewrite zm1 eqxx.
  by apply: contraTF => zi1; rewrite -leqNgt m_min.
have: n %% m < m by rewrite ltn_mod.
apply: contraLR; rewrite -lt0n -leqNgt => nm_gt0; apply: m_min.
by rewrite nm_gt0 /= exprn_mod ?zn1.
Qed.

Section OnePrimitive.

Variables (n : nat) (z : R).
Hypothesis prim_z : n.-primitive_root z.

Lemma prim_order_gt0 : n > 0. Proof. by case/andP: prim_z. Qed.
Let n_gt0 := prim_order_gt0.

Lemma prim_expr_order : z ^+ n = 1.
Proof.
case/andP: prim_z => _; rewrite -(prednK n_gt0); move/forallP; move/(_ ord_max).
by rewrite unity_rootE eqxx; do 2!move/eqP.
Qed.

Lemma prim_expr_mod i : z ^+ (i %% n) = z ^+ i.
Proof. exact: exprn_mod prim_expr_order. Qed.

Lemma prim_order_dvd i : (n %| i) = (z ^+ i == 1).
Proof.
move: n_gt0; rewrite -prim_expr_mod /dvdn -(ltn_mod i).
case: {i}(i %% n)%N => [|i] lt_i; first by rewrite !eqxx.
case/andP: prim_z => _; move/forallP; move/(_ (Ordinal (ltnW lt_i))).
by move/eqP; rewrite unity_rootE eqn_leq andbC leqNgt lt_i.
Qed.

Lemma eq_prim_root_expr i j : (z ^+ i == z ^+ j) = (i == j %[mod n]).
Proof.
wlog le_ji: i j / j <= i.
  move=> IH; case: (leqP j i); last move/ltnW; move/IH=> //.
  by rewrite eq_sym (eq_sym (j %% n)%N).
rewrite -{1}(subnKC le_ji) exprn_addr -prim_expr_mod eqn_mod_dvd //.
rewrite prim_order_dvd; apply/eqP/eqP=> [|->]; last by rewrite mulr1.
move/(congr1 ( *%R (z ^+ (n - j %% n)))); rewrite mulrA -exprn_addr.
by rewrite subnK ?prim_expr_order ?mul1r // ltnW ?ltn_mod.
Qed.

End OnePrimitive.

Lemma prim_root_exp_coprime n z k :
  n.-primitive_root z -> n.-primitive_root (z ^+ k) = coprime k n.
Proof.
move=> prim_z;have n_gt0 := prim_order_gt0 prim_z.
apply/idP/idP=> [prim_zk | co_k_n].
  set d := gcdn k n; have dv_d_n: (d %| n)%N := dvdn_gcdr _ _.
  rewrite /coprime -/d -(eqn_pmul2r n_gt0) mul1n -{2}(gcdn_mull n d).
  rewrite -{2}(divnK dv_d_n) (mulnC _ d) gcdn_mul2l dvdn_gcd_idr //.
  rewrite (prim_order_dvd prim_zk) -exprn_mulr -(prim_order_dvd prim_z).
  by rewrite gcdn_divnC dvdn_mulr.
have zkn_1: z ^+ k ^+ n = 1 by rewrite exprnC (prim_expr_order prim_z) exp1rn.
have{zkn_1} [m prim_zk dv_m_n]:= prim_order_exists n_gt0 zkn_1.
suffices /eqP <-: m == n by [].
rewrite eqn_dvd dv_m_n -(@gauss n k m) 1?coprime_sym //=.
by rewrite (prim_order_dvd prim_z) exprn_mulr (prim_expr_order prim_zk).
Qed.

End PolynomialTheory.

Prenex Implicits polyC Poly lead_coef monic root horner.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
Notation "c %:P" := (polyC c) : ring_scope.
Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.
Notation "p .[ x ]" := (horner p x) : ring_scope.
Notation "n .-unity_root" := (root_of_unity n) : ring_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.

Implicit Arguments monicP [R p].
Implicit Arguments rootP [R p x].
Implicit Arguments rootPf [R p x].
Implicit Arguments rootPt [R p x].
Implicit Arguments unity_rootP [R n z].

(* Container morphism. *)
Section MapPoly.

Section Definitions.

Variables (aR rR : ringType) (f : aR -> rR).

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

(* Alternative definition; the one above is more convenient because it lets *)
(* us use the lemmas on \poly, e.g., size (map_poly p) <= size p is an      *)
(* instance of size_poly.                                                   *)
Lemma map_polyE p : map_poly p = Poly (map f p).
Proof.
unlock map_poly poly; congr Poly.
apply: (@eq_from_nth _ 0); rewrite size_mkseq ?size_map // => i lt_i_p.
by rewrite (nth_map 0) ?nth_mkseq.
Qed.

Lemma coef_map_id0_poly p i : f 0 = 0 -> (map_poly p)`_i = f p`_i.
Proof.
by move=> f0; rewrite coef_poly; case: ltnP => // le_p_i; rewrite nth_default.
Qed.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

Variables (aR rR : ringType).

Lemma eq_map_poly (f g : aR -> rR) : f =1 g -> map_poly f =1 map_poly g.
Proof. by move=> eq_fg p; rewrite !map_polyE (eq_map eq_fg). Qed.

Lemma map_poly_comp_id0 (iR : ringType) (f : aR -> rR) (g : iR -> aR) p :
  f 0 = 0 -> map_poly (f \o g) p = map_poly f (map_poly g p).
Proof.
move=> f0; apply/polyP => i; rewrite !coef_poly.
have [lt_i_p | _] := ifP; last by rewrite f0 if_same.
case: ifPn => //=; apply: contraNeq => nz_fgpi; apply: leq_coef_size.
by rewrite coef_poly lt_i_p; apply: contraNneq nz_fgpi => ->; rewrite f0.
Qed.

Section Additive.

Variables (iR : ringType) (f : {additive aR -> rR}).

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma coef_map p i : p^f`_i = f p`_i.
Proof.
by rewrite coef_poly; case: ltnP => // le_p_i; rewrite nth_default ?raddf0.
Qed.

Lemma map_poly_comp (g : iR -> aR) p :
  map_poly (f \o g) p = map_poly f (map_poly g p).
Proof. exact: map_poly_comp_id0 (raddf0 f). Qed.

Fact map_poly_is_additive : additive (map_poly f).
Proof.
by move=> p q; apply/polyP=> i; rewrite !(coef_map, coef_sub) raddf_sub.
Qed.

Canonical map_poly_additive := Additive map_poly_is_additive.

Lemma map_polyC a : (a%:P)^f = (f a)%:P.
Proof. by apply/polyP=> i; rewrite !(coef_map, coefC) -!mulrb raddfMn. Qed.

Lemma lead_coef_map_eq p :
  f (lead_coef p) != 0 -> lead_coef p^f = f (lead_coef p).
Proof.
move=> fp_nz; rewrite lead_coef_poly // lt0n size_poly_eq0.
by apply: contra fp_nz => /eqP->; rewrite lead_coef0 raddf0.
Qed.

End Additive.

Variable f : {rmorphism aR -> rR}.
Implicit Types p : {poly aR}.

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Fact map_poly_is_rmorphism : GRing.rmorphism (map_poly f).
Proof.
split; first exact: map_poly_is_additive.
split=> [p q|]; apply/polyP=> i; last first.
  by rewrite !(coef_map, coef1) /= rmorph_nat.
rewrite coef_map /= !coefM /= !rmorph_sum; apply: eq_bigr => j _.
by rewrite !coef_map rmorphM.
Qed.
Canonical map_poly_rmorphism := RMorphism map_poly_is_rmorphism.

Lemma map_polyX : ('X)^f = 'X.
Proof. by apply/polyP=> i; rewrite coef_map !coefX /= rmorph_nat. Qed.

Lemma map_polyXn n : ('X^n)^f = 'X^n.
Proof. by rewrite rmorphX /= map_polyX. Qed.

Lemma map_poly_scaler k (p : {poly aR}) : (k *: p)^f = f k *: (p^f).
Proof. by apply/polyP=> i; rewrite !(coef_map, coefZ) /= rmorphM. Qed.

Lemma horner_map p x : p^f.[f x] = f p.[x].
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(rmorph0, horner0).
rewrite horner_amulX !rmorphD !rmorphM /=.
by rewrite map_polyX map_polyC horner_amulX IHp.
Qed.

Lemma map_comm_poly p x : comm_poly p x -> comm_poly p^f (f x).
Proof. by rewrite /comm_poly horner_map -!rmorphM // => ->. Qed.

Lemma map_comm_coef p x : comm_coef p x -> comm_coef p^f (f x).
Proof. by move=> cpx i; rewrite coef_map -!rmorphM ?cpx. Qed.

Lemma root_map_poly p x : root p x -> root p^f (f x).
Proof. by move/eqP=> px0; rewrite rootE horner_map px0 rmorph0. Qed.

Lemma rmorph_unity_root n z : n.-unity_root z -> n.-unity_root (f z).
Proof.
move/root_map_poly; rewrite rootE rmorph_sub horner_add horner_opp.
by rewrite /= map_polyXn rmorph1 hornerC hornerXn subr_eq0 unity_rootE.
Qed.

Variable u : rR.
Hypothesis cfu : commr_rmorph f u.

Lemma horner_morphC a : horner_morph cfu a%:P = f a.
Proof. by rewrite /horner_morph map_polyC hornerC. Qed.

Lemma horner_morphX : horner_morph cfu 'X = u.
Proof. by rewrite /horner_morph map_polyX hornerX. Qed.

Fact horner_is_rmorphism : GRing.rmorphism (horner_morph cfu).
Proof.
split=> [p q|]; first by rewrite /horner_morph rmorph_sub horner_add horner_opp.
split=> [p q|]; last by rewrite /horner_morph rmorph1 hornerC.
rewrite /horner_morph rmorphM /= horner_mul_comm //.
by apply: comm_coef_poly => i; rewrite coef_map cfu.
Qed.
Canonical horner_additive := Additive horner_is_rmorphism.
Canonical horner_rmorphism := RMorphism horner_is_rmorphism.

End MapPoly.

(* Morphisms from the polynomial ring, and the initiality of polynomials  *)
(* with respect to these.                                                 *)
Section MorphPoly.

Variable (aR rR : ringType) (pf : {rmorphism {poly aR} -> rR}).

Lemma poly_morphX_comm : commr_rmorph (pf \o polyC) (pf 'X).
Proof. by move=> a; rewrite /GRing.comm /= -!rmorphM // commr_polyX. Qed.

Lemma poly_initial : pf =1 horner_morph poly_morphX_comm.
Proof.
apply: poly_ind => [|p a IHp]; first by rewrite !rmorph0.
by rewrite !rmorphD !rmorphM /= -{}IHp horner_morphC ?horner_morphX.
Qed.

End MorphPoly.

Section PolynomialComRing.

Variable R : comRingType.
Implicit Types p q : {poly R}.

Fact poly_mul_comm p q : p * q = q * p.
Proof.
apply/polyP=> i; rewrite coefM coefMr.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical poly_comRingType := Eval hnf in ComRingType {poly R} poly_mul_comm.
Canonical polynomial_comRingType :=
  Eval hnf in ComRingType (polynomial R) poly_mul_comm.
Canonical poly_algType := Eval hnf in CommAlgType R {poly R}.
Canonical polynomial_algType :=
  Eval hnf in [algType R of polynomial R for poly_algType].

Lemma horner_mul p q x : (p * q).[x] = p.[x] * q.[x].
Proof. by rewrite horner_mul_comm //; exact: mulrC. Qed.

Lemma horner_exp p x n : (p ^+ n).[x] = p.[x] ^+ n.
Proof. by rewrite horner_exp_comm //; exact: mulrC. Qed.

Lemma horner_prod I r (P : pred I) (F : I -> {poly R}) x :
  (\prod_(i <- r | P i) F i).[x] = \prod_(i <- r | P i) (F i).[x].
Proof. by elim/big_rec2: _ => [|i _ p _ <-]; rewrite (horner_mul, hornerC). Qed.

Definition horner_lin :=
  (horner_add, horner_opp, hornerX, hornerC, horner_pcons,
   simp, horner_Cmul, horner_scaler, horner_mul).

End PolynomialComRing.

Section PolynomialIdomain.

(* Integral domain structure on poly *)
Variable R : idomainType.
Implicit Types (a b x y : R) (p q r m : {poly R}).

Lemma size_mul_id p q : p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
by move=> nz_p nz_q; rewrite -size_proper_mul ?mulf_neq0 ?lead_coef_eq0.
Qed.

Fact poly_idomainAxiom p q : p * q = 0 -> (p == 0) || (q == 0).
Proof.
move=> pq0; apply/norP=> [[p_nz q_nz]]; move/eqP: (size_mul_id p_nz q_nz).
by rewrite eq_sym pq0 size_poly0 (polySpred p_nz) (polySpred q_nz) addnS.
Qed.

Definition poly_unit : pred {poly R} :=
  fun p => (size p == 1%N) && GRing.unit p`_0.

Definition poly_inv p := if poly_unit p then (p`_0)^-1%:P else p.

Fact poly_mulVp : {in poly_unit, left_inverse 1 poly_inv *%R}.
Proof.
move=> p Up; rewrite /poly_inv [poly_unit p]Up.
by case/andP: Up => /size1P[c [_ ->]]; rewrite coefC -polyC_mul => /mulVr->.
Qed.

Fact poly_intro_unit p q : q * p = 1 -> poly_unit p.
Proof.
move=> pq1; apply/andP; split; last first.
  apply/unitrP; exists q`_0.
  by rewrite 2!mulrC -!/(coefp 0 _) -rmorphM pq1 rmorph1.
have: size (q * p) == 1%N by rewrite pq1 size_poly1.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 size_poly0.
have [-> | nz_q] := eqVneq q 0; first by rewrite mul0r size_poly0.
rewrite size_mul_id // (polySpred nz_p) (polySpred nz_q) addnS addSn !eqSS.
by rewrite addn_eq0 => /andP[].
Qed.

Fact poly_inv_out : {in predC poly_unit, poly_inv =1 id}.
Proof. by rewrite /poly_inv => p /negbTE->. Qed.

Definition poly_comUnitMixin :=
  ComUnitRingMixin poly_mulVp poly_intro_unit poly_inv_out.

Canonical poly_unitRingType :=
  Eval hnf in UnitRingType {poly R} poly_comUnitMixin.
Canonical polynomial_unitRingType :=
  Eval hnf in [unitRingType of polynomial R for poly_unitRingType].

Canonical poly_unitAlgType := Eval hnf in [unitAlgType R of {poly R}].
Canonical polynomial_unitAlgType := Eval hnf in [unitAlgType R of polynomial R].

Canonical poly_comUnitRingType := Eval hnf in [comUnitRingType of {poly R}].
Canonical polynomial_comUnitRingType :=
  Eval hnf in [comUnitRingType of polynomial R].

Canonical poly_idomainType :=
  Eval hnf in IdomainType {poly R} poly_idomainAxiom.
Canonical polynomial_idomainType :=
  Eval hnf in [idomainType of polynomial R for poly_idomainType].

Lemma poly_unitE p : GRing.unit p = (size p == 1%N) && GRing.unit p`_0.
Proof. by []. Qed.

Lemma poly_invE p : p ^-1 = if GRing.unit p then (p`_0)^-1%:P else p.
Proof. by []. Qed.

Lemma polyCV c : c%:P^-1 = (c^-1)%:P.
Proof.
have [/rmorphV-> // | nUc] := boolP (GRing.unit c).
by rewrite !invr_out // poly_unitE coefC (negbTE nUc) andbF.
Qed.

Lemma root_mul p q x : root (p * q) x = root p x || root q x.
Proof. by rewrite !rootE horner_mul mulf_eq0. Qed.

Lemma root_scaler x a p : a != 0 -> root (a *: p) x = root p x.
Proof. by move=> nz_a; rewrite -mul_polyC root_mul rootC (negPf nz_a). Qed.

Lemma size_scaler a p : a != 0 -> size (a *: p) = size p.
Proof. by move/lregP/lreg_size->. Qed.

Lemma size_polyC_mul a p : a != 0 -> size (a%:P * p) = size p.
Proof. by rewrite mul_polyC => /size_scaler->. Qed.

Lemma lead_coef_Imul p q : lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !(mul0r, lead_coef0).
have [-> | nz_q] := eqVneq q 0; first by rewrite !(mulr0, lead_coef0).
by rewrite lead_coef_proper_mul // mulf_neq0 ?lead_coef_eq0.
Qed.

Lemma scale_poly_eq0 a p : (a *: p == 0) = (a == 0) || (p == 0).
Proof. by rewrite -mul_polyC mulf_eq0 polyC_eq0. Qed.

Lemma size_prod_id (I : finType) (P : pred I) (F : I -> {poly R}) :
    (forall i, P i -> F i != 0) ->
  size (\prod_(i | P i) F i) = ((\sum_(i | P i) size (F i)).+1 - #|P|)%N.
Proof.
move=> nzF; transitivity (\sum_(i | P i) (size (F i)).-1).+1; last first.
  apply: canRL (addKn _) _; rewrite addnS -sum1_card -big_split /=.
  by congr _.+1; apply: eq_bigr => i /nzF/polySpred.
elim/big_rec2: _ => [|i d p /nzF nzFi IHp]; first by rewrite size_poly1.
by rewrite size_mul_id // -?size_poly_eq0 IHp // addnS polySpred.
Qed.

Lemma size_exp_id p n : (size (p ^+ n)).-1 = ((size p).-1 * n)%N.
Proof.
elim: n => [|n IHn]; first by rewrite size_poly1 muln0.
have [-> | nz_p] := eqVneq p 0; first by rewrite exprS mul0r size_poly0.
rewrite exprS size_mul_id ?expf_neq0 // mulnS -{}IHn.
by rewrite polySpred // [size (p ^+ n)]polySpred ?expf_neq0 ?addnS.
Qed.

Lemma lead_coef_exp_id p n : lead_coef (p ^+ n) = lead_coef p ^+ n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 lead_coef1.
by rewrite !exprS lead_coef_Imul IHn.
Qed.

Lemma root_prod_factors rs x :
  root (\prod_(a <- rs) ('X - a%:P)) x = (x \in rs).
Proof.
elim: rs => [|a rs IHrs]; first by rewrite rootE big_nil hornerC oner_eq0.
by rewrite big_cons root_mul IHrs root_factor.
Qed.

Lemma root_exp_factors n a x : root (('X - a%:P) ^+ n.+1) x = (x == a).
Proof. by rewrite rootE horner_exp expf_eq0 [_ == 0]root_factor. Qed.

Lemma size_factor_exp n a : size (('X - a%:P) ^+ n) = n.+1.
Proof.
rewrite -[size _]prednK ?size_exp_id ?size_factor ?mul1n //.
by rewrite lt0n size_poly_eq0 expf_eq0 factor_eq0 andbF.
Qed.

End PolynomialIdomain.

Section MapFieldPoly.

Variables (F : fieldType) (R : ringType) (f : {rmorphism F -> R}).

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma size_map_poly p : size p^f = size p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite rmorph0 !size_poly0.
by rewrite size_poly_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma lead_coef_map p : lead_coef p^f = f (lead_coef p).
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !(rmorph0, lead_coef0).
by rewrite lead_coef_map_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma map_poly_eq0 p : (p^f == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_map_poly. Qed.

Lemma map_poly_inj : injective (map_poly f).
Proof.
move=> p q eqfpq; apply/eqP; rewrite -subr_eq0 -map_poly_eq0.
by rewrite rmorph_sub /= eqfpq subrr.
Qed.

Lemma map_monic p : monic p^f = monic p.
Proof. by rewrite /monic lead_coef_map -(inj_eq (fmorph_inj f)) rmorph1. Qed.

Lemma map_poly_com p x : comm_poly p^f (f x).
Proof. exact: map_comm_poly (mulrC x _). Qed.

Lemma fmorph_root p x : root p^f (f x) = root p x.
Proof. by rewrite rootE horner_map // fmorph_eq0. Qed.

Lemma fmorph_unity_root n z : n.-unity_root (f z) = n.-unity_root z.
Proof. by rewrite !unity_rootE -(inj_eq (fmorph_inj f)) rmorphX ?rmorph1. Qed.

Lemma fmorph_primitive_root n z :
  n.-primitive_root (f z) = n.-primitive_root z.
Proof.
by congr (_ && _); apply: eq_forallb => i; rewrite fmorph_unity_root.
Qed.

End MapFieldPoly.

Section MaxRoots.

Variable R : unitRingType.
Implicit Types (x y : R) (rs : seq R) (p : {poly R}).

Definition diff_roots (x y : R) := (x * y == y * x) && GRing.unit (y - x).

Fixpoint uniq_roots rs :=
  if rs is x :: rs' then all (diff_roots x) rs' && uniq_roots rs' else true.

Lemma uniq_roots_factors p rs :
    all (root p) rs -> uniq_roots rs ->
  exists q, p = q * \prod_(z <- rs) ('X - z%:P).
Proof.
elim: rs => [|z rs IHrs] /=; first by rewrite big_nil; exists p; rewrite mulr1.
case/andP=> rpz rprs /andP[drs urs]; case: IHrs => {urs rprs}// q def_p.
have [|q' def_q] := factor_theorem q z _; last first.
  by exists q'; rewrite big_cons mulrA -def_q.
rewrite {p}def_p in rpz.
elim/last_ind: rs drs rpz => [|rs t IHrs] /=; first by rewrite big_nil mulr1.
rewrite all_rcons => /andP[/andP[/eqP czt Uzt] /IHrs {IHrs}IHrs].
rewrite -cats1 big_cat big_seq1 /= mulrA rootE horner_mul_comm; last first.
  by rewrite /comm_poly horner_factor mulr_subl mulr_subr czt.
rewrite horner_factor -oppr_sub mulrN oppr_eq0 -(mul0r (t - z)).
by rewrite (inj_eq (mulIr Uzt)) => /IHrs.
Qed.

Theorem max_ring_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> nz_p _ /(@uniq_roots_factors p)[// | q def_p]; rewrite def_p in nz_p *.
have nz_q: q != 0 by apply: contraNneq nz_p => ->; rewrite mul0r.
rewrite size_mul_monic ?monic_prod_factors // (polySpred nz_q) addSn /=.
by rewrite size_prod_factors leq_addl.
Qed.

Lemma all_roots_factors p rs :
    size p = (size rs).+1 -> all (root p) rs -> uniq_roots rs ->
  p = lead_coef p *: \prod_(z <- rs) ('X - z%:P).
Proof.
move=> size_p /uniq_roots_factors def_p Urs.
case/def_p: Urs => q -> {p def_p} in size_p *.
have [q0 | nz_q] := eqVneq q 0; first by rewrite q0 mul0r size_poly0 in size_p.
have{q nz_q size_p} /size1P[c _ ->]: size q == 1%N.
  rewrite -(eqn_addr (size rs)) add1n -size_p.
  by rewrite size_mul_monic ?monic_prod_factors // size_prod_factors addnS.
by rewrite lead_coef_mul_monic ?monic_prod_factors // lead_coefC mul_polyC.
Qed.

End MaxRoots.

Section FieldRoots.

Variable F : fieldType.
Implicit Types (p : {poly F}) (rs : seq F).

Lemma uniq_rootsE rs : uniq_roots rs = uniq rs.
Proof.
elim: rs => //= r rs ->; congr (_ && _); rewrite -has_pred1 -all_predC.
by apply: eq_all => t; rewrite /diff_roots mulrC eqxx unitfE subr_eq0.
Qed.

Theorem max_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq rs -> size rs < size p.
Proof. by rewrite -uniq_rootsE; exact: max_ring_poly_roots. Qed.

Variable n : nat.

Lemma max_unity_roots rs :
  n > 0 -> all n.-unity_root rs -> uniq rs -> size rs <= n.
Proof.
move=> n_gt0 rs_n_1 Urs; have szPn := size_Xn_sub_1 F n_gt0.
by rewrite -ltnS -szPn max_poly_roots -?size_poly_eq0 ?szPn.
Qed.

Lemma mem_unity_roots rs :
    n > 0 -> all n.-unity_root rs -> uniq rs -> size rs = n ->
  n.-unity_root =i rs.
Proof.
move=> n_gt0 rs_n_1 Urs sz_rs_n x; rewrite -topredE /=.
apply/idP/idP=> xn1; last exact: (allP rs_n_1).
apply: contraFT (ltnn n) => not_rs_x.
by rewrite -{1}sz_rs_n (@max_unity_roots (x :: rs)) //= ?xn1 ?not_rs_x.
Qed.

(* Showing the existence of a primitive root requires the theory in cyclic. *)

Variable z : F.
Hypothesis prim_z : n.-primitive_root z.

Let zn := [seq z ^+ i | i <- index_iota 0 n].

Lemma prod_factors_of_unity : \prod_(0 <= i < n) ('X - (z ^+ i)%:P) = 'X^n - 1.
Proof.
transitivity (\prod_(w <- zn) ('X - w%:P)); first by rewrite big_map.
have n_gt0: n > 0 := prim_order_gt0 prim_z.
rewrite (@all_roots_factors _ ('X^n - 1) zn); first 1 last.
- by rewrite size_Xn_sub_1 // size_map size_iota subn0.
- apply/allP=> _ /mapP[i _ ->] /=; rewrite rootE !horner_lin hornerXn.
  by rewrite exprnC (prim_expr_order prim_z) exp1rn subrr.
- rewrite uniq_rootsE map_inj_in_uniq ?iota_uniq // => i j.
  rewrite !mem_index_iota => ltin ltjn /eqP.
  by rewrite (eq_prim_root_expr prim_z) !modn_small // => /eqP.
by rewrite (monicP (monic_Xn_sub_1 F n_gt0)) scale1r.
Qed.

Lemma prim_rootP x : x ^+ n = 1 -> {i : 'I_n | x = z ^+ i}.
Proof.
move=> xn1; pose logx := [pred i : 'I_n | x == z ^+ i].
case: (pickP logx) => [i /eqP-> | no_i]; first by exists i.
case: notF; suffices{no_i}: x \in zn.
  case/mapP=> i; rewrite mem_index_iota => lt_i_n def_x.
  by rewrite -(no_i (Ordinal lt_i_n)) /= -def_x.
rewrite -root_prod_factors big_map prod_factors_of_unity.
by rewrite [root _ x]unity_rootE xn1.
Qed.

End FieldRoots.

Section MapPolyRoots.

Variables (F : fieldType) (R : unitRingType) (f : {rmorphism F -> R}).

Lemma map_diff_roots x y : diff_roots (f x) (f y) = (x != y).
Proof.
rewrite /diff_roots -rmorph_sub // fmorph_unit // subr_eq0 //.
by rewrite rmorph_comm // eqxx eq_sym.
Qed.

Lemma map_uniq_roots s : uniq_roots (map f s) = uniq s.
Proof.
elim: s => //= x s ->; congr (_ && _); elim: s => //= y s ->.
by rewrite map_diff_roots -negb_or.
Qed.

End MapPolyRoots.

Section AutPolyRoot.
(* The action of automorphisms on roots of unity. *)

Variable F : fieldType.
Implicit Types u v : {rmorphism F -> F}.

Lemma aut_prim_rootP u z n :
  n.-primitive_root z -> {k | coprime k n & u z = z ^+ k}.
Proof.
move=> prim_z; have:= prim_z; rewrite -(fmorph_primitive_root u) => prim_uz.
have [[k _] /= def_uz] := prim_rootP prim_z (prim_expr_order prim_uz).
by exists k; rewrite // -(prim_root_exp_coprime _ prim_z) -def_uz.
Qed.

Lemma aut_unity_rootP u z n : n > 0 -> z ^+ n = 1 -> {k | u z = z ^+ k}.
Proof.
by move=> _ /prim_order_exists[// | m /(aut_prim_rootP u)[k]]; exists k.
Qed.

Lemma aut_unity_rootC u v z n : n > 0 -> z ^+ n = 1 -> u (v z) = v (u z).
Proof.
move=> n_gt0 /(aut_unity_rootP _ n_gt0) def_z.
have [[i def_uz] [j def_vz]] := (def_z u, def_z v).
by rewrite !(def_uz, def_vz, rmorphX) exprnC.
Qed.

End AutPolyRoot.

Section PolyCompose.

Variable R : ringType.

Implicit Types p q : {poly R}.

(* Todo : might be renamed to comp_poly, allowing to use _poly as a suffix *)
Definition poly_comp q p := (map_poly polyC p).[q].

Local Notation "p \Po q" := (poly_comp q p) (at level 50).

Lemma poly_compE p q : p \Po q = \sum_(i < size p) p`_i *: q^+i.
Proof.
by rewrite [p \Po q]horner_poly; apply: eq_bigr => i _; rewrite mul_polyC.
Qed.

Lemma poly_compC p c : p \Po c%:P = p.[c]%:P.
Proof. exact: horner_map. Qed.

Lemma poly_comp0 p : p \Po 0 = (p`_0)%:P.
Proof. by rewrite poly_compC horner_coef0. Qed.

Lemma poly_comCp c p : c%:P \Po p = c%:P.
Proof. by rewrite /(_ \Po p) map_polyC hornerC. Qed.

Fact poly_comp_is_linear p : linear (poly_comp p).
Proof.
move=> a q r.
by rewrite /poly_comp rmorphD /= map_poly_scaler !horner_lin mul_polyC.
Qed.

Canonical poly_comp_additive p := Additive (poly_comp_is_linear p).
Canonical poly_comp_linear p := Linear (poly_comp_is_linear p).

Lemma poly_com0p p : 0 \Po p = 0.
Proof. exact: raddf0. Qed.

Lemma poly_comp_addl p q r : (p + q) \Po r = (p \Po r) + (q \Po r).
Proof. exact: raddfD. Qed.

Lemma poly_comp_subl p q r : (p - q) \Po r = (p \Po r) - (q \Po r).
Proof. exact: raddf_sub. Qed.

Lemma poly_comp_scall c p q : (c *: p) \Po q = c *: (p \Po q).
Proof. exact: linearZ. Qed.

Lemma poly_compX p : p \Po 'X = p.
Proof. by rewrite -{2}/(idfun p) poly_initial. Qed.

Lemma poly_comXp p : 'X \Po p = p.
Proof. by rewrite /(_ \Po p) map_polyX hornerX. Qed.

Lemma poly_comp_translateK z : ('X + z%:P) \Po ('X - z%:P) = 'X.
Proof. by rewrite poly_comp_addl poly_comXp poly_comCp subrK. Qed.

Lemma poly_comp_amulX c p q : (p * 'X + c%:P) \Po q = (p \Po q) * q + c%:P.
Proof.
by rewrite /(_ \Po q) rmorphD rmorphM /= map_polyX map_polyC horner_amulX.
Qed.

Lemma size_poly_comp p q : size (p \Po q) <= ((size p).-1 * (size q).-1).+1.
Proof.
rewrite poly_compE (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
rewrite (leq_trans (size_poly _ _)) // (leq_trans (size_exp _ _)) // ltnS.
by rewrite mulnC leq_mul // -{2}(subnKC (valP i)) leq_addr.
Qed.

End PolyCompose.

Notation "p \Po q" := (poly_comp q p) (at level 50).

Section ComPolyCompose.

Variable R : comRingType.
Implicit Types (p q r : {poly R}) (x : R).

Fact poly_comp_multiplicative p : multiplicative (poly_comp p).
Proof.
split=> [q r|]; last by rewrite poly_comCp.
by rewrite /poly_comp rmorphM horner_mul.
Qed.

Canonical poly_comp_rmorphism p := AddRMorphism (poly_comp_multiplicative p).

Lemma poly_comp_mull p q r : (p * q) \Po r = (p \Po r) * (q \Po r).
Proof. exact: rmorphM. Qed.

Lemma horner_poly_comp p q x : (p \Po q).[x] = p.[q.[x]].
Proof.
rewrite /poly_comp (horner_coef_wide _ (size_poly _ _)).
rewrite horner_sum [p.[_]]horner_coef.
by apply: eq_bigr => i _; rewrite coef_map ?horner_lin ?horner_exp.
Qed.

Lemma root_comp p q x : root (p \Po q) x = root p (q.[x]).
Proof. by rewrite !rootE horner_poly_comp. Qed.

Lemma poly_compA p q r : (p \Po q) \Po r = p \Po (q \Po r).
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !poly_comCp.
by rewrite !poly_comp_addl !poly_comp_mull !poly_comXp IHp !poly_comCp.
Qed.

End ComPolyCompose.

Section IdomainPolyCompose.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types p q r : {poly R}.

Lemma size_poly_comp_id p q :
  (size (p \Po q)).-1 = ((size p).-1 * (size q).-1)%N.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite poly_com0p size_poly0.
have [/size1_polyC-> | nc_q] := leqP (size q) 1.
  by rewrite poly_compC !size_polyC -!sub1b !predn_sub muln0.
have nz_q: q != 0 by rewrite -size_poly_eq0 -(subnKC nc_q).
rewrite mulnC poly_compE (polySpred nz_p) /= big_ord_recr Monoid.mulmC.
rewrite size_addl size_scaler ?lead_coef_eq0 ?size_exp_id //=.
rewrite [X in _ < X]polySpred ?expf_neq0 // ltnS size_exp_id.
rewrite (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
rewrite (leq_trans (size_poly _ _)) // polySpred ?expf_neq0 // size_exp_id.
by rewrite -(subnKC nc_q) ltn_pmul2l.
Qed.

End IdomainPolyCompose.

Section Deriv.

Variable R : ringType.

Implicit Types p q : {poly R}.

Definition deriv p := \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1).

Local Notation "a ^` ()" := (deriv a).

Lemma coef_deriv p i : p^`()`_i = p`_i.+1 *+ i.+1.
Proof.
rewrite coef_poly -subn1 -ltn_add_sub; case: leqP => // /(nth_default 0) ->.
by rewrite mul0rn.
Qed.

Lemma derivC c : c%:P^`() = 0.
Proof. by apply/polyP=> i; rewrite coef_deriv coef0 coefC mul0rn. Qed.

Lemma derivX : ('X)^`() = 1.
Proof. by apply/polyP=> [[|i]]; rewrite coef_deriv coef1 coefX ?mul0rn. Qed.

Lemma derivXn n : 'X^n^`() = 'X^n.-1 *+ n.
Proof.
case: n => [|n]; first exact: derivC.
apply/polyP=> i; rewrite coef_deriv coefMn !coefXn eqSS.
by case: eqP => [-> // | _]; rewrite !mul0rn.
Qed.

Fact deriv_is_linear : linear deriv.
Proof.
move=> k p q; apply/polyP=> i.
by rewrite !(coef_deriv, coefD, coefZ) mulrn_addl mulrnAr.
Qed.

Canonical deriv_additive := Additive deriv_is_linear.
Canonical deriv_linear := Linear deriv_is_linear.

Lemma deriv0 : 0^`() = 0.
Proof. exact: linear0. Qed.

Lemma derivD : {morph deriv : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma derivN : {morph deriv : p / - p}.
Proof. exact: linearN. Qed.

Lemma deriv_sub : {morph deriv : p q / p - q}.
Proof. exact: linear_sub. Qed.

Lemma derivMn n p : (p *+ n)^`() = p^`() *+ n.
Proof. exact: linearMn. Qed.

Lemma derivMNn n p : (p *- n)^`() = p^`() *- n.
Proof. exact: linearMNn. Qed.

Lemma derivZ c p : (c *: p)^`() = c *: p^`().
Proof. exact: linearZ. Qed.

Lemma deriv_mulC c p : (c%:P * p)^`() = c%:P * p^`().
Proof. by rewrite !mul_polyC derivZ. Qed.

Lemma derivM p q : (p * q)^`() = p^`() * q + p * q^`().
Proof.
apply/polyP=> i; rewrite !(coef_deriv, coefD, coefM).
pose pq j a b :=  p`_j *+ a * (q`_(i.+1 - j) *+ b).
transitivity (\sum_(j < i.+2) (pq j j 1%N + pq j 1%N (i.+1 - j)%N)).
  rewrite -sumr_muln; apply: eq_bigr => j _.
  by rewrite /pq !mulr1n mulrnAl mulrnAr -mulrn_addr subnKC // leq_ord.
rewrite big_split /= {}/pq; congr (_ + _).
  rewrite big_ord_recl mulr0n mul0r add0r.
  by apply: eq_bigr => j _; rewrite coef_deriv.
rewrite big_ord_recr subnn mulr0n mulr0 /= addr0.
by apply: eq_bigr => j _; rewrite coef_deriv // leq_subS // leq_ord.
Qed.

Lemma deriv_amulX p c : (p * 'X + c%:P)^`() = p + p^`() * 'X.
Proof. by rewrite derivD derivC addr0 derivM derivX mulr1 addrC. Qed.

Lemma deriv_factor (a : R) : ('X - a%:P)^`() = 1.
Proof. by rewrite deriv_sub derivX derivC subr0. Qed.

(* Note : reorder derivE, *)
(*    put factor factor before deriv_sub and derivM in the end *)
Definition derivE := Eval lazy beta delta [morphism_2 morphism_1] in
  (derivZ, deriv_mulC, derivC, derivX, deriv_amulX, derivM, deriv_sub, 
   derivD, derivMn, derivN, derivXn, deriv_factor).

Definition derivn n p := iter n deriv p.

Notation "a ^` ( n )" := (derivn n a).

Lemma derivn0 p : p^`(0) = p.
Proof. by []. Qed.

Lemma derivn1 p : p^`(1) = p^`().
Proof. by []. Qed.

Lemma derivnS p n : p^`(n.+1) = p^`(n)^`().
Proof. by []. Qed.

Lemma derivSn p n : p^`(n.+1) = p^`()^`(n).
Proof. exact: iterSr. Qed.

Lemma coef_derivn n p i : p^`(n)`_i = p`_(n + i) *+ (n + i) ^_ n.
Proof.
elim: n i => [|n IHn] i; first by rewrite ffactn0 mulr1n.
by rewrite derivnS coef_deriv IHn -mulrnA ffactnSr addSnnS addKn.
Qed.

Fact derivn_is_linear n : linear (derivn n).
Proof. by elim: n => // n IHn a p q; rewrite derivnS IHn linearP. Qed.
Canonical derivn_additive n :=  Additive (derivn_is_linear n).
Canonical derivn_linear n :=  Linear (derivn_is_linear n).

Lemma derivnC c n : c%:P^`(n) = if n == 0%N then c%:P else 0.
Proof. by case: n => // n; rewrite derivSn derivC linear0. Qed.

Lemma derivnD n : {morph (derivn n) : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma derivn_sub n : {morph (derivn n) : p q / p - q}.
Proof. exact: linear_sub. Qed.

Lemma derivnMn n m p : (p *+ m)^`(n) = p^`(n) *+ m.
Proof. exact: linearMn. Qed.

Lemma derivnMNn n m p : (p *- m)^`(n) = p^`(n) *- m.
Proof. exact: linearMNn. Qed.

Lemma derivnN n : {morph (derivn n) : p / - p}.
Proof. exact: linearN. Qed.

Lemma derivnZ n : scalable (derivn n).
Proof. exact: linearZ. Qed.

Lemma derivnXn m n : 'X^m^`(n) = 'X^(m - n) *+ m ^_ n.
Proof.
apply/polyP=>i; rewrite coef_derivn coefMn !coefXn.
case: (ltnP m n) => [lt_m_n | le_m_n].
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn ffact_small.
by rewrite -{1 3}(subnKC le_m_n) eqn_addl; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Lemma derivn_amulX n p c :
  (p * 'X + c%:P)^`(n.+1) = p^`(n) *+ n.+1  + p^`(n.+1) * 'X.
Proof.
elim: n => [|n IHn]; first by rewrite derivn1 deriv_amulX.
rewrite derivnS IHn derivD derivM derivX mulr1 derivMn -!derivnS.
by rewrite addrA addrAC -mulrSr.
Qed.

Lemma derivn_poly0 p n : size p <= n -> p^`(n) = 0.
Proof.
move=> le_p_n; apply/polyP=> i; rewrite coef_derivn.
rewrite nth_default; first by rewrite mul0rn coef0.
by apply: leq_trans le_p_n _; apply leq_addr.
Qed.

Lemma lt_size_deriv (p : {poly R}) : p != 0 -> size p^`() < size p.
Proof. by move=> /polySpred->; exact: size_poly. Qed.

(* A normalising version of derivation to get the division by n! in Taylor *)

Definition nderivn n p := \poly_(i < size p - n) (p`_(n + i) *+  'C(n + i, n)).

Notation "a ^`N ( n )" := (nderivn n a).

Lemma coef_nderivn n p i : p^`N(n)`_i = p`_(n + i) *+  'C(n + i, n).
Proof.
rewrite coef_poly -ltn_add_sub; case: leqP => // le_p_ni.
by rewrite nth_default ?mul0rn.
Qed.

(* Here is the division by n! *)
Lemma nderivn_def n p : p^`(n) = p^`N(n) *+ n`!.
Proof.
apply/polyP=> i.
by rewrite coefMn coef_nderivn coef_derivn -mulrnA bin_ffact.
Qed.

Lemma nderivn0 p : p^`N(0) = p.
Proof. by rewrite -[p^`N(0)](nderivn_def 0). Qed.

Lemma nderivn1 p : p^`N(1) = p^`().
Proof. by rewrite -[p^`N(1)](nderivn_def 1). Qed.

Lemma nderivnC c n : (c%:P)^`N(n) = if n == 0%N then c%:P else 0.
Proof.
apply/polyP=> i; rewrite coef_nderivn.
by case: n => [|n]; rewrite ?bin0 // coef0 coefC mul0rn.
Qed.

Lemma nderivnXn m n : 'X^m^`N(n) = 'X^(m - n) *+ 'C(m, n).
Proof.
apply/polyP=> i; rewrite coef_nderivn coefMn !coefXn.
have [lt_m_n | le_n_m] := ltnP m n.
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn bin_small.
by rewrite -{1 3}(subnKC le_n_m) eqn_addl; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Fact nderivn_is_linear n : linear (nderivn n).
Proof.
move=> k p q; apply/polyP=> i.
by rewrite !(coef_nderivn, coefD, coefZ) mulrn_addl mulrnAr.
Qed.
Canonical nderivn_additive n := Additive(nderivn_is_linear n).
Canonical nderivn_linear n := Linear (nderivn_is_linear n).

Lemma nderivnD n : {morph (nderivn n) : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma nderivn_sub n : {morph (nderivn n) : p q / p - q}.
Proof. exact: linear_sub. Qed.

Lemma nderivnMn n m p : (p *+ m)^`N(n) = p^`N(n) *+ m.
Proof. exact: linearMn. Qed.

Lemma nderivnMNn n m p : (p *- m)^`N(n) = p^`N(n) *- m.
Proof. exact: linearMNn. Qed.

Lemma nderivnN n : {morph (nderivn n) : p / - p}.
Proof. exact: linearN. Qed.

Lemma nderivnZ n : scalable (nderivn n).
Proof. exact: linearZ. Qed.

Lemma nderivn_amulX n p c :
  (p * 'X + c%:P)^`N(n.+1) = p^`N(n) + p^`N(n.+1) * 'X.
Proof.
apply/polyP=> i; rewrite coef_nderivn !coefD !coefMX coefC.
rewrite !addSn /= !coef_nderivn addr0 binS mulrn_addr addrC; congr (_ + _).
by rewrite addSnnS; case: i; rewrite // addn0 bin_small.
Qed.

Lemma nderivn_poly0 p n : size p <= n -> p^`N(n) = 0.
Proof.
move=> le_p_n; apply/polyP=> i; rewrite coef_nderivn.
rewrite nth_default; first by rewrite mul0rn coef0.
by apply: leq_trans le_p_n _; apply leq_addr.
Qed.

Lemma nderiv_taylor p x h :
  GRing.comm x h -> p.[x + h] = \sum_(i < size p) p^`N(i).[x] * h ^+ i.
Proof.
move/commr_exp=> cxh; elim/poly_ind: p => [|p c IHp].
  by rewrite size_poly0 big_ord0 horner0.
rewrite horner_amulX size_amulX.
have [-> | nz_p] := altP (p =P 0).
  rewrite horner0 !simp; have [-> | _] := c =P 0; first by rewrite big_ord0.
  by rewrite size_poly0 big_ord_recl big_ord0 nderivn0 hornerC !simp.
rewrite big_ord_recl nderivn0 !simp horner_amulX addrAC; congr (_ + _).
rewrite mulr_addr {}IHp !big_distrl polySpred //= big_ord_recl /= mulr1 -addrA.
rewrite nderivn0  /bump /(addn 1) /=; congr (_ + _).
rewrite !big_ord_recr /= nderivn_amulX -mulrA -exprSr -polySpred // !addrA.
congr (_ + _); last by rewrite (nderivn_poly0 (leqnn _)) !simp.
rewrite addrC -big_split /=; apply: eq_bigr => i _.
by rewrite nderivn_amulX !horner_lin_comm /= mulr_addl -!mulrA -exprSr cxh.
Qed.

Lemma nderiv_taylor_wide n p x h :
    GRing.comm x h -> size p <= n ->
  p.[x + h] = \sum_(i < n) p^`N(i).[x] * h ^+ i.
Proof.
move/nderiv_taylor=> -> le_p_n.
rewrite (big_ord_widen n (fun i => p^`N(i).[x] * h ^+ i)) // big_mkcond.
apply: eq_bigr => i _; case: leqP => // /nderivn_poly0->.
by rewrite horner0 simp.
Qed.

End Deriv.

Notation "a ^` ()" := (deriv a) : ring_scope.
Notation "a ^` ( n )" := (derivn n a) : ring_scope.
Notation "a ^`N ( n )" := (nderivn n a) : ring_scope.

Section DerivComRing.

Variable R : comRingType.

Implicit Types p q : {poly R}.

Lemma deriv_poly_comp p q : (p \Po q) ^`() = (p ^`() \Po q) * q^`().
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(deriv0, poly_com0p) mul0r.
rewrite poly_comp_amulX derivD derivC derivM IHp deriv_amulX poly_comp_addl.
by rewrite poly_comp_mull poly_comXp addr0 addrC mulrAC -mulr_addl.
Qed.

Lemma deriv_exp p n : (p ^+ n)^`() = p^`() * p ^+ n.-1 *+ n.
Proof.
elim: n => [|n IHn]; first by rewrite expr0 mulr0n derivC.
by rewrite exprS derivM {}IHn (mulrC p) mulrnAl -mulrA -exprSr mulrS; case n.
Qed.

Definition derivCE := (derivE, deriv_exp).

End DerivComRing.

Section MapDeriv.

Variables (R S : ringType) (f : {rmorphism R -> S}) (n : nat) (p : {poly R}).

Lemma deriv_map : (map_poly f p)^`() = map_poly f (p^`()).
Proof. by apply/polyP => i; rewrite !(coef_map, coef_deriv) //= rmorphMn. Qed.

Lemma derivn_map : (map_poly f p)^`(n) = map_poly f (p^`(n)).
Proof. by apply/polyP => i; rewrite !(coef_map, coef_derivn) //= rmorphMn. Qed.

Lemma nderivn_map : (map_poly f p)^`N(n) = map_poly f (p^`N(n)).
Proof. by apply/polyP => i; rewrite !(coef_map, coef_nderivn) //= rmorphMn. Qed.

End MapDeriv.

Module UnityRootTheory.

Notation "n .-unity_root" := (root_of_unity n) : unity_root_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : unity_root_scope.
Open Scope unity_root_scope.

Definition unity_rootE := unity_rootE.
Definition unity_rootP := @unity_rootP.
Implicit Arguments unity_rootP [R n z].

Definition prim_order_exists := prim_order_exists.
Notation prim_order_gt0 :=  prim_order_gt0.
Notation prim_expr_order := prim_expr_order.
Definition prim_expr_mod := prim_expr_mod.
Definition prim_order_dvd := prim_order_dvd.
Definition eq_prim_root_expr := eq_prim_root_expr.

Definition rmorph_unity_root := rmorph_unity_root.
Definition fmorph_unity_root := fmorph_unity_root.
Definition fmorph_primitive_root := fmorph_primitive_root.
Definition max_unity_roots := max_unity_roots.
Definition mem_unity_roots := mem_unity_roots.
Definition prim_rootP := prim_rootP.

End UnityRootTheory.


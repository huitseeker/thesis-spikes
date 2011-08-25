(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path fintype.
Require Import div bigop.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*        prime p <=> p is a prime.                                           *)
(*       primes m == the sorted list of prime divisors of m > 1, else [::].   *)
(*        pfactor == the type of prime factors, syntax (p ^ e)%pfactor.       *)
(* prime_decomp m == the list of prime factors of m > 1, sorted by primes.    *)
(*       logn p m == the e such that (p ^ e) \in prime_decomp n, else 0.      *)
(*         pdiv n == the smallest prime divisor of n > 1, else 1.             *)
(*     max_pdiv n == the largest prime divisor of n > 1, else 1.              *)
(*     divisors m == the sorted list of divisors of m > 0, else [::].         *)
(*          phi n == the Euler totient (#|{i < n | i and n coprime}|).        *)
(*       nat_pred == the type of explicit collective nat predicates.          *)
(*                := simpl_pred nat.                                          *)
(*    -> We allow the coercion nat >-> nat_pred, interpreting p as pred1 p.   *)
(*    -> We define a predType for nat_pred, enabling the notation p \in pi.   *)
(*    -> We don't have nat_pred >-> pred, which would imply nat >-> Funclass. *)
(*           pi^' == the complement of pi : nat_pred, i.e., the nat_pred such *)
(*                   that (p \in pi^') = (p \notin pi).                       *)
(*         \pi(n) == the set of prime divisors of n, i.e., the nat_pred such  *)
(*                   that (p \in \pi(n)) = (p \in primes n).                  *)
(*         \pi(A) == the set of primes of #|A|, with A a collective predicate *)
(*                   over a finite Type.                                      *)
(*     -> The notation \pi(A) is implemented with a collapsible Coercion, so  *)
(*        the type of A must coerce to finpred_class (e.g., by coercing to    *)
(*        {set T}), not merely implement the predType interface (as seq T     *)
(*        does).                                                              *)
(*     -> The expression #|A| will only appear in \pi(A) after simplification *)
(*        collapses the coercion stack, so it is advisable to do so early on. *)
(*     pi.-nat n <=> n > 0 and all prime divisors of n are in pi.             *)
(*          n`_pi == the pi-part of n -- the largest pi.-nat divisor of n.    *)
(*               := \prod_(0 <= p < n.+1 | p \in pi) p ^ logn p n.            *)
(*     -> The nat >-> nat_pred coercion lets us write p.-nat n and n`_p.      *)
(* In addition to the lemmas relevant to these definitions, this file also    *)
(* contains the dvdn_sum lemma, so that bigop.v doesn't depend on div.v.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The complexity of any arithmetic operation with the Peano representation *)
(* is pretty dreadful, so using algorithms for "harder" problems such as    *)
(* factoring, that are geared for efficient artihmetic leads to dismal      *)
(* performance -- it takes a significant time, for instance, to compute the *)
(* divisors of just a two-digit number. On the other hand, for Peano        *)
(* integers, prime factoring (and testing) is linear-time with a small      *)
(* constant factor -- indeed, the same as converting in and out of a binary *)
(* representation. This is implemented by the code below, which is then     *)
(* used to give the "standard" definitions of prime, primes, and divisors,  *)
(* which can then be used casually in proofs with moderately-sized numeric  *)
(* values (indeed, the code here performs well for up to 6-digit numbers).  *)

(* We start with faster mod-2 functions. *)

Fixpoint edivn2 (q r : nat) {struct r} :=
  if r is r'.+2 then edivn2 q.+1 r' else (q, r).

Lemma edivn2P : forall n, edivn_spec n 2 (edivn2 0 n).
Proof.
move=> n; rewrite -[n]odd_double_half addnC -{1}[n./2]addn0 -{1}mul2n mulnC.
elim: n./2 {1 4}0 => [|r IHr] q; first by case (odd n) => //=.
rewrite addSnnS; exact: IHr.
Qed.

Fixpoint elogn2 (e q r : nat) {struct q} :=
  match q, r with
  | 0, _ | _, 0 => (e, q)
  | q'.+1, 1 => elogn2 e.+1 q' q'
  | q'.+1, r'.+2 => elogn2 e q' r'
  end.

CoInductive elogn2_spec n : nat * nat -> Type :=
  Elogn2Spec e m of n = 2 ^ e * m.*2.+1 : elogn2_spec n (e, m).

Lemma elogn2P : forall n, elogn2_spec n.+1 (elogn2 0 n n).
Proof.
move=> n; rewrite -{1}[n.+1]mul1n -[1]/(2 ^ 0) -{1}(addKn n n) addnn.
elim: n {1 4 6}n {2 3}0 (leqnn n) => [|q IHq] [|[|r]] e //=; last first.
  by move/ltnW; exact: IHq.
clear 1; rewrite subn1 -[_.-1.+1]doubleS -mul2n mulnA -expnSr.
rewrite -{1}(addKn q q) addnn; exact: IHq.
Qed.

Definition ifnz T n (x y : T) := if n is 0 then y else x.

CoInductive ifnz_spec T n (x y : T) : T -> Type :=
  | IfnzPos of n > 0 : ifnz_spec n x y x
  | IfnzZero of n = 0 : ifnz_spec n x y y.

Lemma ifnzP : forall T n (x y : T), ifnz_spec n x y (ifnz n x y).
Proof. by move=> T [|n] *; [right | left]. Qed.

(* For pretty-printing. *)
Definition NumFactor (f : nat * nat) := ([Num of f.1], f.2).

Definition pfactor p e := p ^ e.

Definition cons_pfactor (p e : nat) pd := ifnz e ((p, e) :: pd) pd.

Notation Local "p ^? e :: pd" := (cons_pfactor p e pd)
  (at level 30, e at level 30, pd at level 60) : nat_scope.

Section prime_decomp.

Import NatTrec.

Fixpoint prime_decomp_rec (m k a b c e : nat) {struct a} :=
  let p := k.*2.+1 in
  if a is a'.+1 then
    if b - (ifnz e 1 k - c) is b'.+1 then
      [rec m, k, a', b', ifnz c c.-1 (ifnz e p.-2 1), e] else
    if (b == 0) && (c == 0) then
      let b' := k + a' in [rec b'.*2.+3, k, a', b', k.-1, e.+1] else
    let bc' := ifnz e (ifnz b (k, 0) (edivn2 0 c)) (b, c) in
    p ^? e :: ifnz a' [rec m, k.+1, a'.-1, bc'.1 + a', bc'.2, 0] [:: (m, 1)]
  else if (b == 0) && (c == 0) then [:: (p, e.+2)] else p ^? e :: [:: (m, 1)]
where "[ 'rec' m , k , a , b , c , e ]" := (prime_decomp_rec m k a b c e).

Definition prime_decomp n :=
  let: (e2, m2) := elogn2 0 n.-1 n.-1 in
  if m2 < 2 then 2 ^? e2 :: 3 ^? m2 :: [::] else
  let: (a, bc) := edivn m2.-2 3 in
  let: (b, c) := edivn (2 - bc) 2 in
  2 ^? e2 :: [rec m2.*2.+1, 1, a, b, c, 0].

(* The list of divisors and the Euler function are computed directly from *)
(* the decomposition, using a merge_sort variant sort the divisor list.   *)

Definition add_divisors f divs :=
  let: (p, e) := f in
  let add1 divs' := merge leq (map (NatTrec.mul p) divs') divs in
  iter e add1 divs.

Definition add_phi_factor f m := let: (p, e) := f in p.-1 * p ^ e.-1 * m.

End prime_decomp.

Definition primes n := unzip1 (prime_decomp n).

Definition prime p := if prime_decomp p is [:: (_ , 1)] then true else false.

Definition nat_pred := simpl_pred nat.

Definition pi_unwrapped_arg := nat.
Definition pi_wrapped_arg := wrapped nat.
Coercion unwrap_pi_arg (wa : pi_wrapped_arg) : pi_unwrapped_arg := unwrap wa.
Coercion pi_arg_of_nat (n : nat) := Wrap n : pi_wrapped_arg.
Coercion pi_arg_of_fin_pred T pT (A : @fin_pred_sort T pT) : pi_wrapped_arg :=
  Wrap #|A|.

Definition pi_of (n : pi_unwrapped_arg) : nat_pred := [pred p \in primes n].

Notation "\pi ( n )" := (pi_of n)
  (at level 2, format "\pi ( n )") : nat_scope.
Notation "\p 'i' ( A )" := \pi(#|A|)
  (at level 2, format "\p 'i' ( A )") : nat_scope.

Definition pdiv n := head 1 (primes n).

Definition max_pdiv n := last 1 (primes n).

Definition divisors n := foldr add_divisors [:: 1] (prime_decomp n).

Definition phi n := foldr add_phi_factor (n > 0) (prime_decomp n).

(* Correctness of the decomposition algorithm. *)

Lemma prime_decomp_correct :
  let pd_val pd := \prod_(f <- pd) pfactor f.1 f.2 in
  let lb_dvd q m := ~~ has [pred d | d %| m] (index_iota 2 q) in
  let pf_ok f := lb_dvd f.1 f.1 && (0 < f.2) in
  let pd_ord q pd := path ltn q (unzip1 pd) in
  let pd_ok q n pd := [/\ n = pd_val pd, all pf_ok pd & pd_ord q pd] in
  forall n, n > 0 -> pd_ok 1 n (prime_decomp n).
Proof.
rewrite unlock => pd_val lb_dvd pf_ok pd_ord pd_ok.
have leq_pd_ok : forall m p q pd, q <= p -> pd_ok p m pd -> pd_ok q m pd.
  rewrite /pd_ok /pd_ord => m p q [|[r _] pd] //= leqp [<- ->].
  by case/andP; move/(leq_trans _)=> ->.
have apd_ok: forall m e q p pd, lb_dvd p p || (e == 0) -> q < p ->
     pd_ok p m pd -> pd_ok q (p ^ e * m) (p ^? e :: pd).
- move=> m [|e] q p pd; rewrite orbC /= => pr_p ltqp.
    rewrite mul1n; apply: leq_pd_ok; exact: ltnW.
  by rewrite /pd_ok /pd_ord /pf_ok /= pr_p ltqp => [[<- -> ->]].
case=> // n _; rewrite /prime_decomp.
case: elogn2P => e2 m2 -> {n}; case: m2 => [|[|abc]]; try exact: apd_ok.
rewrite [_.-2]/= !ltnS ltn0 natTrecE; case: edivnP => a bc ->{abc}.
case: edivnP => b c def_bc /= ltc2 ltbc3; apply: (apd_ok) => //.
move def_m: _.*2.+1 => m; set k := {2}1; rewrite -[2]/k.*2; set e := 0.
pose p := k.*2.+1; rewrite -{1}[m]mul1n -[1]/(p ^ e)%N.
have{def_m bc def_bc ltc2 ltbc3}:
   let kb := (ifnz e k 1).*2 in
   [&& k > 0, p < m, lb_dvd p m, c < kb & lb_dvd p p || (e == 0)]
    /\ m + (b * kb + c).*2 = p ^ 2 + (a * p).*2.
- rewrite -{-2}def_m; split=> //=; last first.
    by rewrite -def_bc addSn -double_add 2!addSn -addnA subnKC // addnC.
  rewrite ltc2 /lb_dvd /index_iota /= dvdn2 -def_m.
  by rewrite [_.+2]lock /= odd_double.
move: {2}a.+1 (ltnSn a) => n; clearbody k e.
elim: n => // n IHn in a k p m b c e *; rewrite ltnS => le_a_n [].
set kb := _.*2; set d := _ + c.
case/and5P=> lt0k ltpm leppm ltc pr_p def_m; have def_k1 := ltn_predK lt0k.
have def_kb1: kb.-1.+1 = kb by rewrite /kb -def_k1; case e.
have eq_bc_0: (b == 0) && (c == 0) = (d == 0).
  by rewrite addn_eq0 muln_eq0 orbC -def_kb1.
have lt1p: 1 < p by rewrite ltnS double_gt0.
have co_p_2: coprime p 2 by rewrite /coprime gcdnC gcdnE modn2 /= odd_double.
have if_d0: d = 0 -> [/\ m = (p + a.*2) * p, lb_dvd p p & lb_dvd p (p + a.*2)].
  move=> d0; have{d0 def_m} def_m: m = (p + a.*2) * p.
    by rewrite d0 addn0 -mulnn -!mul2n mulnA -muln_addl in def_m *.
  split=> //; apply/hasPn=> r; move/(hasPn leppm); apply: contra => /= dv_r.
    by rewrite def_m dvdn_mull.
  by rewrite def_m dvdn_mulr.
case def_a: a => [|a'] /= in le_a_n *; rewrite !natTrecE -/p {}eq_bc_0.
  case: d if_d0 def_m => [[//| def_m {pr_p}pr_p pr_m'] _ | d _ def_m] /=.
    rewrite def_m def_a addn0 mulnA -2!expnSr.
    by split; rewrite /pd_ord /pf_ok /= ?muln1 ?pr_p ?leqnn.
  apply: apd_ok; rewrite // /pd_ok /= /pfactor expn1 muln1 /pd_ord /= ltpm.
  rewrite /pf_ok !andbT /=; split=> //.
  apply: contra leppm; case/hasP=> r /=; rewrite mem_index_iota.
  case/andP=> lt1r ltrm dvrm; apply/hasP; case: (ltnP r p) => [ltrp | lepr].
    by exists r; rewrite // mem_index_iota lt1r.
  case/dvdnP: dvrm => q def_q; exists q; last by rewrite def_q /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1r)) -def_q mul1n ltrm.
  move: def_m; rewrite def_a addn0 -(@ltn_pmul2r p) // mulnn => <-.
  apply: (@leq_ltn_trans m); first by rewrite def_q leq_mul.
  by rewrite -addn1 leq_add2l.
have def_k2: k.*2 = ifnz e 1 k * kb.
  by rewrite /kb; case e => *; rewrite (mul1n, muln2).
case def_b': (b - _) => [|b']; last first.
  have ->: ifnz e k.*2.-1 1 = kb.-1 by rewrite /kb; case e.
  apply: IHn => {n le_a_n}//; rewrite -/p -/kb; split=> //.
    rewrite lt0k ltpm leppm pr_p andbT /=.
    by case: ifnzP; [move/ltn_predK->; exact: ltnW | rewrite def_kb1].
  apply: (@addIn p.*2).
  rewrite -2!addnA -!double_add -addnA -mulSnr -def_a -def_m /d.
  have ->: b * kb = b' * kb + (k.*2 - c * kb + kb).
    rewrite addnCA addnC -mulSnr -def_b' def_k2 -muln_subl -muln_addl subnK //.
    by rewrite ltnW // -subn_gt0 def_b'.
  rewrite -addnA; congr (_ + (_ + _).*2).
  case: (c) ltc; first by rewrite -addSnnS def_kb1 subn0 addn0 addnC.
  rewrite /kb; case e => [[] // _|e' c' _] /=; last first.
    by rewrite -subn_sub subnn addnC addSnnS.
  by rewrite mul1n -double_sub -double_add subn1 !addn1 def_k1.
have ltdp: d < p.
  move/eqP: def_b'; rewrite subn_eq0 -(@leq_pmul2r kb); last first.
    by rewrite -def_kb1.
  rewrite muln_subl -def_k2 ltnS -(leq_add2r c); move/leq_trans; apply.
  have{ltc} ltc: c < k.*2.
    by apply: (leq_trans ltc); rewrite leq_double /kb; case e.
  rewrite -{2}(subnK (ltnW ltc)) leq_add2r leq_sub2l //.
  by rewrite -def_kb1 mulnS leq_addr.
case def_d: d if_d0 => [|d'] => [[//|{def_m ltdp pr_p} def_m pr_p pr_m'] | _].
  rewrite eqxx -doubleS -addnS -def_a double_add -addSn -/p def_m.
  rewrite mulnCA mulnC -expnSr.
  apply: IHn => {n le_a_n}//; rewrite -/p -/kb; split.
    rewrite lt0k -addn1 leq_add2l {1}def_a pr_m' pr_p /= def_k1 -addnn.
    by rewrite leq_addr.
  rewrite -addnA -double_add addnCA def_a addSnnS def_k1 -(addnC k) -mulnSr.
  rewrite -[_.*2.+1]/p muln_addl double_add addnA -mul2n mulnA mul2n -mulSn.
  by rewrite -/p mulnn.
have next_pm: lb_dvd p.+2 m.
  rewrite /lb_dvd /index_iota 2!subSS subn0 -(subnK lt1p) iota_add.
  rewrite has_cat; apply/norP; split=> //=; rewrite orbF subnKC // orbC.
  apply/norP; split; apply/dvdnP=> [[q def_q]].
     case/hasP: leppm; exists 2; first by rewrite /p -(subnKC lt0k).
    by rewrite /= def_q dvdn_mull // dvdn2 /= odd_double.
  move/(congr1 (dvdn p)): def_m; rewrite -mulnn -!mul2n mulnA -muln_addl.
  rewrite dvdn_mull // dvdn_addr; last by rewrite def_q dvdn_mull.
  case/dvdnP=> r; rewrite mul2n => def_r; move: ltdp (congr1 odd def_r).
  rewrite odd_double -ltn_double {1}def_r -mul2n ltn_pmul2r //.
  by case: r def_r => [|[|[]]] //; rewrite def_d // mul1n /= odd_double.
apply: apd_ok => //; case: a' def_a le_a_n => [|a'] def_a => [_ | lta] /=.
  rewrite /pd_ok /= /pfactor expn1 muln1 /pd_ord /= ltpm /pf_ok !andbT /=.
  split => //; apply: contra next_pm.
  case/hasP=> q; rewrite mem_index_iota; case/andP=> lt1q ltqm dvqm.
  apply/hasP; case: (ltnP q p.+2) => [ltqp | lepq].
    by exists q; rewrite // mem_index_iota lt1q.
  case/dvdnP: dvqm => r def_r; exists r; last by rewrite def_r /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1q)) -def_r mul1n ltqm /=.
  rewrite -(@ltn_pmul2l p.+2) //; apply: (@leq_ltn_trans m).
    by rewrite def_r mulnC leq_mul.
  rewrite -addn2 mulnn sqrn_add mul2n muln2 -addnn addnCA -addnA addnCA addnA.
  by rewrite def_a mul1n in def_m; rewrite -def_m addnS -addnA ltnS leq_addr.
set bc := ifnz _ _ _; apply: leq_pd_ok (leqnSn _) _.
rewrite -doubleS -{1}[m]mul1n -[1]/(k.+1.*2.+1 ^ 0)%N.
apply: IHn; first exact: ltnW.
rewrite doubleS -/p [ifnz 0 _ _]/=; do 2?split => //.
  rewrite orbT next_pm /= -(leq_add2r d.*2) def_m 2!addSnnS -doubleS leq_add.
  - move: ltc; rewrite /kb {}/bc andbT; case e => //= e' _; case: ifnzP => //.
    by case: edivn2P.
  - by rewrite -{1}[p]muln1 -mulnn ltn_pmul2l.
  by rewrite leq_double def_a mulSn (leq_trans ltdp) ?leq_addr.
rewrite muln_addl !muln2 -addnA addnCA double_add addnCA.
rewrite (_ : _ + bc.2 = d); last first.
  rewrite /d {}/bc /kb -muln2.
  case: (e) (b) def_b' => //= _ []; first by case edivn2P.
  by case c; do 2?case; rewrite // mul1n /= muln2.
rewrite def_m 3!doubleS addnC -(addn2 p) sqrn_add mul2n muln2 -3!addnA.
congr (_ + _); rewrite 4!addnS -!double_add; congr _.*2.+2.+2.
by rewrite def_a -add2n muln_addl -addnA -muln2 -muln_addr mul2n.
Qed.

Lemma primePn : forall n,
  reflect (n < 2 \/ exists2 d, 1 < d < n & d %| n) (~~ prime n).
Proof.
rewrite /prime => [] [|[|p2]]; try by do 2!left.
case: (@prime_decomp_correct p2.+2) => //; rewrite unlock.
case: prime_decomp => [|[q [|[|e]]] pd] //=; last first; last by rewrite andbF.
  rewrite {1}/pfactor 2!expnS -!mulnA /=.
  case: (_ ^ _ * _) => [|u -> _]; first by rewrite !muln0.
  case/andP=> lt1q _; left; right; exists q; last by rewrite dvdn_mulr.
  have lt0q := ltnW lt1q; rewrite lt1q -{1}[q]muln1 ltn_pmul2l //.
  by rewrite -[2]muln1 leq_mul.
rewrite {1}/pfactor expn1; case: pd => [|[r e] pd] /=; last first.
  case: e => [|e] /=; first by rewrite !andbF.
  rewrite {1}/pfactor expnS -mulnA; case: (_ ^ _ * _) => [|u -> _].
    by rewrite !muln0.
  case/and3P=> lt1q ltqr _; left; right; exists q; last by rewrite dvdn_mulr.
  by rewrite lt1q -{1}[q]mul1n ltn_mul // -[q.+1]muln1 leq_mul.
rewrite muln1 !andbT => def_q pr_q lt1q; right; case=> // [[d]].
by rewrite def_q -mem_index_iota => in_d_2q dv_d_q; case/hasP: pr_q; exists d.
Qed.

Lemma primeP : forall p,
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).
Proof.
move=> p; rewrite -[prime p]negbK; case: primePn => [npr_p | pr_p].
  right=> [[lt1p pr_p]]; case: npr_p => [|[d n1pd]].
    by rewrite ltnNge lt1p.
  by move/pr_p; case/orP; move/eqP=> def_d; rewrite def_d ltnn ?andbF in n1pd.
case: leqP => [lep1 | lt1p]; first by case: pr_p; left.
left; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]]; case: pr_p; right.
exists d; rewrite // andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (dvdn_gt0 lt0p).
Qed.

Lemma prime_nt_dvdP : forall d p, prime p -> d != 1 -> reflect (d = p) (d %| p).
Proof.
move=> d p; case/primeP=> _ min_p d_neq1; apply: (iffP idP) => [|-> //].
by move/min_p; rewrite (negPf d_neq1) /=; move/eqP.
Qed.

Implicit Arguments primeP [p].
Implicit Arguments primePn [n].
Prenex Implicits primePn primeP.

Lemma prime_gt1 : forall p, prime p -> 1 < p.
Proof. by move=> p; case/primeP. Qed.

Lemma prime_gt0 : forall p, prime p -> 0 < p.
Proof. by move=> *; rewrite ltnW ?prime_gt1. Qed.

Hint Resolve prime_gt1 prime_gt0.

Lemma prod_prime_decomp : forall n,
  n > 0 -> n = \prod_(f <- prime_decomp n) f.1 ^ f.2.
Proof. by move=> n; case/prime_decomp_correct. Qed.

Lemma even_prime : forall p, prime p -> p = 2 \/ odd p.
Proof.
move=> p pr_p; case odd_p: (odd p); [by right | left].
have: 2 %| p by rewrite dvdn2 odd_p.
by case/primeP: pr_p => _ dv_p; move/dv_p; move/(2 =P p).
Qed.

Lemma prime_oddPn : forall p, prime p -> reflect (p = 2) (~~ odd p).
Proof.
by move=> p p_pr; apply: (iffP idP) => [|-> //]; case/even_prime: p_pr => ->.
Qed.

Lemma mem_prime_decomp : forall n p e,
  (p, e) \in prime_decomp n -> [/\ prime p, e > 0 & p ^ e %| n].
Proof.
move=> n p e; case: (posnP n) => [-> //| ].
case/prime_decomp_correct=> def_n mem_pd ord_pd pd_pe.
have:= allP mem_pd _ pd_pe; case/andP=> pr_p ->; split=> //; last first.
  case/splitPr: pd_pe def_n => pd1 pd2 ->.
  by rewrite big_cat big_cons /= mulnCA dvdn_mulr.
have lt1p: 1 < p.
  apply: (allP (order_path_min ltn_trans ord_pd)).
  by apply/mapP; exists (p, e).
apply/primeP; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]].
case/hasP: pr_p; exists d => //.
rewrite mem_index_iota andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (dvdn_gt0 lt0p).
Qed.

Lemma prime_coprime : forall p m, prime p -> coprime p m = ~~ (p %| m).
Proof.
move=> p m; case/primeP=> p_gt1 p_pr; apply/eqP/negP=> [d1 | ndv_pm].
  case/dvdnP=> k def_m; rewrite -(addn0 m) def_m gcdn_addl_mul gcdn0 in d1.
  by rewrite d1 in p_gt1.
by apply: gcdn_def => // d; move/p_pr; case/orP; move/eqP=> ->.
Qed.

Lemma dvdn_prime2 : forall p q, prime p -> prime q -> (p %| q) = (p == q).
Proof.
move=> p q pr_p pr_q; apply: negb_inj.
by rewrite eqn_dvd negb_and -!prime_coprime // coprime_sym orbb.
Qed.

Lemma euclid : forall m n p, prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
move=> m n p pr_p; case dv_pm: (p %| m); first exact: dvdn_mulr.
by rewrite gauss // prime_coprime // dv_pm.
Qed.

Lemma euclid1 : forall p, prime p -> (p %| 1) = false.
Proof. by move=> p; rewrite dvdn1; case: eqP => // ->. Qed.

Lemma euclid_exp : forall m n p, prime p -> (p %| m ^ n) = (p %| m) && (n > 0).
Proof.
move=> m [|n] p pr_p; first by rewrite andbF euclid1.
by apply: (inv_inj negbK); rewrite !andbT -!prime_coprime // coprime_pexpr.
Qed.

Lemma mem_primes : forall p n,
  (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
move=> p n; rewrite andbCA; case: posnP => [-> // | /= n_gt0].
apply/mapP/andP=> [[[q e]]|[pr_p]] /=.
  case/mem_prime_decomp=> pr_q e_gt0; case/dvdnP=> u -> -> {p}.
  by rewrite -(prednK e_gt0) expnS mulnCA dvdn_mulr.
rewrite {1}(prod_prime_decomp n_gt0) big_cond_seq /=.
apply big_prop => [| u v IHu IHv | [q e] /= mem_qe dv_p_qe].
- by rewrite euclid1.
- by rewrite euclid //; case/orP.
exists (q, e) => //=; case/mem_prime_decomp: mem_qe => pr_q _ _.
by rewrite euclid_exp // dvdn_prime2 // in dv_p_qe; case: eqP dv_p_qe.
Qed.

Lemma sorted_primes : forall n, sorted ltn (primes n).
Proof.
move=> n; case: (posnP n) => [-> // | ]; case/prime_decomp_correct=> _ _.
exact: path_sorted.
Qed.

Lemma eq_primes : forall m n, (primes m =i primes n) <-> (primes m = primes n).
Proof.
move=> m n; split=> [eqpr| -> //].
by apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes.
Qed.

Lemma primes_uniq : forall n, uniq (primes n).
Proof. move=> n; exact: (sorted_uniq ltn_trans ltnn (sorted_primes n)). Qed.

(* The smallest prime divisor *)

Lemma pi_pdiv : forall n, (pdiv n \in \pi(n)) = (n > 1).
Proof.
case=> [|[|n]] //; rewrite /pdiv !inE /primes.
have:= prod_prime_decomp (ltn0Sn n.+1); rewrite unlock.
by case: prime_decomp => //= pf pd _; rewrite mem_head.
Qed.

Lemma pdiv_prime : forall n, 1 < n -> prime (pdiv n).
Proof. by move=> n; rewrite -pi_pdiv mem_primes; case/and3P. Qed.

Lemma pdiv_dvd : forall n, pdiv n %| n.
Proof.
move=> n; case: n (pi_pdiv n) => [|[|n]] //.
by rewrite mem_primes; case/and3P.
Qed.

Lemma pi_max_pdiv : forall n, (max_pdiv n \in \pi(n)) = (n > 1).
Proof.
move=> n; rewrite !inE -pi_pdiv /max_pdiv /pdiv !inE.
by case: primes => //= p ps; rewrite mem_head mem_last.
Qed.

Lemma max_pdiv_prime : forall n, n > 1 -> prime (max_pdiv n).
Proof. by move=> n; rewrite -pi_max_pdiv mem_primes; case/andP. Qed.

Lemma max_pdiv_dvd : forall n, max_pdiv n %| n.
Proof.
move=> n; case: n (pi_max_pdiv n) => [|[|n]] //.
by rewrite mem_primes; case/andP.
Qed.

Lemma pdiv_leq : forall n, 0 < n -> pdiv n <= n.
Proof. by move=> n n_gt0; rewrite dvdn_leq // pdiv_dvd. Qed.

Lemma max_pdiv_leq : forall n, 0 < n -> max_pdiv n <= n.
Proof. by move=> n n_gt0; rewrite dvdn_leq // max_pdiv_dvd. Qed.

Lemma pdiv_gt0 : forall n, 0 < pdiv n.
Proof. by case=> [|[|n]] //; rewrite prime_gt0 ?pdiv_prime. Qed.

Lemma max_pdiv_gt0 : forall n, 0 < max_pdiv n.
Proof. by case=> [|[|n]] //; rewrite prime_gt0 ?max_pdiv_prime. Qed.
Hint Resolve pdiv_gt0 max_pdiv_gt0.

Lemma pdiv_min_dvd : forall m d, 1 < d -> d %| m -> pdiv m <= d.
Proof.
move=> m d lt1d dv_d_m; case: (posnP m) => [->|mpos]; first exact: ltnW.
rewrite /pdiv; apply: leq_trans (pdiv_leq (ltnW lt1d)).
have: pdiv d \in primes m.
  by rewrite mem_primes mpos pdiv_prime // (dvdn_trans (pdiv_dvd d)).
case: primes (sorted_primes m) => //= p pm ord_pm.
rewrite inE; case/predU1P=> [-> //|].
move/(allP (order_path_min ltn_trans ord_pm)); exact: ltnW.
Qed.

Lemma max_pdiv_max : forall n p, p \in \pi(n) -> p <= max_pdiv n.
Proof.
move=> n p; rewrite /max_pdiv !inE => n_p.
case/splitPr: n_p (sorted_primes n) => p1 p2; rewrite last_cat -cat_rcons /=.
rewrite headI /= path_cat -(last_cons 0) -headI last_rcons; case/andP=> _.
move/(order_path_min ltn_trans); case/lastP: p2 => //= p2 q.
by rewrite all_rcons last_rcons ltn_neqAle -andbA; case/and3P.
Qed.

Lemma ltn_pdiv2_prime : forall n, 0 < n -> n < pdiv n ^ 2 -> prime n.
Proof.
move=> n; case def_n: n => [|[|n']] // _; rewrite -def_n => lt_n_p2.
suff ->: n = pdiv n by rewrite pdiv_prime ?def_n.
apply/eqP; rewrite eqn_leq leqNgt andbC pdiv_leq; last by rewrite def_n.
move: lt_n_p2; rewrite ltnNge; apply: contra => lt_pm_m.
case/dvdnP: (pdiv_dvd n) => q def_q.
rewrite {2}def_q -mulnn leq_pmul2r // pdiv_min_dvd //.
  by rewrite -[pdiv n]mul1n {2}def_q ltn_pmul2r in lt_pm_m.
by rewrite def_q dvdn_mulr.
Qed.

Lemma primePns : forall n,
  reflect (n < 2 \/ exists p, [/\ prime p, p ^ 2 <= n & p %| n]) (~~ prime n).
Proof.
move=> n; apply: (iffP idP) => [npr_p|]; last first.
  case=> [|[p [pr_p le_p2_n dv_p_n]]]; first by case: n => [|[]].
  apply/negP=> pr_n; move: dv_p_n le_p2_n; rewrite dvdn_prime2 //; move/eqP->.
  by rewrite leqNgt -{1}[n]muln1 -mulnn ltn_pmul2l ?prime_gt1 ?prime_gt0.
case: leqP => [lt1p|]; [right | by left].
exists (pdiv n); rewrite pdiv_dvd pdiv_prime //; split=> //.
by case: leqP npr_p => //; move/ltn_pdiv2_prime->; auto.
Qed.

Implicit Arguments primePns [n].
Prenex Implicits primePns.

Lemma pdivP : forall n, n > 1 -> {p | prime p & p %| n}.
Proof. by move=> n lt1n; exists (pdiv n); rewrite ?pdiv_dvd ?pdiv_prime. Qed.

Lemma primes_mul : forall m n p, m > 0 -> n > 0 ->
  (p \in primes (m * n)) = (p \in primes m) || (p \in primes n).
Proof.
move=> m n p m_gt0 n_gt0; rewrite !mem_primes muln_gt0 m_gt0 n_gt0.
by case pr_p: (prime p); rewrite // euclid.
Qed.

Lemma primes_exp : forall m n, n > 0 -> primes (m ^ n) = primes m.
Proof.
move=> m [|n] // _; rewrite expnS; case: (posnP m) => [-> //| m_gt0].
apply/eq_primes => /= p; elim: n => [|n IHn]; first by rewrite muln1.
by rewrite primes_mul ?(expn_gt0, expnS, IHn, orbb, m_gt0).
Qed.

Lemma primes_prime : forall p, prime p -> primes p = [::p].
Proof.
move=> p pr_p; apply: (eq_sorted_irr ltn_trans ltnn) => // [|q].
  exact: sorted_primes.
rewrite mem_seq1 mem_primes prime_gt0 //=.
by apply/andP/idP=> [[pr_q q_p] | ]; [rewrite -dvdn_prime2 | move/eqP->].
Qed.

Lemma coprime_has_primes : forall m n, m > 0 -> n > 0 ->
  coprime m n = ~~ has (mem (primes m)) (primes n).
Proof.
move=> m n m_gt0 n_gt0; apply/eqnP/hasPn=> [mn1 p | no_p_mn].
  rewrite /= !mem_primes m_gt0 n_gt0 /=; case/andP=> pr_p p_n.
  have:= prime_gt1 pr_p; rewrite pr_p ltnNge -mn1 /=; apply: contra => p_m.
  by rewrite dvdn_leq ?gcdn_gt0 ?m_gt0 // dvdn_gcd ?p_m.
case: (ltngtP (gcdn m n) 1) => //; first by rewrite ltnNge gcdn_gt0 ?m_gt0.
move/pdiv_prime; set p := pdiv _ => pr_p.
move/implyP: (no_p_mn p); rewrite /= !mem_primes m_gt0 n_gt0 pr_p /=.
by rewrite !(dvdn_trans (pdiv_dvd _)) // (dvdn_gcdl, dvdn_gcdr).
Qed.

Lemma pdiv_id : forall p, prime p -> pdiv p = p.
Proof. by move=> p p_pr; rewrite /pdiv primes_prime. Qed.

Lemma pdiv_pfactor : forall p k, prime p -> pdiv (p ^ k.+1) = p.
Proof. by move=> p k p_pr; rewrite /pdiv primes_exp ?primes_prime. Qed.

(* "prime" logarithms and p-parts. *)

Fixpoint logn_rec (d m r : nat) {struct r} : nat :=
  match r, edivn m d with
  | r'.+1, (_.+1 as m', 0) => (logn_rec d m' r').+1
  | _, _ => 0
  end.

Definition logn p m := if prime p then logn_rec p m m else 0.

Lemma lognE : forall p m,
  logn p m = if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).+1 else 0.
Proof.
rewrite /logn /dvdn => p m; case p_pr: (prime p) => //.
rewrite /divn modn_def; case def_m: {2 3}m => [|m'] //=.
case: edivnP def_m => [[|q] [|r] -> _] // def_m; congr _.+1; rewrite [_.1]/=.
have{m def_m}: q < m'.
  by rewrite -ltnS -def_m addn0 mulnC -{1}[q.+1]mul1n ltn_pmul2r // prime_gt1.
elim: {m' q}_.+1 {-2}m' q.+1 (ltnSn m') (ltn0Sn q) => // s IHs.
case=> [[]|r] //= m; rewrite ltnS => lt_rs m_gt0 le_mr.
rewrite -{3}[m]prednK //=; case: edivnP => [[|q] [|_] def_q _] //.
have{def_q} lt_qm': q < m.-1.
  by rewrite -[q.+1]muln1 -ltnS prednK // def_q addn0 ltn_pmul2l // prime_gt1.
have{le_mr} le_m'r: m.-1 <= r by rewrite -ltnS prednK.
by rewrite (IHs r) ?(IHs m.-1) // ?(leq_trans lt_qm', leq_trans _ lt_rs).
Qed.

Lemma logn_gt0 : forall p n, (0 < logn p n) = (p \in primes n).
Proof. by move=> p n; rewrite lognE -mem_primes; case: {+}(p \in _). Qed.

Lemma ltn_log0 : forall p n, n < p -> logn p n = 0.
Proof. by move=> p [|n] ltnp; rewrite lognE ?andbF // gtnNdvd ?andbF. Qed.

Lemma logn0 : forall p, logn p 0 = 0.
Proof. by move=> p; rewrite /logn if_same. Qed.

Lemma logn1 : forall p, logn p 1 = 0.
Proof. by move=> p; rewrite lognE dvdn1 /= andbC; case: eqP => // ->. Qed.

Lemma pfactor_gt0 : forall p n, 0 < p ^ logn p n.
Proof. by move=> p n; rewrite expn_gt0 lognE; case: (posnP p) => // ->. Qed.
Hint Resolve pfactor_gt0.

Lemma pfactor_dvdn : forall p n m,
  prime p -> m > 0 -> (p ^ n %| m) = (n <= logn p m).
Proof.
move=> p n m p_pr; elim: n m => [|n IHn] m m_gt0; first exact: dvd1n.
rewrite lognE p_pr m_gt0 /=; case dv_pm: (p %| m); last first.
  apply/dvdnP=> [] [/= q def_m].
  by rewrite def_m expnS mulnCA dvdn_mulr in dv_pm.
case/dvdnP: dv_pm m_gt0 => q ->{m}; rewrite muln_gt0; case/andP=> p_gt0 q_gt0.
by rewrite expnSr dvdn_pmul2r // mulnK // IHn.
Qed.

Lemma pfactor_dvdnn : forall p n, p ^ logn p n %| n.
Proof.
move=> p [|n] //; case pr_p: (prime p); first by rewrite pfactor_dvdn.
by rewrite lognE pr_p dvd1n.
Qed.

Lemma logn_prime : forall p q, prime q -> logn p q = (p == q).
Proof.
move=> p q pr_q; have q_gt0 := prime_gt0 pr_q; rewrite lognE q_gt0 /=.
case pr_p: (prime p); last by case: eqP pr_p pr_q => // -> ->.
by rewrite dvdn_prime2 //; case: eqP => // ->; rewrite divnn q_gt0 logn1.
Qed.

Lemma pfactor_coprime : forall p n, prime p -> n > 0 ->
  {m | coprime p m & n = m * p ^ logn p n}.
Proof.
move=> p n p_pr n_gt0; set k := logn p n.
have dv_pk_n: p ^ k %| n by rewrite pfactor_dvdn.
exists (n %/ p ^ k); last by rewrite divnK.
rewrite prime_coprime // -(@dvdn_pmul2r (p ^ k)) ?expn_gt0 ?prime_gt0 //.
by rewrite -expnS divnK // pfactor_dvdn // ltnn.
Qed.

Lemma pfactorK : forall p n, prime p -> logn p (p ^ n) = n.
Proof.
move=> p n p_pr; have pn_gt0: p ^ n > 0 by rewrite expn_gt0 prime_gt0.
apply/eqP; rewrite eqn_leq -pfactor_dvdn // dvdnn andbT.
by rewrite -(leq_exp2l _ _ (prime_gt1 p_pr)) dvdn_leq // pfactor_dvdn.
Qed.

Lemma pfactorKpdiv : forall p n,
  prime p -> logn (pdiv (p ^ n)) (p ^ n) = n.
Proof. by move=> p [//|n] p_pr; rewrite pdiv_pfactor ?pfactorK. Qed.

Lemma dvdn_leq_log : forall p m n, 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
move=> p m n n_gt0 dv_m_n; have m_gt0 := dvdn_gt0 n_gt0 dv_m_n.
case p_pr: (prime p); last by do 2!rewrite lognE p_pr /=.
by rewrite -pfactor_dvdn //; apply: dvdn_trans dv_m_n; rewrite pfactor_dvdn.
Qed.

Lemma logn_gauss : forall p m n, coprime p m -> logn p (m * n) = logn p n.
Proof.
move=> p m n co_pm; case p_pr: (prime p); last by rewrite /logn p_pr.
case: (posnP n) => [->|n_gt0]; first by rewrite muln0.
case: (posnP m) => [m0|m_gt0].
  by rewrite m0 prime_coprime ?dvdn0 in co_pm.
have mn_gt0: m * n > 0 by rewrite muln_gt0 m_gt0.
apply/eqP; rewrite eqn_leq andbC dvdn_leq_log ?dvdn_mull //.
set k := logn p _; have: p ^ k %| m * n by rewrite pfactor_dvdn.
by rewrite gauss ?coprime_expl // -pfactor_dvdn.
Qed.

Lemma logn_mul : forall p m n,
  0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
move=> p m n; case p_pr: (prime p); last by rewrite /logn p_pr.
have xlp := pfactor_coprime p_pr.
case/xlp=> m' co_m' def_m; case/xlp=> n' co_n' def_n {xlp}.
by rewrite {1}def_m {1}def_n mulnCA -mulnA -expn_add !logn_gauss // pfactorK.
Qed.

Lemma logn_exp : forall p m n, logn p (m ^ n) = n * logn p m.
Proof.
move=> p m n; case p_pr: (prime p); last by rewrite /logn p_pr muln0.
elim: n => [|n IHn]; first by rewrite logn1.
case: (posnP m) => [->|m_gt0]; first by rewrite exp0n // lognE andbF muln0.
by rewrite expnS logn_mul ?IHn // expn_gt0 m_gt0.
Qed.

Lemma logn_div : forall p m n, m %| n -> logn p (n %/ m) = logn p n - logn p m.
Proof.
move=> p m n; rewrite dvdn_eq; move/eqP=> def_n.
case: (posnP n) => [-> |]; first by rewrite div0n logn0.
by rewrite -{1 3}def_n muln_gt0; case/andP=> *; rewrite logn_mul ?addnK.
Qed.

Lemma dvdn_pfactor : forall p d n, prime p ->
  reflect (exists2 m, m <= n & d = p ^ m) (d %| p ^ n).
Proof.
move=> p d n p_pr; have pn_gt0: p ^ n > 0 by rewrite expn_gt0 prime_gt0.
apply: (iffP idP) => [dv_d_pn|[m le_m_n ->]]; last first.
  by rewrite -(subnK le_m_n) expn_add dvdn_mull.
exists (logn p d); first by rewrite -(pfactorK n p_pr) dvdn_leq_log.
have d_gt0: d > 0 by exact: dvdn_gt0 dv_d_pn.
case: (pfactor_coprime p_pr d_gt0) => q co_p_q def_d.
rewrite {1}def_d ((q =P 1) _) ?mul1n // -dvdn1.
suff: q %| p ^ n * 1 by rewrite gauss // coprime_sym coprime_expl.
by rewrite muln1 (dvdn_trans _ dv_d_pn) // def_d dvdn_mulr.
Qed.

Lemma prime_decompE : forall n,
  prime_decomp n = map (fun p => (p, logn p n)) (primes n).
Proof.
move=> [//|n]; pose f0 := (0, 0); rewrite -map_comp.
apply: (@eq_from_nth _ f0) => [|i lt_i_n]; first by rewrite size_map.
rewrite (nth_map f0) //; case def_f: (nth _ _ i) => [p e] /=.
congr (_, _); rewrite [n.+1]prod_prime_decomp //.
have: (p, e) \in prime_decomp n.+1 by rewrite -def_f mem_nth.
case/mem_prime_decomp=> pr_p _ _.
rewrite (big_nth f0) big_mkord (bigD1 (Ordinal lt_i_n)) //=.
rewrite def_f mulnC logn_gauss ?pfactorK //.
apply big_prop => [|m1 m2 com1 com2| [j ltj] /=]; first exact: coprimen1.
  by rewrite coprime_mulr com1.
rewrite -val_eqE /= => nji; case def_j: (nth _ _ j) => [q e1] /=.
have: (q, e1) \in prime_decomp n.+1 by rewrite -def_j mem_nth.
case/mem_prime_decomp=> pr_q e1_gt0 _; rewrite coprime_pexpr //.
rewrite prime_coprime // dvdn_prime2 //; apply: contra nji => eq_pq.
rewrite -(nth_uniq 0 _ _ (primes_uniq n.+1)) ?size_map //=.
by rewrite !(nth_map f0) //  def_f def_j /= eq_sym.
Qed.

(* pi- parts *)

(* Testing for membership in set of prime factors. *)

Canonical Structure nat_pred_pred := Eval hnf in [predType of nat_pred].

Coercion nat_pred_of_nat (p : nat) : nat_pred := pred1 p.

Section NatPreds.

Variables (n : nat) (pi : nat_pred).

Definition negn : nat_pred := [predC pi].

Definition pnat : pred nat := fun m => (m > 0) && all (mem pi) (primes m).

Definition partn := \prod_(0 <= p < n.+1 | p \in pi) p ^ logn p n.

End NatPreds.

Notation "pi ^'" := (negn pi) (at level 2, format "pi ^'") : nat_scope.

Notation "pi .-nat" := (pnat pi) (at level 2, format "pi .-nat") : nat_scope.

Notation "n `_ pi" := (partn n pi) : nat_scope.

Lemma negnK : forall pi, pi^'^' =i pi.
Proof. move=> pi p; exact: negbK. Qed.

Lemma eq_negn : forall pi1 pi2, pi1 =i pi2 -> pi1^' =i pi2^'.
Proof. by move=> pi1 pi2 eq_pi n; rewrite 3!inE /= eq_pi.
Qed.

Lemma eq_piP : forall m n, \pi(m) =i \pi(n) <-> \pi(m) = \pi(n).
Proof.
rewrite /pi_of => m n; have eqs := eq_sorted_irr ltn_trans ltnn.
by split=> [|-> //]; move/(eqs _ _ (sorted_primes m) (sorted_primes n)) ->.
Qed.

Lemma part_gt0 : forall pi n, 0 < n`_pi.
Proof. move=> pi n; exact: prodn_gt0. Qed.
Hint Resolve part_gt0.

Lemma sub_in_partn : forall pi1 pi2 n,
  {in \pi(n), {subset pi1 <= pi2}} -> n`_pi1 %| n`_pi2.
Proof.
move=> pi1 pi2 n pi12; rewrite ![n`__]big_mkcond /=.
apply (big_rel (fun m1 m2 => m1 %| m2)) => // [*|p _]; first exact: dvdn_mul.
rewrite lognE -mem_primes; case: ifP => pi1p; last exact: dvd1n.
by case: ifP => pr_p; [rewrite pi12 | rewrite if_same].
Qed.

Lemma eq_in_partn : forall (pi1 pi2 : nat_pred) n,
  {in \pi(n), pi1 =i pi2} -> n`_pi1 = n`_pi2.
Proof.
move=> pi1 pi2 n pi12; apply/eqP.
by rewrite eqn_dvd ?sub_in_partn // => p; move/pi12->.
Qed.

Lemma eq_partn : forall (pi1 pi2 : nat_pred) n, pi1 =i pi2 -> n`_pi1 = n`_pi2.
Proof. by move=> pi1 pi2 n pi12; apply: eq_in_partn => p _. Qed.

Lemma partnNK : forall pi n, n`_pi^'^' = n`_pi.
Proof. by move=> pi n; apply: eq_partn; exact: negnK. Qed.

Lemma widen_partn : forall m pi n,
  n <= m -> n`_pi = \prod_(0 <= p < m.+1 | p \in pi) p ^ logn p n.
Proof.
move=> m pi n le_n_m; rewrite big_mkcond /=.
rewrite [n`_pi](big_nat_widen _ _ m.+1) // big_mkcond /=.
apply: eq_bigr => p _; rewrite ltnS lognE.
by case: and3P => [[_ *]|]; rewrite ?if_same // andbC dvdn_leq.
Qed.

Lemma partn0 : forall pi, 0`_pi = 1.
Proof. by move=> pi; apply: big1_seq => [] [|n]; rewrite andbC. Qed.

Lemma partn1 : forall pi, 1`_pi = 1.
Proof. by move=> pi; apply: big1_seq => [] [|[|n]]; rewrite andbC. Qed.

Lemma partn_mul : forall pi m n, m > 0 -> n > 0 -> (m * n)`_pi = m`_pi * n`_pi.
Proof.
have le_pmul: forall m n, m > 0 -> n <= m * n by case=> // *; exact: leq_addr.
move=> pi m n mpos npos; rewrite !(@widen_partn (n * m)) 3?(le_pmul, mulnC) //.
rewrite !big_mkord -big_split; apply: eq_bigr => p _ /=.
by rewrite logn_mul // expn_add.
Qed.

Lemma partn_exp : forall pi m n, (m ^ n)`_pi = m`_pi ^ n.
Proof.
move=> pi m; elim=> [|n IHn]; first exact: partn1.
rewrite expnS; case: (posnP m) => [->|m_gt0]; first by rewrite partn0 exp1n.
by rewrite expnS partn_mul ?IHn // expn_gt0 m_gt0.
Qed.

Lemma partn_dvd : forall pi m n, n > 0 -> m %| n -> m`_pi %| n`_pi.
Proof.
move=> pi m n n_gt0 dvmn; case/dvdnP: dvmn n_gt0 => q ->{n}.
by rewrite muln_gt0; case/andP=> q_gt0 m_gt0; rewrite partn_mul ?dvdn_mull.
Qed.

Lemma p_part : forall p n : nat, n`_p = p ^ logn p n.
Proof.
move=> p n; case (posnP (logn p n)) => [log0 |].
  by rewrite log0 [n`_p]big1_seq // => q; case/andP; move/eqnP->; rewrite log0.
rewrite logn_gt0 mem_primes; case/and3P=> _ n_gt0 dv_p_n.
have le_p_n: p < n.+1 by rewrite ltnS dvdn_leq.
by rewrite [n`_p]big_mkord (big_pred1 (Ordinal le_p_n)).
Qed.

Lemma p_part_eq1 : forall p n : nat, (n`_p == 1) = (p \notin \pi(n)).
Proof.
move=> p n; rewrite mem_primes p_part lognE; case: and3P => // [[p_pr _ _]].
by rewrite -dvdn1 pfactor_dvdn // logn1.
Qed.

Lemma p_part_gt1 : forall p n : nat, (n`_p > 1) = (p \in \pi(n)).
Proof.
by move=> p n; rewrite ltn_neqAle part_gt0 andbT eq_sym p_part_eq1 negbK.
Qed.

Lemma primes_part : forall pi n, primes n`_pi = filter (mem pi) (primes n).
Proof.
move=> pi n; have ltnT := ltn_trans.
case: (posnP n) => [-> | n_gt0]; first by rewrite partn0.
apply: (eq_sorted_irr ltnT ltnn); rewrite ?(sorted_primes, sorted_filter) //.
move=> p; rewrite mem_filter /= !mem_primes n_gt0 part_gt0 /=.
apply/andP/and3P=> [[p_pr] | [pi_p p_pr dv_p_n]].
  rewrite /partn; apply big_prop => [|n1 n2 IHn1 IHn2|q pi_q].
  - by rewrite dvdn1; case: eqP p_pr => // ->.
  - by rewrite euclid //; case/orP.
  rewrite -{1}(expn1 p) pfactor_dvdn // logn_exp muln_gt0.
  rewrite logn_gt0 mem_primes n_gt0 - andbA /=; case/and3P=> pr_q dv_q_n.
  by rewrite logn_prime //; case: eqP => // ->.
have le_p_n: p < n.+1 by rewrite ltnS dvdn_leq.
rewrite [n`_pi]big_mkord (bigD1 (Ordinal le_p_n)) //= dvdn_mulr //.
by rewrite lognE p_pr n_gt0 dv_p_n expnS dvdn_mulr.
Qed.

Lemma filter_pi_of : forall n m,
  n < m -> filter \pi(n) (index_iota 0 m) = primes n.
Proof.
move=> n m lt_n_m; have ltnT := ltn_trans; apply: (eq_sorted_irr ltnT ltnn).
- by rewrite sorted_filter // sorted_ltn_iota.
- exact: sorted_primes.
move=> p; rewrite mem_filter mem_index_iota /= mem_primes; case: and3P => //.
case=> _ n_gt0 dv_p_n; apply: leq_ltn_trans lt_n_m; exact: dvdn_leq.
Qed.

Lemma partn_pi : forall n, n > 0 -> n`_\pi(n) = n.
Proof.
move=> n n_gt0; rewrite {3}(prod_prime_decomp n_gt0) prime_decompE big_map.
by rewrite -[n`__]big_filter filter_pi_of.
Qed.

Lemma partnT : forall n, n > 0 -> n`_predT = n.
Proof.
move=> n n_gt0; rewrite -{2}(partn_pi n_gt0) {2}/partn big_mkcond /=.
by apply: eq_bigr => p _; rewrite -logn_gt0; case: (logn p _).
Qed.

Lemma partnC : forall pi n, n > 0 -> n`_pi * n`_pi^' = n.
Proof.
move=> pi n n_gt0; rewrite -{3}(partnT n_gt0) /partn.
do 2!rewrite mulnC big_mkcond /=; rewrite -big_split; apply: eq_bigr => p _ /=.
by rewrite mulnC inE /=; case: (p \in pi); rewrite /= (muln1, mul1n).
Qed.

Lemma dvdn_part : forall pi n, n`_pi %| n.
Proof. by move=> pi [|n] //; rewrite -{2}[n.+1](@partnC pi) // dvdn_mulr. Qed.

Lemma logn_part : forall p m, logn p m`_p = logn p m.
Proof.
move=> p m; case p_pr: (prime p); first by rewrite p_part pfactorK.
by rewrite lognE (lognE p m) p_pr.
Qed.
    
Lemma partn_lcm : forall pi m n,
  m > 0 -> n > 0 -> (lcmn m n)`_pi = lcmn m`_pi n`_pi.
Proof.
move=> pi m n m_gt0 n_gt0; have p_gt0: lcmn m n > 0 by rewrite lcmn_gt0 m_gt0.
apply/eqP; rewrite eqn_dvd dvdn_lcm !partn_dvd ?dvdn_lcml ?dvdn_lcmr //.
rewrite -(dvdn_pmul2r (part_gt0 pi^' (lcmn m n))) partnC // dvdn_lcm !andbT.
rewrite -{1}(partnC pi m_gt0) andbC -{1}(partnC pi n_gt0).
by rewrite !dvdn_mul ?partn_dvd ?dvdn_lcml ?dvdn_lcmr.
Qed. 

Lemma partn_gcd : forall pi m n,
  m > 0 -> n > 0 -> (gcdn m n)`_pi = gcdn m`_pi n`_pi.
Proof.
move=> pi m n m_gt0 n_gt0; have p_gt0: gcdn m n > 0 by rewrite gcdn_gt0 m_gt0.
apply/eqP; rewrite eqn_dvd dvdn_gcd !partn_dvd ?dvdn_gcdl ?dvdn_gcdr //=.
rewrite -(dvdn_pmul2r (part_gt0 pi^' (gcdn m n))) partnC // dvdn_gcd.
rewrite -{3}(partnC pi m_gt0) andbC -{3}(partnC pi n_gt0).
by rewrite !dvdn_mul ?partn_dvd ?dvdn_gcdl ?dvdn_gcdr.
Qed. 

Lemma partn_biglcm : forall (I : finType) (P : pred I) F pi,
    (forall i, P i -> F i > 0) ->
  (\big[lcmn/1%N]_(i | P i) F i)`_pi = \big[lcmn/1%N]_(i | P i) (F i)`_pi.
Proof.
move=> I P F pi F_gt0; set m := \big[lcmn/1%N]_(i | P i) F i.
have m_gt0: 0 < m by apply big_prop => // p q p_gt0; rewrite lcmn_gt0 p_gt0.
apply/eqP; rewrite eqn_dvd andbC; apply/andP; split.
  by apply/dvdn_biglcmP=> i Pi; rewrite partn_dvd // (@biglcmn_sup _ i).
rewrite -(dvdn_pmul2r (part_gt0 pi^' m)) partnC //.
apply/dvdn_biglcmP=> i Pi; rewrite -(partnC pi (F_gt0 i Pi)) dvdn_mul //.
  by rewrite (@biglcmn_sup _ i).
by rewrite partn_dvd // (@biglcmn_sup _ i).
Qed.

Lemma partn_biggcd : forall (I : finType) (P : pred I) F pi,
    #|SimplPred P| > 0 -> (forall i, P i -> F i > 0) ->
  (\big[gcdn/0]_(i | P i) F i)`_pi = \big[gcdn/0]_(i | P i) (F i)`_pi.
Proof.
move=> I P F pi ntP F_gt0; set d := \big[gcdn/0]_(i | P i) F i.
have d_gt0: 0 < d.
  case/card_gt0P: ntP => i /= Pi; have:= F_gt0 i Pi.
  rewrite !lt0n -!dvd0n; apply: contra => dv0d.
  by rewrite (dvdn_trans dv0d) // (@biggcdn_inf _ i).
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  by apply/dvdn_biggcdP=> i Pi; rewrite partn_dvd ?F_gt0 // (@biggcdn_inf _ i).
rewrite -(dvdn_pmul2r (part_gt0 pi^' d)) partnC //.
apply/dvdn_biggcdP=> i Pi; rewrite -(partnC pi (F_gt0 i Pi)) dvdn_mul //.
  by rewrite (@biggcdn_inf _ i).
by rewrite partn_dvd ?F_gt0 // (@biggcdn_inf _ i).
Qed.

Section PiNat.

Implicit Types p n m : nat.
Implicit Type pi rho : nat_pred.

Lemma sub_in_pnat : forall pi rho n,
  {in \pi(n), {subset pi <= rho}} -> pi.-nat n -> rho.-nat n.
Proof.
rewrite /pnat => pi rho n subpi; case/andP=> -> pi_n.
apply/allP=> p pr_p; apply: subpi => //; exact: (allP pi_n).
Qed.

Lemma eq_in_pnat : forall pi rho n,
  {in \pi(n), pi =i rho} -> pi.-nat n = rho.-nat n.
Proof.
by move=> pi rho n eqpi; apply/idP/idP; apply: sub_in_pnat => p; move/eqpi->.
Qed.

Lemma eq_pnat : forall pi rho n, pi =i rho -> pi.-nat n = rho.-nat n.
Proof. by move=> pi rho n eqpi; apply: eq_in_pnat => p _. Qed.

Lemma pnatNK : forall pi n, pi^'^'.-nat n = pi.-nat n.
Proof. move=> pi n; exact: eq_pnat (negnK pi). Qed.

Lemma pnatI : forall pi rho n,
  [predI pi & rho].-nat n = pi.-nat n && rho.-nat n.
Proof. by move=> pi rho n; rewrite /pnat andbCA all_predI !andbA andbb. Qed.

Lemma pnat_mul : forall pi m n, pi.-nat (m * n) = pi.-nat m && pi.-nat n.
Proof.
move=> pi m n; rewrite /pnat muln_gt0 andbCA -andbA andbCA.
case: posnP => // n_gt0; case: posnP => //= m_gt0.
apply/allP/andP=> [pi_mn | [pi_m pi_n] p].
  by split; apply/allP=> p m_p; apply: pi_mn; rewrite primes_mul // m_p ?orbT.
rewrite primes_mul //; case/orP; [exact: (allP pi_m) | exact: (allP pi_n)].
Qed.

Lemma pnat_exp : forall pi m n, pi.-nat (m ^ n) = pi.-nat m || (n == 0).
Proof.
by move=> pi m [|n]; rewrite orbC // /pnat expn_gt0 orbC primes_exp.
Qed.

Lemma part_pnat : forall pi n, pi.-nat n`_pi.
Proof.
move=> pi n; rewrite /pnat primes_part part_gt0.
by apply/allP=> p; rewrite mem_filter; case/andP.
Qed.

Lemma pnatE : forall pi p, prime p -> pi.-nat p = (p \in pi).
Proof.
by move=> pi p pr_p; rewrite /pnat prime_gt0 ?primes_prime //= andbT.
Qed.

Lemma pnat_id : forall p, prime p -> p.-nat p.
Proof. by move=> p pr_p; rewrite pnatE ?inE /=. Qed.

Lemma coprime_pi' : forall m n,
   m > 0 -> n > 0 -> coprime m n = \pi(m)^'.-nat n.
Proof.
by move=> m n m_gt0 n_gt0; rewrite /pnat n_gt0 all_predC coprime_has_primes.
Qed.

Lemma pnat_pi : forall n, n > 0 -> \pi(n).-nat n.
Proof. rewrite /pnat => n ->; exact/allP. Qed.

Lemma pi_of_dvd : forall m n, m %| n -> n > 0 -> {subset \pi(m) <= \pi(n)}.
Proof.
move=> m n m_dv_n n_gt0 p; rewrite !mem_primes n_gt0; case/and3P=> -> _ p_dv_m.
exact: dvdn_trans p_dv_m m_dv_n.
Qed.

Lemma pi_of_muln : forall m n,
  m > 0 -> n > 0 -> \pi(m * n) =i [predU \pi(m) & \pi(n)].
Proof. move=> m n m_gt0 n_gt0 p; exact: primes_mul. Qed.

Lemma pi_of_partn : forall pi n, n > 0 -> \pi(n`_pi) =i [predI \pi(n) & pi].
Proof. by move=> pi n n_gt0 p; rewrite /pi_of primes_part mem_filter andbC. Qed.

Lemma pi_of_exp : forall p n, n > 0 -> \pi(p ^ n) = \pi(p).
Proof. by move=> p n n_gt0; rewrite /pi_of primes_exp. Qed.

Lemma pi_of_prime : forall p, prime p -> \pi(p) =i (p : nat_pred).
Proof. by move=> p pr_p q; rewrite /pi_of primes_prime // mem_seq1. Qed.

Lemma p'natEpi : forall p n, n > 0 -> p^'.-nat n = (p \notin \pi(n)).
Proof. by move=> p [|n] // _; rewrite /pnat all_predC has_pred1. Qed.

Lemma p'natE : forall p n, prime p -> p^'.-nat n = ~~ (p %| n).
Proof.
move=> p [|n] p_pr; first by case: p p_pr.
by rewrite p'natEpi // mem_primes p_pr.
Qed.

Lemma pnatPpi : forall pi n p, pi.-nat n -> p \in \pi(n) -> p \in pi.
Proof. by move=> pi n p; case/andP=> _; move/allP; exact. Qed.

Lemma pnat_dvd : forall m n pi, m %| n -> pi.-nat n -> pi.-nat m.
Proof. by move=> m n pi; case/dvdnP=> q ->; rewrite pnat_mul; case/andP. Qed.

Lemma pnat_div : forall m n pi, m %| n -> pi.-nat n -> pi.-nat (n %/ m).
Proof.
move=> m n // pi; case/dvdnP=> q ->; rewrite pnat_mul andbC; case/andP.
by case: m => // m _; rewrite mulnK.
Qed.

Lemma pnat_coprime : forall pi m n, pi.-nat m -> pi^'.-nat n -> coprime m n.
Proof.
move=> pi m n; case/andP=> m_gt0 pi_m; case/andP=> n_gt0 pi'_n.
rewrite coprime_has_primes //; apply/hasPn=> p; move/(allP pi'_n).
apply: contra; exact: allP.
Qed.

Lemma p'nat_coprime : forall pi m n, pi^'.-nat m -> pi.-nat n -> coprime m n.
Proof. by move=> pi m n pi'm pi_n; rewrite (pnat_coprime pi'm) ?pnatNK. Qed.

Lemma sub_pnat_coprime : forall pi rho m n,
  {subset rho <= pi^'} -> pi.-nat m -> rho.-nat n -> coprime m n.
Proof.
move=> pi rho m n pi'rho pi_m; move/(sub_in_pnat (in1W pi'rho)).
exact: pnat_coprime.
Qed.

Lemma coprime_partC : forall pi m n, coprime m`_pi n`_pi^'.
Proof. move=> pi m n; apply: (@pnat_coprime pi); exact: part_pnat. Qed.

Lemma pnat_1 : forall pi n, pi.-nat n -> pi^'.-nat n -> n = 1.
Proof.
by move=> pi n pi_n pi'_n; rewrite -(eqnP (pnat_coprime pi_n pi'_n)) gcdnn.
Qed.

Lemma part_pnat_id : forall pi n, pi.-nat n -> n`_pi = n.
Proof.
move=> pi n; case/andP=> n_gt0 pi_n.
rewrite -{2}(partnT n_gt0) /partn big_mkcond; apply: eq_bigr=> p _.
case: (posnP (logn p n)) => [-> |]; first by rewrite if_same.
by rewrite logn_gt0; move/(allP pi_n)=> /= ->.
Qed.

Lemma part_p'nat : forall pi n, pi^'.-nat n -> n`_pi = 1.
Proof.
move=> pi n; case/andP=> n_gt0 pi'_n; apply: big1_seq => p.
case/andP=> pi_p _; case: (posnP (logn p n)) => [-> //|].
by rewrite logn_gt0; move/(allP pi'_n); case/negP.
Qed.

Lemma partn_eq1 : forall pi n, n > 0 -> (n`_pi == 1) = pi^'.-nat n.
Proof.
move=> pi n n_gt0; apply/eqP/idP=> [pi_n_1|]; last exact: part_p'nat.
by rewrite -(partnC pi n_gt0) pi_n_1 mul1n part_pnat.
Qed.

Lemma pnatP : forall pi n,
  n > 0 -> reflect (forall p, prime p -> p %| n -> p \in pi) (pi.-nat n).
Proof.
move=> pi n n_gt0; rewrite /pnat n_gt0.
apply: (iffP allP) => /= pi_n p => [pr_p p_n|].
  by rewrite pi_n // mem_primes pr_p n_gt0.
by rewrite mem_primes n_gt0 /=; case/andP; move: p.
Qed.

Lemma pi_pnat : forall pi p n, p.-nat n -> p \in pi -> pi.-nat n.
Proof.
move=> pi p n p_n pi_p; have [n_gt0 _] := andP p_n.
by apply/pnatP=> // q q_pr; move/(pnatP _ n_gt0 p_n _ q_pr); move/eqnP->.
Qed.

Lemma p_natP : forall p n, p.-nat n -> {k | n = p ^ k}.
Proof. by move=> p n p_n; exists (logn p n); rewrite -p_part part_pnat_id. Qed.

Lemma pi'_p'nat : forall pi p n, pi^'.-nat n -> p \in pi -> p^'.-nat n.
Proof.
move=> pi p n pi'n pi_p; apply: sub_in_pnat pi'n => q _.
by apply: contraNneq => ->.
Qed.
 
Lemma pi_p'nat : forall pi p n, pi.-nat n -> p \in pi^' -> p^'.-nat n.
Proof. by move=> pi p n pi_n; apply: pi'_p'nat; rewrite pnatNK. Qed.
 
Lemma partn_part : forall pi rho n,
  {subset pi <= rho} -> n`_rho`_pi = n`_pi.
Proof.
move=> pi rho n pi_sub_rho.
case: (posnP n) => [-> | n_gt0]; first by rewrite !partn0 partn1.
rewrite -{2}(partnC rho n_gt0) partn_mul //.
suff: pi^'.-nat n`_rho^' by move/part_p'nat->; rewrite muln1.
apply: sub_in_pnat (part_pnat _ _) => q _; apply: contra; exact: pi_sub_rho.
Qed.

Lemma partnI : forall pi rho n, n`_[predI pi & rho] = n`_pi`_rho.
Proof.
move=> pi rho n; rewrite -(@partnC [predI pi & rho] _`_rho) //.
symmetry; rewrite 2?partn_part; try by move=> p; case/andP.
rewrite mulnC part_p'nat ?mul1n // pnatNK pnatI part_pnat andbT.
exact: pnat_dvd (dvdn_part _ _) (part_pnat _ _).
Qed.

Lemma odd_2'nat : forall n, odd n = 2^'.-nat n.
Proof. by case=> // n; rewrite p'natE // dvdn2 negbK. Qed.

End PiNat.

(************************************)
(* Properties of the divisors list. *)
(************************************)

Lemma divisors_correct : forall n, n > 0 ->
  [/\ uniq (divisors n), sorted leq (divisors n)
    & forall d, (d \in divisors n) = (d %| n)].
Proof.
move=> n; move/prod_prime_decomp=> def_n; rewrite {4}def_n {def_n}.
have: all prime (primes n) by apply/allP=> p; rewrite mem_primes; case/andP.
have:= primes_uniq n; rewrite /primes /divisors; move/prime_decomp: n.
elim=> [|[p e] pd] /=; first by split=> // d; rewrite big_nil dvdn1 mem_seq1.
rewrite big_cons /=; move: (foldr _ _ pd) => divs IHpd.
case/andP=> npd_p Upd; case/andP=> pr_p pr_pd.
have lt0p: 0 < p by exact: prime_gt0.
case: {IHpd Upd}(IHpd Upd pr_pd) => Udivs Odivs mem_divs.
have ndivs_p: p * _ \notin divs.
  move=> m; suff: p \notin divs; rewrite !mem_divs.
    by apply: contra; case/dvdnP=> n ->; rewrite mulnCA dvdn_mulr.
  have ndv_p_1: ~~(p %| 1) by rewrite dvdn1 neq_ltn orbC prime_gt1.
  rewrite big_cond_seq /=; apply big_prop => [//|u v npu npv|[q f] /= pd_qf].
    by rewrite euclid //; apply/norP.
  elim: (f) => // f'; rewrite expnS euclid // orbC negb_or => -> {f'}/=.
  have pd_q: q \in unzip1 pd by apply/mapP; exists (q, f).
  by apply: contra npd_p; rewrite dvdn_prime2 // ?(allP pr_pd) //; move/eqP->.
elim: e => [|e] /=; first by split=> // d; rewrite mul1n.
have Tmulp_inj: injective (NatTrec.mul p).
  by move=> u v; move/eqP; rewrite !natTrecE eqn_pmul2l //; move/eqP.
move: (iter e _ _) => divs' [Udivs' Odivs' mem_divs']; split=> [||d].
- rewrite merge_uniq cat_uniq map_inj_uniq // Udivs Udivs' andbT /=.
  apply/hasP=> [[d dv_d]]; case/mapP=> d' _ def_d; case/idPn: dv_d.
  by rewrite def_d natTrecE.
- rewrite (sorted_merge leq_total) //; case: (divs') Odivs' => //= d ds.
  rewrite (@path_map _ _ _ _ leq xpred0) ?has_pred0 // => u v _.
  by rewrite !natTrecE leq_pmul2l.
rewrite mem_merge mem_cat; case dv_d_p: (p %| d).
  case/dvdnP: dv_d_p => d' ->{d}; rewrite mulnC (negbTE (ndivs_p d')) orbF.
  rewrite expnS -mulnA dvdn_pmul2l // -mem_divs'.
  by rewrite -(mem_map Tmulp_inj divs') natTrecE.
case pdiv_d: (_ \in _).
  by case/mapP: pdiv_d dv_d_p => d' _ ->; rewrite natTrecE dvdn_mulr.
by rewrite mem_divs gauss // coprime_sym coprime_expl ?prime_coprime ?dv_d_p.
Qed.

Lemma sorted_divisors : forall n, sorted leq (divisors n).
Proof. by move=> n; case: (posnP n) => [-> //|]; case/divisors_correct. Qed.

Lemma divisors_uniq : forall n, uniq (divisors n).
Proof. by move=> n; case: (posnP n) => [-> //|]; case/divisors_correct. Qed.

Lemma sorted_divisors_ltn : forall n, sorted ltn (divisors n).
Proof.
by move=> n; rewrite sorted_ltn_uniq_leq divisors_uniq sorted_divisors.
Qed.

Lemma dvdn_divisors : forall d m, 0 < m -> (d %| m) = (d \in divisors m).
Proof. by move=> d m; case/divisors_correct. Qed.

Lemma divisor1 : forall n, 1 \in divisors n.
Proof. by case=> // n; rewrite -dvdn_divisors // dvd1n. Qed.

Lemma divisorn : forall n, 0 < n -> n \in divisors n.
Proof. by move=> n n_gt0; rewrite -dvdn_divisors. Qed.

(* Big sum / product lemmas*)

Lemma dvdn_sum : forall d I r (K : pred I) F,
  (forall i, K i -> d %| F i) -> d %| \sum_(i <- r | K i) F i.
Proof. move=> I r K F d dF; apply big_prop => //; exact: dvdn_add. Qed.

Lemma dvdn_partP : forall n m : nat, 0 < n ->
  reflect (forall p, p \in \pi(n) -> n`_p %| m) (n %| m).
Proof.
move=> n m n_gt0; apply: (iffP idP) => n_dvd_m => [p _|].
  apply: dvdn_trans n_dvd_m; exact: dvdn_part.
case: (posnP m) => [-> // | m_gt0].
rewrite -(partnT n_gt0) -(partnT m_gt0).
rewrite !(@widen_partn (m + n)) ?leq_addl ?leq_addr // /in_mem /=.
apply (big_rel (fun n m => n %| m)) => // [*|q _]; first exact: dvdn_mul.
case: (posnP (logn q n)) => [-> // | ]; rewrite logn_gt0 => q_n.
have pr_q: prime q by move: q_n; rewrite mem_primes; case/andP.
by have:= n_dvd_m q q_n; rewrite p_part !pfactor_dvdn // pfactorK.
Qed.

Lemma modn_partP : forall n a b : nat, 0 < n ->
  reflect (forall p : nat, p \in \pi(n) -> a = b %[mod n`_p]) (a == b %[mod n]).
Proof.
move=> n a b n_gt0; wlog le_b_a: a b / b <= a.
  move=> IH; case: (leqP b a); last move/ltnW; move/IH => {IH}// IH.
  by rewrite eq_sym; apply: (iffP IH) => eqab p; move/eqab.
rewrite eqn_mod_dvd //; apply: (iffP (dvdn_partP _ n_gt0)) => eqab p;
  by move/eqab; rewrite -eqn_mod_dvd //; move/eqP.   
Qed.

(* The Euler phi function *)

Lemma phiE : forall n,
  n > 0 -> phi n = \prod_(p <- primes n) (p.-1 * p ^ (logn p n).-1).
Proof.
move=> n n_gt0; rewrite /phi n_gt0 prime_decompE unlock.
by elim: (primes n) => //= [p pr ->]; rewrite !natTrecE.
Qed.

Lemma phi_gt0 : forall n, (0 < phi n) = (0 < n).
Proof.
case=> // n; rewrite phiE // big_cond_seq prodn_cond_gt0 // => p.
by rewrite mem_primes muln_gt0 expn_gt0; case: p => [|[|]].
Qed.

Lemma phi_pfactor : forall p e,
  prime p -> e > 0 -> phi (p ^ e) = p.-1 * p ^ e.-1.
Proof.
move=> p e pr_p e_gt0; rewrite phiE ?expn_gt0 ?prime_gt0 //.
by rewrite primes_exp // primes_prime // unlock /= muln1 pfactorK.
Qed.

Lemma phi_coprime : forall m n,
  coprime m n -> phi (m * n) = phi m * phi n.
Proof.
move=> m n co_mn; case: (posnP m) => [-> //| m_gt0].
case: (posnP n) => [->|n_gt0]; first by rewrite !muln0.
rewrite !phiE ?muln_gt0 ?m_gt0 //.
have: perm_eq (primes (m * n)) (primes m ++ primes n).
  apply: uniq_perm_eq => [||p]; first exact: primes_uniq.
    by rewrite cat_uniq !primes_uniq -coprime_has_primes // co_mn.
  by rewrite mem_cat primes_mul.
move/(eq_big_perm _)->; rewrite big_cat /= !(big_cond_seq xpredT) /=.
congr (_ * _); apply: eq_bigr => p; rewrite mem_primes; case/and3P=> _ _ dvp.
  rewrite (mulnC m) logn_gauss //; move: co_mn.
  by rewrite -(divnK dvp) coprime_mull; case/andP.
rewrite logn_gauss //; move: co_mn.
by rewrite coprime_sym -(divnK dvp) coprime_mull; case/andP.
Qed.

Lemma phi_count_coprime : forall n, phi n = \sum_(0 <= d < n | coprime n d) 1.
Proof.
move=> n; elim: {n}_.+1 {-2}n (ltnSn n) => // m IHm n; rewrite ltnS => le_n_m.
case: (leqP n 1) => [|lt1n]; first by rewrite unlock; case: (n) => [|[]].
pose p := pdiv n; have pr_p: prime p by exact: pdiv_prime.
have p1 := prime_gt1 pr_p; have p0 := ltnW p1.
pose np := n`_p; pose np' := n`_p^'.
have co_npp' : coprime np np' by rewrite coprime_partC.
have [n0 np0 np'0]: [/\ n > 0, np > 0 & np' > 0] by rewrite ltnW ?part_gt0.
have def_n: n = np * np' by rewrite partnC.
have lnp0: 0 < logn p n by rewrite lognE pr_p n0 pdiv_dvd.
pose in_mod k (k0 : k > 0) d := Ordinal (ltn_pmod d k0).
rewrite {1}def_n phi_coprime // {IHm}(IHm np') ?big_mkord; last first.
  apply: leq_trans le_n_m; rewrite def_n ltn_Pmull //.
  by rewrite /np p_part -(expn0 p) ltn_exp2l.
have ->: phi np = #|[pred d : 'I_np | coprime np d]|.
  rewrite {1}[np]p_part phi_pfactor //=; set q := p ^ _.
  apply: (@addnI (1 * q)); rewrite -muln_addl [1 + _]prednK // mul1n.
  have def_np: np = p * q by rewrite -expnS prednK // -p_part.
  pose mulp := [fun d : 'I_q => in_mod _ np0 (p * d)].
  rewrite -def_np -{1}[np]card_ord -(cardC [image mulp of predT]).
  rewrite card_in_image => [|[d1 ltd1] [d2 ltd2] /= _ _ []]; last first.
    move/eqP; rewrite def_np !modn_pmul2l ?modn_small //.
    by rewrite eqn_pmul2l // => eq_op12; exact/eqP.
  rewrite card_ord; congr (q + _); apply: eq_card => d /=.
  rewrite !inE /= {6}[np]p_part coprime_pexpl ?prime_coprime //; congr (~~ _).
  apply/imageP/idP=> [[d' _ -> /=]|].
    by rewrite def_np modn_pmul2l // dvdn_mulr.
  case/dvdnP=> r; rewrite mulnC; case: d => d ltd /= def_d.
  have ltr: r < q by rewrite -(ltn_pmul2l p0) -def_np -def_d.
  by exists (Ordinal ltr) => //; apply: val_inj; rewrite /= -def_d modn_small.
pose h (d : 'I_n) := (in_mod _ np0 d, in_mod _ np'0 d).
pose h' (d : 'I_np * 'I_np') := in_mod _ n0 (chinese np np' d.1 d.2).
rewrite -sum_nat_const pair_big (reindex_onto h h') => [|[d d'] _].
  apply: eq_bigl => [[d ltd] /=]; rewrite !inE /= -val_eqE /= andbC.
  rewrite !coprime_modr def_n -chinese_modlr // -coprime_mull -def_n.
  by rewrite modn_small ?eqxx.
apply/eqP; rewrite /eq_op /= /eq_op /= !modn_dvdm ?dvdn_part //.
by rewrite chinese_modl // chinese_modr // !modn_small ?eqxx ?ltn_ord.
Qed.




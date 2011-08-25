(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import bigop ssralg poly choice.

(******************************************************************************)
(* This file provides a library for pseudo division on univariate             *)
(* polynomials over ring structures; it also provides an extended theory      *)
(* for polynomials whose coefficients range over commutative rings and        *)
(* integral domains.                                                          *)
(*                                                                            *)
(*  We define pseudo division on polynomials over an integral domain :        *)
(*             m %/ d == the pseudo-quotient                                  *)
(*             m %% d == the pseudo remainder                                 *)
(*          scalp m d == the exponnent of the correcting coefficient          *)
(*             p %| q <=> q is a pseudo-divisor of p                          *)
(*             p %= q <=> p and q are equal up to a non-zero scalar factor    *)
(*                    := (p %| q) && (q %| p)                                 *)
(*                   *** If R is a field, this means p and q are associate.   *)
(*           gcdp p q == pseudo-gcd of p and q. This is defined for p and q   *)
(*                       with coefficients in an arbitrary ring; however gcdp *)
(*                       is only known to be idempotent and  associative when *)
(*                       R has an integral domain (idomainType) structure.    *)
(*       coprime p q <=> gcdp p q %= 1                                        *)
(*          gdcop q p == greatest pseudo divisor of p which is coprime with q *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "p %= q" (at level 70, no associativity).

Local Notation simp := Monoid.simpm.

Section PolyDivRing.

Variable R : ringType.
Implicit Types p q : {poly R}.

(* Pseudo division, defined on an arbitrary ring *)
Definition edivp_rec (q : {poly R})  :=
  let sq := size q in
  let cq := lead_coef q in
  fix loop (n : nat) (k : nat) (qq r : {poly R}) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := (lead_coef r)%:P * 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    if n is n1.+1 then loop n1 k.+1 qq1 r1 else (k.+1, qq1, r1).

Definition edivp (p q : {poly R}) : nat * {poly R} * {poly R} :=
  if q == 0 then (0%N, 0, p) else edivp_rec q (size p) 0 0 p.

CoInductive edivp_spec (m d : {poly R}) : nat * {poly R} * {poly R} -> Type :=
  EdivnSpec k (q r: {poly R}) of
   (GRing.comm d (lead_coef d)%:P -> m * (lead_coef d ^+ k)%:P = q * d + r) &
   (d != 0 -> size r < size d) : edivp_spec m d (k, q, r).

Lemma edivpP : forall m d, edivp_spec m d (edivp m d).
Proof.
rewrite /edivp => m d; case: (altP (d =P 0))=> [->| Hd].
  by constructor; rewrite !(simp, eqxx).
have: GRing.comm d (lead_coef d)%:P -> m * (lead_coef d ^+ 0)%:P = 0 * d + m.
  by rewrite !simp.
elim: (size m) 0%N 0 {1 4 7}m (leqnn (size m))=>
   [|n IHn] k q r Hr /=.
  have->: r = 0 by apply/eqP; rewrite -size_poly_eq0; move: Hr; case: size.
  suff F3: size (0: {poly R}) < size d by rewrite F3=> /= Hr1; constructor.
  by rewrite size_polyC eqxx (polySpred Hd).
case: ltP=> Hlt Heq; first by constructor=> // Hq; apply/ltP.
apply: IHn=> [|Cda]; last first.
  by rewrite mulr_addl addrAC -addrA subrK exprSr polyC_mul
             mulrA Heq // mulr_addl -mulrA Cda mulrA.
apply: leq_size_coef => j Hj.
rewrite  coefD coefN -!mulrA coefMC coefCM coefXnM.
move/ltP: Hlt; rewrite -leqNgt=> Hlt.
move: Hj; rewrite leq_eqVlt; case/predU1P => [<-{j} | Hj]; last first.
  rewrite nth_default ?(leq_trans Hqq) // ?simp; last by apply: (leq_trans Hr).
  rewrite nth_default; first by rewrite if_same !simp oppr0.
  by rewrite -{1}(subKn Hlt) leq_sub2r // (leq_trans Hr).
move: Hr; rewrite leq_eqVlt ltnS; case/predU1P=> Hqq; last first.
  rewrite !nth_default ?if_same ?simp ?oppr0 //.
  by rewrite -{1}(subKn Hlt) leq_sub2r // (leq_trans Hqq).
rewrite {2}/lead_coef Hqq polySpred // subSS ltnNge leq_subr /=.
by rewrite subKn ?addrN // -subn1 leq_sub_add add1n -Hqq.
Qed.

Lemma edivp_eq : forall d q r: {poly R},
  GRing.comm d (lead_coef d)%:P -> GRing.rreg (lead_coef d) -> size r < size d ->
  let k := (edivp (q * d + r) d).1.1 in
  let c := (lead_coef d ^+ k)%:P in
  edivp (q * d + r) d = (k, q * c, r * c).
Proof.
move=> d q r Cdl Rreg lt_rd.
case: edivpP=> k q1 r1; move/(_ Cdl)=> Heq.
have: d != 0.
  by case: (size d) lt_rd (size_poly_eq0 d) => // n _ <-.
move=> H; move/(_ H)=> Hs.
have F: q * d * (lead_coef d ^+ k)%:P = q * (lead_coef d ^+ k)%:P * d.
  by rewrite -mulrA polyC_exp (GRing.commr_exp k Cdl) mulrA.
suff F1: q1 = q * (lead_coef d ^+ k)%:P.
  congr (_,_,_)=> //.
  by apply: (@addrI _ (q1 * d)); rewrite {2}F1 -F -mulr_addl.
apply/eqP; rewrite -subr_eq0.
have : (q1 - q * (lead_coef d ^+ k)%:P) * d = r * (lead_coef d ^+ k)%:P - r1.
  apply: (@addIr _ r1); rewrite subrK.
  apply: (@addrI _  ((q * (lead_coef d ^+ k)%:P) * d)).
  by rewrite mulr_addl mulNr !addrA [_ + (q1 * d)]addrC addrK -F -mulr_addl.
move/eqP; rewrite -[_ == _ - _]subr_eq0 rreg_div0 //; first by case/andP.
rewrite size_opp; apply: (leq_ltn_trans (size_add _ _)).
rewrite size_opp ltnNge leq_maxr negb_or -!ltnNge Hs andbT.
apply: (leq_ltn_trans (size_mul _ _)).
rewrite size_polyC; case: (_ == _); last by rewrite addnS addn0.
by rewrite addn0; apply: leq_ltn_trans lt_rd; case: size.
Qed.

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.
Definition dvdp p q := modp q p == 0.

Local Notation "m %/ d" := (divp m d) : ring_scope.
Local Notation "m %% d" := (modp m d) : ring_scope.
Local Notation "p %| q" := (dvdp p q) : ring_scope.

Lemma divp_size : forall p q, size p < size q -> p %/ q = 0.
Proof.
move=> p q; rewrite /divp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs.
Qed.

Lemma modp_size : forall p q, size p < size q -> p %% q = p.
Proof.
move=> p q; rewrite /modp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs /=.
Qed.

(* Todo : this is no spec, add _comm in the name *)
Lemma divp_spec :
  forall p q, GRing.comm q (lead_coef q)%:P ->
  p * (lead_coef q ^+ scalp p q)%:P = p %/ q * q + p %% q.
Proof.
move=> p q Cq.
rewrite /divp /modp /scalp; case: edivpP=> k q1 r1 Hc _; exact: Hc.
Qed.

Lemma divp_mon_spec : forall p q, monic q-> p = p %/ q * q + p %% q.
Proof.
move=> p q Hm; have Hp: lead_coef q = 1 by apply/eqP.
rewrite -divp_spec Hp ?(exp1rn,simp) //.
by exact: commr1.
Qed.

(* rename to ltn_psize_mod, add ltn_size_mod and leq_size_mod *)
Lemma modp_spec : forall p q, q != 0 -> size (p %% q) < size q.
Proof.
move=> p q Hq.
rewrite /divp /modp /scalp; case: edivpP=> k q1 r1 _ Hc; exact: Hc.
Qed.

Lemma div0p : forall p, 0 %/ p = 0.
Proof.
move=> p; rewrite /divp /edivp; case: ifP => // Hp.
by rewrite /edivp_rec !size_poly0 polySpred ?Hp.
Qed.

Lemma modp0 : forall p, p %% 0 = p.
Proof. by rewrite /modp /edivp eqxx. Qed.

Lemma mod0p : forall p, 0 %% p = 0.
Proof.
move=> p; rewrite /modp /edivp; case: ifP => // Hp.
by rewrite /edivp_rec !size_poly0 polySpred ?Hp.
Qed.

Lemma dvd0p : forall p, 0 %| p = (p == 0).
Proof. by move=> p; rewrite /dvdp modp0. Qed.

Lemma dvdp0 : forall p, p %| 0.
Proof. move=> p; apply/eqP; exact: mod0p. Qed.

Lemma dvdpn0 : forall p q, p %| q -> q != 0 -> p != 0.
Proof. by move=> p q pq hq; apply: contraL pq=> /eqP ->; rewrite dvd0p. Qed.

(* Todo : rewrite this *)
Lemma comm_dvdpP : forall p q, GRing.comm q (lead_coef q)%:P -> GRing.rreg (lead_coef q) ->
  reflect (exists nq: nat * {poly R}, p * ((lead_coef q)^+nq.1)%:P= nq.2 * q)
          (q %| p).
Proof.
move=> p q; set lq := lead_coef q; move=> Cq Rq; apply: (iffP idP).
  rewrite /dvdp; move/eqP=> Dqp.
  by exists (scalp p q, p %/ q); rewrite {1}divp_spec // Dqp !simp.
move=> [[k q1] /= Hq].
have Hnq0 := rreg_lead0 Rq.
pose v := scalp p q; pose m := maxn v k.
rewrite /dvdp -(rreg_scale0 _ (@rregX _ _ (m - v) Rq)).
suff:
 (p %/ q * (lq ^+ (m - v))%:P  - q1 * (lq ^+ (m - k))%:P) * q +
  p %% q * (lq ^+ (m - v))%:P  == 0.
  rewrite rreg_div0 //; first by case/andP.
  by rewrite rreg_size ?modp_spec //; apply rregX.
rewrite mulr_addl addrAC mulNr -!mulrA.
rewrite  polyC_exp -(GRing.commr_exp (m-v) Cq) -polyC_exp.
rewrite mulrA -mulr_addl -divp_spec //.
rewrite  [(_ ^+ (m - k))%:P]polyC_exp -(GRing.commr_exp (m-k) Cq) -polyC_exp.
rewrite mulrA -Hq -!mulrA -!polyC_mul -/v -!exprn_addr addnC subnK.
  by rewrite addnC subnK ?subrr // leq_maxr leqnn orbT.
by rewrite leq_maxr leqnn.
Qed.

Lemma dvdMpP : forall p q, monic q -> reflect (exists qq, p = qq * q) (q %| p).
Proof.
move=> p q Hm; case: (monic_comreg Hm)=> Hc Hr.
apply: (iffP (comm_dvdpP _ Hc Hr)); move: Hm; rewrite /monic; move/eqP->.
  by case=> [[n x]]; rewrite /= exp1rn mulr1 => ->; exists x.
by case=> x ->; exists (0%N,x); rewrite exp1rn mulr1.
Qed.

Lemma divp_mon_eq : forall d q r: {poly R}, monic d -> size r < size d ->
  (q * d + r) %/ d = q.
Proof.
move=> d q r Hm Hd; case: (monic_comreg Hm)=> Hc Hr.
rewrite /divp edivp_eq //.
move: Hm; rewrite /monic; move/eqP->.
by rewrite exp1rn mulr1 //.
Qed.

Lemma modMp_eq : forall d q r: {poly R}, monic d -> size r < size d ->
  (q * d + r) %% d = r.
Proof.
move=> d q r Hm Hd; case: (monic_comreg Hm)=> Hc Hr.
rewrite /modp edivp_eq //.
move: Hm; rewrite /monic; move/eqP->.
by rewrite exp1rn !mulr1.
Qed.

Lemma size_dvdMp_leqif : forall p q : {poly R},
    monic p -> p %| q -> q != 0 ->
  size p <= size q ?= iff (q == lead_coef q *: p).
Proof.
move=> p q0 mon_p; case: (monic_comreg mon_p)=> HC HR.
case/comm_dvdpP=> // [[k q]] /=.
move: (mon_p); rewrite /monic; move/eqP->; rewrite exp1rn simp=> ->{q0}.
case: (eqVneq q 0) => [-> | nz_q _]; first by rewrite mul0r eqxx.
have q_gt0: size q > 0 by rewrite lt0n size_poly_eq0.
split; first by rewrite size_mul_monic // -(prednK q_gt0) leq_addl.
rewrite lead_coef_mul_monic // -mul_polyC.
apply/idP/eqP=> [|->]; last first.
  by rewrite size_mul_monic // -?size_poly_eq0 size_polyC lead_coef_eq0 nz_q.
rewrite size_mul_monic // eqn_leq; case/andP=> _.
rewrite -subn1 leq_sub_add leq_add2r => le_q_1; congr (_ * _).
by rewrite {1}(size1_polyC le_q_1) lead_coefE -subn1 ((_ - 1 =P 0)%N _).
Qed.

Lemma modpC : forall p c, c != 0 -> p %% c%:P = 0.
Proof.
move=> p c Hc; apply/eqP; rewrite -size_poly_eq0 -leqn0 -ltnS.
by apply: leq_trans (modp_spec _ _) _; rewrite ?polyC_eq0 // size_polyC Hc.
Qed.

Lemma modp1 : forall p, p %% 1 = 0.
Proof. move=> p; apply: modpC; exact: nonzero1r. Qed.

Lemma divp1 : forall p, p %/ 1 = p.
Proof.
move=> p; case: (monic_comreg (monic1 R))=> [Hc Hr].
by move: (divp_spec p Hc); rewrite lead_coef1 exp1rn modp1 !simp.
Qed.

Lemma dvd1p : forall p, 1 %| p.
Proof. move=> p; apply/eqP; exact: modp1. Qed.

Lemma rreg_dvdp_mull : forall p q,
  GRing.comm q (lead_coef q)%:P -> GRing.rreg (lead_coef q) -> q %| p * q.
Proof.
by move=> p q Cq Rq; apply/comm_dvdpP=> //; exists (0%N,p); rewrite expr0 simp.
Qed.

Lemma monic_divp_mull : forall p q, monic q -> p * q %/ q = p.
Proof.
move=> p q Mq.
by rewrite -[p*q]addr0 divp_mon_eq // size_polyC eqxx polySpred // monic_neq0.
Qed.

Lemma monic_modp_add : forall p q m, monic m -> (p + q) %% m = p %% m + q %% m.
Proof.
move=> p q m Hmon.
rewrite {1}(divp_mon_spec p Hmon) {1}(divp_mon_spec q Hmon).
rewrite addrCA 2!addrA -mulr_addl (addrC (q %/ m)) -addrA modMp_eq //.
apply: (leq_ltn_trans (size_add _ _)).
wlog hyp : / size (p %% m) <= size (q %% m).
  case/orP: (orbN (size (p %% m) <= size (q %% m))) => [?|]; first by apply.
  rewrite -ltnNge => sz hyp.
  rewrite maxnl; by [apply modp_spec, monic_neq0 | apply ltnW].
rewrite maxnr //; by apply modp_spec, monic_neq0.
Qed.

Lemma monic_modp_mulmr : forall p q m, monic m -> (p * (q %% m)) %% m = (p * q) %% m.
Proof.
move=> p q m mon.
have -> : q %% m = q - q %/ m * m by rewrite {2}(divp_mon_spec q mon) -addrA addrC subrK.
rewrite mulr_addr monic_modp_add // -mulNr mulrA.
rewrite -{2}[_ %% _]addr0; congr (_ + _).
by apply/eqP; apply: rreg_dvdp_mull; case: (monic_comreg mon).
Qed.

Lemma dvdp_factorl : forall p x, ('X - x%:P %| p) = root p x.
Proof.
move=> p x; have [HcX Hr] := (monic_comreg (monic_factor x)).
apply/comm_dvdpP/factor_theorem=> //; last first.
  by case=> p1 ->; exists (0%N,p1); rewrite expr0 simp.
move: (monic_factor x); rewrite /monic; move/eqP->.
by case=> [[k1 p1]]; rewrite exp1rn simp=> ->; exists p1.
Qed.

Lemma factorP : forall p x, reflect (p.[x] = 0) ('X - x%:P %| p).
Proof. by move=> p x; apply: (iffP idP); rewrite dvdp_factorl; move/rootP. Qed.

Lemma root_factor_theorem : forall p x, root p x = ('X - x%:P %| p).
Proof. by move=> *; rewrite dvdp_factorl. Qed.

(* Pseudo gcd *)
Definition gcdp p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := pp %% qq in
      if rr == 0 then qq else
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.

Lemma gcd0p : left_id 0 gcdp.
Proof.
move=> p; rewrite /gcdp size_poly0 lt0n size_poly_eq0 if_neg.
case: ifP => /= [_ | nzp]; first by rewrite eqxx.
by rewrite polySpred !(modp0, nzp) //; case: _.-1 => [|m]; rewrite mod0p eqxx.
Qed.

Lemma gcdp0 : right_id 0 gcdp.
Proof.
move=> p; have:= gcd0p p; rewrite /gcdp size_poly0 lt0n size_poly_eq0 if_neg.
by case: ifP => /= p0; rewrite ?(eqxx, p0) // (eqP p0).
Qed.

Lemma gcdpE : forall p q,
  gcdp p q = if size p < size q then gcdp (q %% p) p else gcdp (p %% q) q.
Proof.
pose gcdp_rec := fix gcdp_rec (n : nat) (pp qq : {poly R}) {struct n} :=
   let rr := pp %% qq in
   if rr == 0 then qq else
   if n is n1.+1 then gcdp_rec n1 qq rr else rr.
have Irec: forall m n p q, size q <= m -> size q <= n
      -> size q < size p -> gcdp_rec m p q = gcdp_rec n p q.
+ elim=> [|m Hrec] [|n] //= p q.
  - rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
    rewrite size_poly0 lt0n size_poly_eq0 modp0 => nzp.
    by rewrite (negPf nzp); case: n => [|n] /=; rewrite mod0p eqxx.
  - rewrite leqn0 size_poly_eq0 => _; move/eqP=> ->.
    rewrite size_poly0 lt0n size_poly_eq0 modp0 => nzp.
    by rewrite (negPf nzp); case: m {Hrec} => [|m] /=; rewrite mod0p eqxx.
  case: ifP => Epq Sm Sn Sq //; rewrite ?Epq //.
  case: (eqVneq q 0) => [->|nzq].
    by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite mod0p eqxx.
  apply: Hrec; last exact: modp_spec.
    by rewrite -ltnS (leq_trans _ Sm) // modp_spec.
  by rewrite -ltnS (leq_trans _ Sn) // modp_spec.
move=> p q; case: (eqVneq p 0) => [-> | nzp].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
case: (eqVneq q 0) => [-> | nzq].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
rewrite /gcdp -/gcdp_rec.
case: ltnP; rewrite (negPf nzp, negPf nzq) //=.
  move=> ltpq; rewrite modp_spec (negPf nzp) //=.
  rewrite -(ltn_predK ltpq) /=; case: eqP => [->|].
    by case: (size p) => [|[|s]]; rewrite /= modp0 (negPf nzp) // mod0p eqxx.
  move/eqP=> nzqp; apply: Irec => //; last exact: modp_spec.
    by rewrite -ltnS (ltn_predK ltpq) (leq_trans _ ltpq) ?leqW // modp_spec.
  by rewrite ltnW // modp_spec.
move=> leqp; rewrite modp_spec (negPf nzq) //=.
have p_gt0: size p > 0 by rewrite lt0n size_poly_eq0.
rewrite -(prednK p_gt0) /=; case: eqP => [->|].
  by case: (size q) => [|[|s]]; rewrite /= modp0 (negPf nzq) // mod0p eqxx.
move/eqP=> nzpq; apply: Irec => //; last exact: modp_spec.
  by rewrite -ltnS (prednK p_gt0) (leq_trans _ leqp) // modp_spec.
by rewrite ltnW // modp_spec.
Qed.

Definition coprimep p q := size (gcdp p q) == 1%N.


(* Equality up to a constant factor; this is only used when R is integral *)
Definition eqp p q :=  (p %| q) && (q %| p).
Notation "p %= q" := (eqp p q) : ring_scope.

End PolyDivRing.

Notation "m %/ d" := (divp m d) : ring_scope.
Notation "m %% d" := (modp m d) : ring_scope.
Notation "p %| q" := (dvdp p q) : ring_scope.
Notation "p %= q" := (eqp p q) : ring_scope.

Section PolyDivUnit.

Variable R : unitRingType.
Implicit Type p : {poly R}.

Lemma uniq_roots_dvd : forall p rs,
  all (root p) rs -> uniq_roots rs ->
  \prod_(z <- rs) ('X - z%:P) %| p.
Proof.
move=> p rs rrs; case/(uniq_roots_factors rrs)=> q ->.
apply/comm_dvdpP; rewrite (monicP (monic_prod_factors _)); first exact: commr1.
 exact: rreg1.
by exists (0%N, q)=> /=; rewrite expr0 polyC1 mulr1.
Qed.

End PolyDivUnit.

Section PolyDivCom.

Variable R : comRingType.
Implicit Type p q : {poly R}.

(* Pseudo-division in a commutative setting *)
(* This is no spec *)
Lemma divCp_spec : forall p q,
 lead_coef q ^+ scalp p q *: p = p %/ q * q + p %% q.
Proof.
move=> p q; rewrite -divp_spec; last by exact: mulrC.
by rewrite mulrC -mul_polyC.
Qed.

End PolyDivCom.

Section PolyDivIDomain.

Variable R : idomainType.
Implicit Type p q : {poly R}.

Lemma scalp_Ineq0 : forall p q, lead_coef q ^+ scalp p q != 0.
Proof.
move=> p q; case: (eqVneq q 0) => [->|nzq].
  by rewrite /scalp /edivp eqxx nonzero1r.
by rewrite expf_neq0 ?lead_coef_eq0.
Qed.

Lemma modIp_mull : forall p q, p * q %% q = 0.
Proof.
move=> p q; case: (q =P 0)=> Hq; first by rewrite Hq simp mod0p.
apply/eqP; apply: rreg_dvdp_mull; first by exact: mulrC.
by apply/rregP; apply/negP; rewrite lead_coef_eq0; apply/negP; apply/eqP.
Qed.

Lemma modpp : forall p, p %% p = 0.
Proof. by move=> p; rewrite -{1}(mul1r p) modIp_mull. Qed.

Lemma dvdpp : forall p, p %| p.
Proof. move=> p; apply/eqP; exact: modpp. Qed.

Lemma divp_mull : forall p q, q != 0 ->
  p * q %/ q = lead_coef q ^+ scalp (p * q) q *: p.
Proof.
by move=> p q /rregP; apply; rewrite -scaler_mull divCp_spec modIp_mull addr0.
Qed.

(******************************************************************)
(* Todo : rename & change *)
Lemma dvdpPc : forall p q,
  reflect (exists c, exists qq, c != 0 /\ c *: p = qq * q) (q %| p).
Proof.
move=> /= p q; apply: (iffP idP) => [|[c [qq [nz_c def_qq]]]].
  move/(p %% q =P 0) => dv_qp.
 exists (lead_coef q ^+ scalp p q); exists (p %/ q).
  by rewrite scalp_Ineq0 divCp_spec dv_qp !simp.
have Ecc: c%:P != 0 by rewrite polyC_eq0.
case: (eqVneq p 0) => [->|nz_p]; first by rewrite dvdp0.
pose p1 : {poly R} := lead_coef q ^+ scalp p q  *: qq - c *: (p %/ q).
have E1: c *: (p %% q) = p1 * q.
  rewrite mulr_addl {1}mulNr -scaler_mull -def_qq.
  rewrite scalerA mulrC -scalerA -scaler_mull -scaler_subr.
  by rewrite divCp_spec addrC addKr.
rewrite /dvdp; apply/idPn=> m_nz.
have: p1 * q != 0 by rewrite -E1 -mul_polyC mulf_neq0.
rewrite mulf_eq0; case/norP=> p1_nz q_nz; have:= modp_spec p q_nz.
rewrite -(size_scaler _ nz_c) E1 size_mul_id //.
by rewrite polySpred // ltnNge leq_addl.
Qed.

(* Todo : rename & change *)
Lemma dvdpP : forall p q,
   ((lead_coef q) ^+ (scalp p q) *: p == (p %/ q) * q) =  (q %| p).
Proof.
move=> /= p q; rewrite -mul_polyC mulrC.
rewrite divp_spec ?modp_dvd_eq0 /GRing.comm mulrC //.
by rewrite (can2_eq (@addKr _ _) (@addNKr _ _)) addNr.
Qed.


(* Todo : rename & change *)
Lemma dvd_factorP : forall p c,
  (p == (p %/ ('X - c%:P)) * ('X - c%:P)) = ('X - c%:P %| p).
Proof. by move=> p c; rewrite -dvdpP lead_coef_factor exp1rn scale1r. Qed.

(* Todo : remove, replace by modp_eq0 *)
Lemma modp_dvd_eq0 : forall p q, (q %| p) = (p %% q == 0).
Proof. by []. Qed.

(******************************************************************)

Lemma modp_eq0 : forall p q, (p %% q == 0) = (q %| p). Proof. by []. Qed.

Lemma modp_dvd : forall p q, (q %| p) -> p %% q = 0.
Proof. by move=> *; apply/eqP. Qed.

Lemma size_dvdp : forall p q, q != 0 -> p %| q -> size p <= size q.
Proof.
move=> p q Eq; case/dvdpPc => c1 [q1 [Ec1 Ec1q]].
have: q1 * p != 0 by  rewrite -Ec1q -!size_poly_eq0 size_scaler in Eq *.
rewrite mulf_eq0; case/norP=> Eq1 Ep1.
rewrite -(size_scaler q Ec1) Ec1q size_mul_id //.
by rewrite (polySpred Eq1) leq_addl.
Qed.

Lemma dvdp_mull : forall d m n : {poly R}, d %| n -> d %| m * n.
Proof.
move=> d m n; case/dvdpPc => c [q [Hc Hq]].
apply/dvdpPc; exists c; exists (m * q); split => //.
by rewrite scaler_mulr Hq mulrA.
Qed.

Lemma dvdp_mulr : forall d m n : {poly R}, d %| m -> d %|  m * n.
Proof. by move=> d m n d_m; rewrite mulrC dvdp_mull. Qed.

Lemma dvdp_mul : forall d1 d2 m1 m2 : {poly R},
  d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
move=> d1 d2 m1 m2.
case/dvdpPc=> c1 [q1 [Hc1 Hq1]]; case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c1 * c2); exists (q1 * q2); split.
  by rewrite mulf_neq0.
rewrite -scalerA scaler_mulr scaler_mull Hq1 Hq2 -!mulrA.
by rewrite [d1 * (q2 * _)]mulrCA.
Qed.

Lemma dvdp_trans : transitive (@dvdp R).
Proof.
move=> n d m.
case/dvdpPc=> c1 [q1 [Hc1 Hq1]]; case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c2 * c1); exists (q2 * q1); split.
  by apply: mulf_neq0.
by rewrite mulrC -scalerA Hq2 scaler_mulr Hq1 mulrA.
Qed.

Lemma dvdp_addr : forall m d n : {poly R}, d %| m -> (d %| m + n) = (d %| n).
Proof.
move=> n d m; case/dvdpPc=> c1 [q1 [Hc1 Hq1]].
apply/dvdpPc/dvdpPc; case=> c2 [q2 [Hc2 Hq2]].
  exists (c1 * c2); exists (c1 *: q2 - c2 *: q1).
  rewrite mulf_neq0 // mulr_addl.
rewrite -scaleNr -!scaler_mull -Hq1 -Hq2 !scalerA.
by rewrite mulNr mulrC scaleNr -scaler_subr addrC addKr.
exists (c1 * c2); exists (c1 *: q2 + c2 *: q1).
rewrite mulf_neq0 // mulr_addl.
by rewrite -!scaler_mull -Hq1 -Hq2 !scalerA mulrC addrC scaler_addr.
Qed.

Lemma dvdp_addl : forall n d m : {poly R}, d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addrC; exact: dvdp_addr. Qed.

Lemma dvdp_add : forall d m n : {poly R}, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdp_addr->. Qed.

Lemma dvdp_add_eq : forall d m n : {poly R}, d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdp_addr <-| move/dvdp_addl <-]. Qed.

Lemma dvdp_subr : forall d m n : {poly R}, d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> *; apply dvdp_add_eq; rewrite -addrA addNr simp. Qed.

Lemma dvdp_subl : forall d m n : {poly R}, d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n Hn; rewrite -(dvdp_addl _ Hn) subrK. Qed.

Lemma dvdp_sub : forall d m n : {poly R}, d %| m -> d %| n -> d %| m - n.
Proof.  by move=> d n m Dm Dn; rewrite dvdp_subl. Qed.

Lemma dvdp_mod : forall d m n : {poly R}, d %| m -> (d %| n) = (d %| n %% m).
Proof.
move=> d n m; case/dvdpPc => c1 [q1 [Ec1 Eq1]].
apply/dvdpPc/dvdpPc=> [] [] c2 [q2 [Ec2 Eq2]]; last first.
  exists (c1 * c2 * lead_coef n ^+ scalp m n).
  exists (c2 *: (m  %/ n) * q1 + c1 *: q2); split.
    by rewrite !mulf_neq0 ?scalp_Ineq0.
  rewrite -scalerA divCp_spec.
  rewrite scaler_addr -!scalerA Eq2 scaler_mull.
  by rewrite scaler_mulr Eq1 scaler_mull mulr_addl mulrA.
exists (c1 * c2);
  exists ((c1 * lead_coef n ^+ scalp m n) *: q2 - c2 *: (m %/ n) * q1).
rewrite mulf_neq0 // mulr_addl mulNr -!scaler_mull -!mulrA -Eq1 -Eq2.
rewrite -scaler_mulr !scalerA mulrC [_ * c2]mulrC mulrA.
by rewrite -[((_ * _) * _) *: _]scalerA -scaler_subr divCp_spec addrC addKr.
Qed.

Lemma gcdpp : idempotent (@gcdp R).
Proof. by move=> p; rewrite gcdpE ltnn modpp gcd0p. Qed.

Lemma dvdp_gcd2 : forall m n : {poly R}, (gcdp m n %| m) && (gcdp m n %| n).
Proof.
move=> m n.
elim: {m n}minn {-2}m {-2}n (leqnn (minn (size n) (size m))) => [|r Hrec] m n.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p) dvdpp dvdp0.
case: (eqVneq m 0) => [-> _|nz_m]; first by rewrite gcd0p dvdpp dvdp0.
case: (eqVneq n 0) => [->|nz_n]; first by rewrite gcdp0 dvdpp dvdp0.
rewrite gcdpE minnC /minn; case: ltnP => [lt_mn | le_nm] le_nr.
  suffices: minn (size m) (size (n %% m)) <= r.
    by move/Hrec; case/andP => E1 E2; rewrite E2 (dvdp_mod _ E2).
  rewrite leq_minl orbC -ltnS (leq_trans _ le_nr) //.
  by rewrite (leq_trans (modp_spec _ nz_m)) // leq_minr ltnW // leqnn.
suffices: minn (size n) (size (m %% n)) <= r.
  by move/Hrec; case/andP => E1 E2; rewrite E2 andbT (dvdp_mod _ E2).
rewrite leq_minl orbC -ltnS (leq_trans _ le_nr) //.
by rewrite (leq_trans (modp_spec _ nz_n)) // leq_minr leqnn.
Qed.

Lemma dvdp_gcdl : forall m n : {poly R}, gcdp m n %| m.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcdr : forall m n : {poly R}, gcdp m n %| n.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcd : forall p m n : {poly R}, p %| gcdp m n = (p %| m) && (p %| n).
Proof.
move=> p m n; apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite ?(dvdp_trans dv_pmn) ?dvdp_gcdl ?dvdp_gcdr.
move: (leqnn (minn (size n) (size m))) dv_pm dv_pn.
elim: {m n}minn {-2}m {-2}n => [|r Hrec] m n.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p).
case: (eqVneq m 0) => [-> _|nz_m]; first by rewrite gcd0p dvdp0.
case: (eqVneq n 0) => [->|nz_n]; first by rewrite gcdp0 dvdp0.
rewrite gcdpE minnC /minn; case: ltnP => Cnm le_r dv_m dv_n.
  apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_m).
  rewrite leq_minl orbC -ltnS (leq_trans _ le_r) //.
  by rewrite (leq_trans (modp_spec _ nz_m)) // leq_minr ltnW // leqnn.
apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_n).
rewrite leq_minl orbC -ltnS (leq_trans _ le_r) //.
by rewrite (leq_trans (modp_spec _ nz_n)) // leq_minr leqnn.
Qed.

(* Equality modulo constant factors *)

Lemma eqpP : forall m n : {poly R},
  reflect (exists c1, exists c2, [/\ c1 != 0, c2 != 0 & c1 *: m = c2 *: n])
          (m %= n).
Proof.
move=> m n; apply: (iffP idP) => [|[c1 [c2 [nz_c1 nz_c2 eq_cmn]]]]; last first.
by apply/andP; split; apply/dvdpPc;
      [exists c2; exists c1%:P | exists c1; exists c2%:P]; rewrite mul_polyC.
case/andP; case/dvdpPc=> /= c1 [q1 [Hc1 Hq1]].
case/dvdpPc=> /= c2 [q2 [Hc2 Hq2]].
case: (eqVneq m 0) => [m0 | m_nz].
  by do 2!exists c1; rewrite Hq1 m0 scaler0 !simp.
have def_q12: q1 * q2 = (c1 * c2)%:P.
  apply: (mulIf m_nz).
  by rewrite mulrAC mulrC -Hq1 -scaler_mulr -Hq2 scalerA -mul_polyC.
have: q1 * q2 != 0 by rewrite def_q12 -size_poly_eq0 size_polyC mulf_neq0.
rewrite mulf_eq0; case/norP=> nz_q1 nz_q2.
exists c2; exists q2`_0.
rewrite -[_ *: n]mul_polyC Hc2 -polyC_eq0 -size1_polyC //.
have:= size_mul_id nz_q1 nz_q2; rewrite def_q12 size_polyC mulf_neq0 //=.
by rewrite polySpred // => ->; rewrite leq_addl.
Qed.

(* eqp theory *)
Lemma eqpxx : reflexive (@eqp R).
Proof. by move=> p; rewrite /eqp dvdpp. Qed.

Lemma eqp_sym : symmetric (@eqp R).
Proof. by move=> p q; rewrite /eqp andbC. Qed.

Lemma eqp_trans : transitive (@eqp R).
Proof.
move=> p q r; case/andP=> Dp pD; case/andP=> Dq qD.
by rewrite /eqp (dvdp_trans Dp) // (dvdp_trans qD).
Qed.

Lemma eqp_ltrans : left_transitive (@eqp R).
Proof.
move=> p q r pq.
by apply/idP/idP=> e; apply: eqp_trans e; rewrite // eqp_sym.
Qed.

Lemma eqp_rtrans : right_transitive (@eqp R).
Proof. by move=> x y xy z; rewrite eqp_sym (eqp_ltrans xy) eqp_sym. Qed.

Lemma eqp0 : forall p, (p %= 0) = (p == 0).
Proof.
move=> p; case: eqP; move/eqP=> Ep; first by rewrite (eqP Ep) eqpxx.
by apply/negP; case/andP=> _; rewrite /dvdp modp0 (negPf Ep).
Qed.

Lemma eqp01 : 0 %= (1 : {poly R}) = false.
Proof.
case abs : (0 %= 1) => //; case/eqpP: abs=> c1 [c2 [c1n0 c2n0]].
by rewrite scaler0 scale_poly1; move/eqP; rewrite eq_sym polyC_eq0 (negbTE c2n0).
Qed.

Lemma size_eqp : forall p q, p %= q -> size p = size q.
Proof.
move=> p q.
case: (q =P 0); move/eqP => Eq.
  by rewrite (eqP Eq) eqp0; move/eqP->.
rewrite eqp_sym; case: (p =P 0); move/eqP => Ep.
  by rewrite (eqP Ep) eqp0; move/eqP->.
by case/andP => Dp Dq; apply: anti_leq; rewrite !size_dvdp.
Qed.

Lemma size_poly_eq1 : forall p, (size p == 1%N) = (p %= 1).
Proof.
move=> p; apply/size1P/idP=> [[c [cn0 ep]] |].
  by apply/eqpP; exists 1; exists c; rewrite oner_eq0 scale_poly1 scale1r.
by move/size_eqp; rewrite size_poly1; move/eqP; move/size1P.
Qed.

(* Now we can state that gcd is commutative modulo a factor *)
Lemma gcdpC : forall p q, gcdp p q %= gcdp q p.
Proof. by move=> p q; rewrite /eqp !dvdp_gcd !dvdp_gcdl !dvdp_gcdr. Qed.

Lemma dvdp_eqp1 : forall p q, p %| q -> q %= 1 -> p %= 1.
Proof.
move=> p q dpq hq.
have sizeq : size q == 1%N by rewrite size_poly_eq1.
have n0q : q != 0.
  by case abs: (q == 0) => //; move: hq; rewrite (eqP abs) eqp01.
rewrite -size_poly_eq1 eqn_leq -{1}(eqP sizeq) size_dvdp //=.
case p0 : (size p == 0%N); last by rewrite neq0_lt0n.
move: dpq;  rewrite size_poly_eq0 in p0.
by rewrite (eqP p0) dvd0p (negbTE n0q).
Qed.

Lemma dvdp_mulIl : forall p q, p %| p * q.
Proof. by move=> p q; apply: dvdp_mulr; exact: dvdpp. Qed.

Lemma dvdp_mulIr : forall p q, q %| p * q.
Proof. by move=> p q; apply: dvdp_mull; exact: dvdpp. Qed.

Lemma dvdp_mul2r : forall r p q, r != 0 -> (p * r %| q * r) = (p %| q).
Proof.
move => r p q nzr.
apply/idP/idP; last by move => ?; rewrite dvdp_mul ?dvdpp.
move/dvdpPc => [c [x [Hc Hx]]].
apply/dvdpPc.
exists c; exists x; split => //.
apply: (GRing.mulIf nzr).
by rewrite -GRing.mulrA -GRing.scaler_mull.
Qed.

Lemma dvdp_mul2l: forall r p q, r != 0 -> (r * p %| r * q) = (p %| q).
Proof. move => r p q; rewrite ![r * _]GRing.mulrC; apply dvdp_mul2r. Qed.

Lemma polyC_eqp1: forall c : R, (c%:P %= 1) = (c != 0).
Proof.
move=> c; apply/eqpP/idP=> [[x] [y]|nc0].
  case c0: (c == 0); rewrite // scale_poly1 (eqP c0) scaler0.
  case=> _ /=; move/negbTE<-.
  by move/eqP; rewrite eq_sym polyC_eq0.
by exists 1; exists c; rewrite nc0 /= nonzero1r scale_poly1 scale1r.
Qed.

Lemma gcd1p : forall p, gcdp 1 p %= 1.
Proof.
move=> p; rewrite -size_poly_eq1 gcdpE size_poly1; case: ltnP.
  by rewrite modp1 gcd0p size_poly1 eqxx.
move/size1_polyC=> e; rewrite e.
case p00: (p`_0 == 0); first by rewrite (eqP p00) modp0 gcdp0 size_poly1.
by rewrite modpC ?p00 // gcd0p size_polyC p00.
Qed.

Lemma gcdp1 : forall p, gcdp p 1 %= 1.
Proof. by move=> p; rewrite (eqp_ltrans (gcdpC _ _)) gcd1p. Qed.

Lemma eqp_dvdr : forall q p d, p %= q -> d %| p = (d %| q).
Proof.
move=> q p d epq; move: q p epq.
suff: forall q p, p %= q -> (d %| p) -> (d %| q)=> [Hpq|] q p.
  by move=> pq; apply/idP/idP; apply: Hpq; rewrite // eqp_sym.
by rewrite /eqp; case/andP=> pq qp dp; apply: (dvdp_trans dp).
Qed.

Lemma eqp_dvdl : forall d' d p, d %= d' -> d %| p = (d' %| p).
move=> d' d p edd'; move: d' d edd'.
suff: forall d' d, d %= d' -> (d %| p) -> (d' %| p)=> [Hdd'|] d' d.
  by move=> dd'; apply/idP/idP; apply: Hdd'; rewrite // eqp_sym.
by rewrite /eqp; case/andP=> dd' d'd dp; apply: (dvdp_trans d'd).
Qed.

Lemma dvdUp : forall d p, d %= 1 -> d %| p.
Proof. by move=> d p d1; rewrite (@eqp_dvdl 1)// dvd1p. Qed.

Lemma dvdp1 : forall d : {poly R}, (d %| 1) = (d %= 1).
Proof.
move=> d; apply/idP/idP; last exact: dvdUp.
move=> d1; move/size_dvdp:(d1); rewrite GRing.nonzero1r size_poly1.
move/(_ is_true_true); rewrite leq_eqVlt; case/orP; last first.
  rewrite ltnS leqn0 size_poly_eq0=> Ed0; move: d1.
  by rewrite (eqP Ed0) dvd0p oner_eq0.
case/size1P=> x [Hx ->].
by rewrite -size_poly_eq1 size_polyC Hx.
Qed.

Lemma dvdpU : forall d p, p %= 1 -> (d %| p) = (d %= 1).
Proof. by move=> d p p1; rewrite (@eqp_dvdr 1) // dvdp1. Qed.

Lemma eqp_mulC : forall p c, c != 0 -> c *: p %= p.
Proof.
move=> p c c0; apply/eqpP; exists 1; exists c; rewrite c0 oner_eq0.
by split=> //; rewrite scale1r.
Qed.

Lemma eqp_mul2r : forall r p q, r != 0 -> (p * r %= q * r) = (p %= q).
Proof. by move => r p q nz_r; rewrite /eqp !dvdp_mul2r. Qed.

Lemma eqp_mul2l: forall r p q, r != 0 -> (r * p %= r * q) = (p %= q).
Proof. by move => r p q nz_r; rewrite /eqp !dvdp_mul2l. Qed.

Lemma eqp_mull : forall r p q, (q %= r) -> (p * q %= p * r).
Proof.
move=> r p q;case/eqpP=> [c [d [c0 d0 e]]].
apply/eqpP; exists c; exists d.
by split=> //; rewrite scaler_mulr e -scaler_mulr.
Qed.

Lemma eqp_mulr : forall q p r, (p %= q) -> (p * r %= q * r).
Proof. by move=> q p r epq; rewrite ![_ * r]mulrC eqp_mull. Qed.

Lemma eqp_exp : forall p q n, p %= q -> p ^+ n %= q ^+ n.
Proof.
move=> p q n pq; elim: n=> [|n ihn]; first by rewrite !expr0 eqpxx.
by rewrite !exprS (@eqp_trans (q * p ^+ n)) // (eqp_mulr, eqp_mull).
Qed.

Lemma eqp_gcdr (r p q : {poly R}) : q %= r -> gcdp p q %= gcdp p r.
Proof.
move=> eqr; rewrite /eqp !(dvdp_gcd, dvdp_gcdl, andbT) /=.
by rewrite -(eqp_dvdr _ eqr) dvdp_gcdr (eqp_dvdr _ eqr) dvdp_gcdr.
Qed.

Lemma eqp_gcdl (q p r : {poly R}) :  p %= q -> gcdp p r %= gcdp q r.
move=> eqr; rewrite /eqp !(dvdp_gcd, dvdp_gcdr, andbT) /=.
by rewrite -(eqp_dvdr _ eqr) dvdp_gcdl (eqp_dvdr _ eqr) dvdp_gcdl.
Qed.

Lemma dvdp_size_eqp : forall p q, p %| q -> size p == size q = (p %= q).
Proof.
move=> p q pq; apply/idP/idP; last by move/size_eqp->.
case (q =P 0)=> [->|]; [|move/eqP => Hq].
  by rewrite size_poly0 size_poly_eq0; move/eqP->; rewrite eqpxx.
case (p =P 0)=> [->|]; [|move/eqP => Hp].
  by rewrite size_poly0 eq_sym size_poly_eq0; move/eqP->; rewrite eqpxx.
case/dvdpPc:pq=> x [qq [x0]]=> eqpq.
move:(eqpq); move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite (@size_eqp _ q); last exact: eqp_mulC.
rewrite size_mul_id ?p0 // => [-> HH|]; last first.
  apply/eqP=> HH; move: eqpq; rewrite HH mul0r.
  by move/eqP; rewrite scale_poly_eq0 (negPf Hq) (negPf x0).
suff: size qq == 1%N.
  case/size1P=> y [H1y H2y].
  apply/eqpP; exists y; exists x; first by rewrite eqpq H2y mul_polyC.
case: (size p) HH (size_poly_eq0 p)=> [|n]; first by case: eqP Hp.
by rewrite addnS -add1n eqn_addr;move/eqP->.
Qed.

Lemma size_divp : forall p q, q != 0 -> size q <= size p
  -> size (p %/ q) = ((size p) - (size q).-1)%N.
Proof.
move=> p q nq0 sqp.
move: (nq0); rewrite -size_poly_eq0 -lt0n=> lt0sq.
move: (sqp); move/(leq_trans lt0sq) => lt0sp.
move: (lt0sp); rewrite lt0n size_poly_eq0=> p0.
case:(divCp_spec p q).
move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite (@size_eqp _ p) ?eqp_mulC ?scalp_Ineq0 //.
case qq0: (p %/ q == 0).
  rewrite (eqP qq0) mul0r add0r=> es.
  by have:= modp_spec p nq0; rewrite -es ltnNge sqp.
move/negP:(qq0); move/negP; rewrite -size_poly_eq0 -lt0n=> lt0qq.
rewrite size_addl.
  rewrite size_mul_id ?qq0 // => ->.
  apply/eqP; rewrite -(eqn_addr ((size q).-1)).
  rewrite subnK; first by rewrite -subn1 addn_subA // subn1.
  rewrite /leq -(subn_add2l 1%N) !add1n prednK // (@ltn_predK (size q)) //.
    by rewrite addnC -subn_sub subnn sub0n.
  by rewrite -[size q]add0n ltn_add2r.
rewrite size_mul_id ?qq0 // (leq_trans (modp_spec _ nq0)) //.
rewrite /leq -(subn_add2l 1%N) !add1n (@ltn_predK (size q)).
  by rewrite addnC -subn_sub subSnn subn_eq0.
by rewrite -[size q]add0n ltn_add2r.
Qed.

Lemma gcdp_eq0 : forall p q, gcdp p q == 0 = (p == 0) && (q == 0).
Proof.
move=> p q; apply/idP/idP; last first.
  by case/andP; move/eqP->; move/eqP->; rewrite gcdp0.
move: p q; suff: forall p q,  gcdp p q == 0 -> (p == 0)=> [Hpq|] p q.
  move=> gpq0; apply/andP; split; [apply: (Hpq p q) | apply: (Hpq q p)]=> //.
  by rewrite -eqp0 (eqp_ltrans (gcdpC _ _)) eqp0.
move=> gpq0; rewrite -dvd0p.
apply: dvdp_trans (dvdp_gcdl p q).
by rewrite dvd0p.
Qed.

Lemma gcdp_addl_mul: forall p q r, gcdp r (p * r + q) %= gcdp r q.
Proof.
suff: forall p q r, gcdp r q %| gcdp r (p * r + q).
 move => H p q r.
 apply/andP; split => //.
 rewrite {2}(_: q = (-p) * r + (p * r + q)) ?H //.
 by rewrite GRing.mulNr GRing.addKr.
move => r0 p0 q0.
by rewrite dvdp_gcd dvdp_gcdl /= dvdp_addr ?dvdp_gcdr // dvdp_mull //
           dvdp_gcdl.
Qed.

Lemma coprimep_def :  forall p q, (coprimep p q) = (size (gcdp p q) == 1%N).
Proof. done. Qed.

Lemma gcdp_eqp1 : forall p q, gcdp p q %= 1 = (coprimep p q).
Proof. by move=> p q; rewrite coprimep_def size_poly_eq1. Qed.

Lemma coprimep_sym : forall p q, coprimep p q = coprimep q p.
Proof.
by move=> p q; rewrite -!gcdp_eqp1; apply: eqp_ltrans; rewrite gcdpC.
Qed.

Lemma coprime1p: forall p, coprimep 1 p.
Proof.
move=> p; rewrite /coprimep -[1%N](size_poly1 R); apply/eqP; apply: size_eqp.
exact: gcd1p.
Qed.

Lemma coprimep1 : forall p, coprimep p 1.
Proof. by move=> p; rewrite coprimep_sym; apply: coprime1p. Qed.

Lemma coprimep0 : forall p, coprimep p 0 = (p %= 1).
Proof. by move=> p; rewrite /coprimep gcdp0 size_poly_eq1. Qed.

Lemma coprime0p : forall p, coprimep 0 p = (p %= 1).
Proof. by move=> p; rewrite coprimep_sym coprimep0. Qed.

Lemma coprimepP : forall p q,
  reflect (forall d, d %| p -> d %| q -> d %= 1) (coprimep p q).
Proof.
move=> p q; apply: (iffP idP)=> [|h].
  rewrite /coprimep; move/eqP=> hs d dvddp dvddq.
  have dvddg: d %| gcdp p q by rewrite dvdp_gcd dvddp dvddq.
  by apply: (dvdp_eqp1 dvddg); rewrite -size_poly_eq1; apply/eqP.
by case/andP: (dvdp_gcd2 p q)=> h1 h2; rewrite /coprimep size_poly_eq1; apply: h.
Qed.

Lemma coprimepPn : forall p q, p != 0 ->
  reflect (exists d, (d %| gcdp p q) && ~~(d %= 1))  (~~ coprimep p q).
Proof.
move=> p q p0; apply: (iffP idP).
  by rewrite -gcdp_eqp1=> ng1; exists (gcdp p q); rewrite dvdpp /=.
case=> d; case/andP=> dg; apply: contra; rewrite -gcdp_eqp1=> g1.
by move: dg; rewrite (eqp_dvdr _ g1) -dvdp1.
Qed.

Lemma coprimep_dvdl : forall q p r,
  r %| q -> coprimep p q -> coprimep p r.
Proof.
move=> q p r rq cpq.
apply/coprimepP=> d dp dr; move/coprimepP:cpq=> cpq'.
by apply: cpq'; rewrite // (dvdp_trans dr).
Qed.

Lemma coprimep_dvdr : forall p q r,
  r %| p -> coprimep p q -> coprimep r q.
Proof.
move=> p q r rp; rewrite ![coprimep _ q]coprimep_sym.
by move/coprimep_dvdl; apply.
Qed.

Lemma modp_mod : forall p q, (p %% q) %% q = p %% q.
Proof.
move=> p q; case q0: (q == 0); first by rewrite (eqP q0) modp0.
by rewrite modp_size // modp_spec // q0.
Qed.

Lemma coprimep_modl : forall (p q : {poly R}),
  coprimep (p %% q) q = coprimep p q.
Proof.
move=> p q; symmetry; rewrite !coprimep_def.
case: (ltnP (size p) (size q))=> hpq; first by rewrite modp_size.
by rewrite gcdpE ltnNge hpq.
Qed.

Lemma coprimep_modr : forall (q p : {poly R}),
  coprimep q (p %% q) = coprimep q p.
Proof. by move=> q p; rewrite ![coprimep q _]coprimep_sym coprimep_modl. Qed.

Fixpoint egcdp_rec p q n {struct n} : {poly R} * {poly R} :=
  if n is n'.+1 then
    if q == 0 then (1, 0) else
    let: (u, v) := egcdp_rec q (p%%q) n' in
      (lead_coef q ^+ scalp p q *: v, (u - v * (p %/ q)))
  else (1, 0).
Definition egcdp p q :=
  if size q <= size p then egcdp_rec p q (size q)
    else let e :=  egcdp_rec q p (size p) in (e.2, e.1).

Lemma egcdp_recP : forall n p q, size q <= n -> size q <= size p
  -> let e := (egcdp_rec p q n) in gcdp p q %= e.1 * p + e.2 * q.
Proof.
elim=> [|n ihn] p q /=.
  rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
  by rewrite gcdp0 mul1r mulr0 addr0 eqpxx.
move=> sqSn qsp.
case q0: (q == 0)=> /=.
  by rewrite (eqP q0) gcdp0 mul1r mulr0 addr0 eqpxx.
have := (ihn q (p %% q)_ _).
case: (egcdp_rec _ _)=> u v=> ihn'.
rewrite gcdpE ltnNge qsp //= (eqp_ltrans (gcdpC _ _)).
apply: (eqp_trans (ihn' _ _)).
- by rewrite -(leq_add2l 1) !add1n (leq_trans (modp_spec _ _)) ?q0.
- by rewrite -(leq_add2l 1) !add1n (leq_trans (modp_spec _ _)) ?q0 ?leqnSn.
case: (divCp_spec p q); rewrite -scaler_mull scaler_mulr=> ->.
rewrite eqp_sym mulr_addr mulr_subl mulrA /=.
by rewrite addrC addrA -[_-_+_]addrA addNr addr0 eqpxx.
Qed.

(* Note : if no explicit Prop coercion here, let e := ... in ... is *)
(*        coerced to Prop                                           *)
Lemma egcdpP : forall p q (e := egcdp p q), (gcdp p q %= e.1 * p + e.2 * q : Prop).
Proof.
move=> p q; rewrite /egcdp; case: leqP=> /= hp; first by apply: egcdp_recP.
by move/ltnW in hp; rewrite (eqp_ltrans (gcdpC _ _)) addrC; apply: egcdp_recP.
Qed.

Lemma bezoutp : forall p q, exists u, exists v, u * p + v * q %= (gcdp p q).
Proof.
move=> p q; pose e := egcdp p q; exists e.1; exists e.2.
by rewrite eqp_sym egcdpP.
Qed.

Lemma gcdp_mul2l p q r : gcdp (p * q) (p * r) %= (p * gcdp q r).
Proof.
case: (eqVneq p 0)=> [->|hp]; first by rewrite !mul0r gcdp0 eqpxx.
rewrite /eqp !dvdp_gcd !dvdp_mul2l // dvdp_gcdr dvdp_gcdl !andbT.
move: (bezoutp q r) => [u] [v] huv.
rewrite eqp_sym in huv; rewrite (eqp_dvdr _ (eqp_mull _ huv)).
rewrite mulr_addr ![p * (_ * _)]mulrCA.
by apply: dvdp_add; rewrite dvdp_mull// (dvdp_gcdr, dvdp_gcdl).
Qed.

Lemma gcdp_mul2r q r p : gcdp (q * p) (r * p) %= (gcdp q r * p).
Proof. by rewrite ![_ * p]GRing.mulrC gcdp_mul2l. Qed.

Lemma mulp_gcdr p q r : r * (gcdp p q) %= gcdp (r * p) (r * q).
Proof. by rewrite eqp_sym gcdp_mul2l. Qed.

Lemma mulp_gcdl p q r : (gcdp p q) * r %= gcdp (p * r) (q * r).
Proof. by  rewrite eqp_sym gcdp_mul2r. Qed.

Lemma coprimep_div_gcd p q : (p != 0) || (q != 0) ->
  coprimep (p %/ (gcdp p q)) (q %/ gcdp p q).
Proof.
move=> hpq.
have gpq0: gcdp p q != 0 by rewrite gcdp_eq0 negb_and.
rewrite -gcdp_eqp1 -(@eqp_mul2r (gcdp p q)) // mul1r.
have: gcdp p q %| p by rewrite dvdp_gcdl.
have: gcdp p q %| q by rewrite dvdp_gcdr.
rewrite -!dvdpP eq_sym; move/eqP=> hq; rewrite eq_sym; move/eqP=> hp.
rewrite (eqp_ltrans (mulp_gcdl _ _ _)) hq hp.
rewrite (eqp_ltrans (@eqp_gcdl p _ _ _)) ?eqp_mulC ?scalp_Ineq0 //.
by rewrite (eqp_ltrans (@eqp_gcdr q _ _ _)) ?eqp_mulC ?scalp_Ineq0 // eqpxx.
Qed.

Lemma coprimep_bezout : forall p q,
  reflect (exists u, exists v, u * p + v * q %= 1) (coprimep p q).
Proof.
move=> p q; rewrite -gcdp_eqp1; apply:(iffP idP)=> [g1|].
  case: (bezoutp p q) => [u [v Puv]]; exists u; exists v.
  exact: eqp_trans g1.
move=>[u [v]]; rewrite eqp_sym=> Puv.
rewrite -dvdp1; rewrite (eqp_dvdr _ Puv).
by rewrite dvdp_addr dvdp_mull ?dvdp_gcdl ?dvdp_gcdr.
Qed.

Lemma gaussp : forall p q d, coprimep d q -> (d %| p * q) = (d %| p).
Proof.
move=> p q d; move/coprimep_bezout=>[u [v Puv]].
apply/idP/idP; last exact: dvdp_mulr.
move:Puv; move/(eqp_mull p).
rewrite mulr1 mulr_addr eqp_sym=> peq dpq.
rewrite (eqp_dvdr _  peq) dvdp_addr.
  by rewrite mulrA mulrAC dvdp_mulr.
by rewrite mulrA dvdp_mull ?dvdpp.
Qed.

Lemma coprimep_mulr : forall (p q r : {poly R}),
  coprimep p (q * r) = (coprimep p q && coprimep p r).
Proof.
move=> p q r; apply/coprimepP/andP=> [hp|[/coprimepP hq hr]].
  split; apply/coprimepP=> d dp dq; rewrite hp //;
  [exact: dvdp_mulr|exact: dvdp_mull].
move=> d dp dqr; move/(_ _ dp) in hq.
rewrite gaussp in dqr; first exact: hq.
by move/coprimep_dvdr:hr; apply.
Qed.

Lemma coprimep_mull : forall (q r p : {poly R}),
  coprimep (q * r) p = (coprimep q p && coprimep r p).
Proof. by move=> q r p; rewrite ![coprimep _ p]coprimep_sym coprimep_mulr. Qed.

(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 if Q null, 0 otherwise*)
Fixpoint gdcop_rec q p n :=
  if n is m.+1 then
      if coprimep p q then p
        else gdcop_rec q (p %/ (gcdp p q)) m
    else (q == 0)%:R.
Definition gdcop q p := gdcop_rec q p (size p).

CoInductive gdcop_spec q p : {poly R} -> Type :=
  GdcopSpec r of (r %| p) & ((coprimep r q) || (p == 0))
  & (forall d,  d %| p -> coprimep d q -> d %| r)
  : gdcop_spec q p r.


Lemma gdcop0 : forall q, gdcop q 0 = (q == 0)%:R.
Proof. by move=> q; rewrite /gdcop size_poly0. Qed.

Lemma divpp : forall p, p != 0 -> p %/ p = (lead_coef p ^+ scalp p p)%:P.
Proof.
move=> p np0; case: (divCp_spec p p).
rewrite modpp addr0. move/eqP.
by rewrite -mul_polyC (inj_eq (mulIf np0)); move/eqP.
Qed.

Lemma gdcop_recP : forall q p n,
  size p <= n -> gdcop_spec q p (gdcop_rec q p n).
Proof.
move=> q p n; elim: n p => [p | n ihn p] /=.
  rewrite leqn0 size_poly_eq0; move/eqP->.
  case q0: (_ == _); split; rewrite ?coprime1p ?dvdp0 ?eqxx ?orbT //.
  by move=> d _; rewrite (eqP q0) coprimep0 dvdp1.
move=> hs; case cop : (coprimep _ _); first by split; rewrite ?dvdpp ?cop.
case p0 : (p == 0).
  by rewrite (eqP p0) div0p; apply: ihn; rewrite size_poly0 leq0n.
case q0: (q == 0).
  rewrite (eqP q0) gcdp0 divpp ?p0 //= => {hs ihn}; case: n=> /=.
    rewrite eqxx; split; rewrite ?dvd1p ?coprimep0 ?eqpxx //=.
    by move=> d _; rewrite coprimep0 -dvdp1.
  move=> n; rewrite coprimep0 polyC_eqp1 scalp_Ineq0.
  split; first by rewrite (@eqp_dvdl 1) ?dvd1p ?polyC_eqp1 ?scalp_Ineq0 //.
    by rewrite coprimep0 polyC_eqp1 scalp_Ineq0.
  by move=> d _; rewrite coprimep0; move/eqp_dvdl->; rewrite dvd1p.
(* should we have a spec for dvdn ? => I also wondered *)
case: (divCp_spec p (gcdp p q)); rewrite modp_dvd ?dvdp_gcdl // addr0 => e.
have sgp : size (gcdp p q) <= size p.
  by apply: size_dvdp; rewrite ?gcdp_eq0 ?p0 ?q0 // dvdp_gcdl.
have : p %/ gcdp p q != 0; last move/negPf=>p'n0.
  move: (dvdp_mulIl (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_scaler ?scalp_Ineq0 //size_poly_eq0 p0.
have gn0 : gcdp p q != 0.
  move: (dvdp_mulIr (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_scaler ?scalp_Ineq0 //size_poly_eq0 p0.
have sp' : size (p %/ (gcdp p q)) <= n.
  rewrite size_divp ?sgp // leq_sub_add (leq_trans hs)//.
  rewrite -subn_gt0 addnK -subn1 -ltn_add_sub addn0 ltnNge leq_eqVlt.
  by rewrite [_ == _]cop ltnS leqn0 size_poly_eq0 (negPf gn0).
case (ihn _ sp')=> r' dr'p'; first rewrite p'n0 orbF=> cr'q maxr'.
constructor=> //=; rewrite ?p0 ?orbF //.
  apply: (dvdp_trans dr'p').
  apply/dvdpPc; exists (lead_coef (gcdp p q) ^+ scalp p (gcdp p q));
    exists (gcdp p q).
  by rewrite e mulrC scalp_Ineq0.
move=> d dp cdq.
apply: maxr'; last by rewrite cdq.
case dpq: (d %| gcdp p q).
  move: (dpq); rewrite dvdp_gcd dp /= => dq.
  apply: dvdUp; move: cdq; apply: contraLR=> nd1.
  apply/coprimepPn.
    move/negP: p0; move/negP; apply: contra=> d0.
    by move:dp; rewrite (eqP d0) dvd0p.
  by exists d; rewrite dvdp_gcd dvdpp dq nd1.
move: (dp); apply: contraLR=> ndp'.
rewrite (@eqp_dvdr ((lead_coef (gcdp p q) ^+ scalp p (gcdp p q))*:p)).
  by rewrite e; rewrite gaussp //; apply: (coprimep_dvdl (dvdp_gcdr _ _)).
by rewrite eqp_sym eqp_mulC // scalp_Ineq0.
Qed.

Lemma gdcopP : forall q p, gdcop_spec q p (gdcop q p).
Proof. by move=> q p; rewrite /gdcop; apply: gdcop_recP. Qed.

Lemma dvdp_gdco : forall p q d : {poly R},
  p != 0 -> size d == 2%N ->
  (d %| (gdcop q p)) = (d %| p) && ~~(d %| q).
Proof.
move=> p q d p0 sd.
apply/idP/idP.
  case: gdcopP=> r rp crq maxr dr.
  move/negPf: (p0)=> p0f.
  rewrite (dvdp_trans dr) //=.
  move: crq; apply: contraL=> dq; rewrite p0f orbF; apply/coprimepPn.
    by move:p0; apply: contra=> r0; move: rp; rewrite (eqP r0) dvd0p.
  by exists d; rewrite dvdp_gcd dr dq -size_poly_eq1 (eqP sd).
case/andP=> dp dq.
case: gdcopP=> r rp crq maxr.
apply: maxr=> //.
apply/negPn; apply/negP; case/coprimepPn.
  by move:p0; apply:contra=> d0; move: dp; rewrite (eqP d0) dvd0p.
move=> x; case/andP.
rewrite dvdp_gcd; case/andP=> xd xq nx1.
case (d =P 0)=> [nd0|]; [|move/eqP=> nd0].
  by move: sd; rewrite nd0 size_polyC eqxx.
move:(xd); move/negP: nd0; move/negPn=> nd0; move/(size_dvdp nd0).
rewrite (eqP sd) leq_eqVlt; case/orP.
  rewrite -(eqP sd) dvdp_size_eqp //.
  by move/(eqp_dvdl q); rewrite xq (negPf dq).
rewrite leq_eqVlt; case/orP; first by rewrite eqSS size_poly_eq1 (negPf nx1).
rewrite !ltnS leqn0 size_poly_eq0=> x0; rewrite (eqP x0) dvd0p in xd.
by rewrite (eqP xd) size_poly0 in sd.
Qed.

Lemma root_gdco : forall p q, p != 0 ->
  forall x, root (gdcop q p) x = root p x && ~~(root q x).
Proof.
move=> p q p0 x /=; rewrite !root_factor_theorem.
apply: dvdp_gdco; rewrite ?p0 //.
rewrite size_addl size_polyX // size_opp size_polyC.
by case: (x != 0).
Qed.

Lemma eqp_root : forall p q, p %= q -> root p =1 root q.
Proof.
move=> p q; move/eqpP=> [c [d [c0 d0 e]]] x.
move/negPf:c0=>c0; move/negPf:d0=>d0.
rewrite rootE -[_==_]orFb -c0 -mulf_eq0 -horner_scaler e.
by rewrite horner_scaler mulf_eq0 d0.
Qed.

Lemma root_gcd : forall p q x, root (gcdp p q) x = root p x && root q x.
Proof.
move=> p q x; rewrite /= !root_factor_theorem.
apply/idP/andP=> [dg| [dp dq]].
  by split; apply: (dvdp_trans dg); rewrite ?(dvdp_gcdl, dvdp_gcdr).
have:= (bezoutp p q)=> [[u [v]]]; rewrite eqp_sym=> e.
by rewrite (eqp_dvdr _ e) dvdp_addl dvdp_mull.
Qed.

Lemma root_biggcd : forall x (ps : seq {poly R}),
  root (\big[@gcdp _/0]_(p <- ps) p) x = all (fun p => root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root0.
by move=> p ps ihp; rewrite big_cons /= root_gcd ihp.
Qed.

Lemma root_bigmul : forall x (ps : seq {poly R}),
  ~~root (\big[*%R/1]_(p <- ps) p) x = all (fun p => ~~ root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root1.
by move=> p ps ihp; rewrite big_cons /= root_mul negb_or ihp.
Qed.

Lemma dvdp_exp : forall p n m, size p > 1 -> (p ^+ n %| p ^+ m) = (n <= m).
Proof.
move=> p n m pn0; elim: n p m pn0 => [|n ihn] p.
  by case=>[|m]; rewrite dvd1p leq0n.
move=> m sp1; have pn0: p != 0.
  by rewrite -size_poly_eq0; case: (size p) sp1.
case: m=> [|m].
  rewrite ltn0 expr0; apply/negP; apply/negP.
  rewrite dvdp1 -size_poly_eq1 -[size _]prednK; last first.
    by rewrite ltnNge leqn0 size_poly_eq0 expf_neq0.
  rewrite size_exp_id; apply/negP; case/eqP; move/eqP.
  by rewrite muln_eq0 orbF -subn1 subn_eq0 leqNgt sp1.
by rewrite !exprS dvdp_mul2l// ihn.
Qed.

Lemma dvdp_mul_exp : forall p q n m, p != 0 ->
  (p ^+ n %| q * p ^+ m) = (p ^+ (n - m) %| q).
Proof.
move=> p q n m pn0; case: (leqP n m)=> hnm.
  move:(hnm); rewrite -subn_eq0; move/eqP->; rewrite expr0 dvd1p.
  apply: dvdp_mull; case sp1: (size p > 1); first by rewrite dvdp_exp.
  move/negP:sp1; move/negP; rewrite -ltnNge ltnS.
  case esp: (size p)=> [|sp].
    by move/eqP:esp; rewrite size_poly_eq0 (negPf pn0).
  rewrite ltnS leqn0; move/eqP=> sp0; move/eqP: esp; rewrite sp0.
  by rewrite size_poly_eq1=> p1; rewrite dvdUp // -(@exp1rn _ n) eqp_exp.
rewrite -{1}[n](@subnK m) 1?ltnW// exprn_addr dvdp_mul2r//.
elim: m {hnm}=> [|m ihm]; first by rewrite expr0 oner_eq0.
by rewrite exprS mulf_neq0.
Qed.


Lemma dvdp_poly_comp : forall r p q, (p %| q) -> (p \Po r) %| (q \Po r).
Proof.
move => r p q; move/dvdpPc => [c [s [Hc Hq]]].
apply/dvdpPc; exists c; exists (s \Po r); split => //.
by rewrite -poly_comp_scall Hq poly_comp_mull.
Qed.

Lemma gcdp_poly_comp : forall r p q, gcdp p q \Po r %=  gcdp (p \Po r) (q \Po r).
Proof.
move => r p q.
apply/andP; split.
  by rewrite dvdp_gcd !dvdp_poly_comp ?dvdp_gcdl ?dvdp_gcdr.
case: (bezoutp p q) => u; case => v; case/andP.
move/(dvdp_poly_comp r) => Huv _.
rewrite (dvdp_trans _ Huv) // poly_comp_addl !poly_comp_mull.
by rewrite dvdp_add // dvdp_mull // (dvdp_gcdl,dvdp_gcdr).
Qed.

Lemma coprimep_poly_comp :
  forall r p q, coprimep p q -> coprimep (p \Po r) (q \Po r).
Proof.
move => r p q.
rewrite -!gcdp_eqp1 -!dvdp1.
move/(dvdp_poly_comp r); rewrite poly_comCp => Hgcd.
by apply: dvdp_trans Hgcd; case/andP: (gcdp_poly_comp r p q).
Qed.

End PolyDivIDomain.

Section FieldMap.

Variable aR : fieldType.
Variable rR : ringType.
Implicit Type p q : {poly aR}.

Variable f : {rmorphism aR -> rR}.
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma edivp_map : forall p q,
  edivp p^f q^f = (scalp p q, (p %/ q)^f, (p %% q)^f).
Proof.
move=> p q; rewrite /divp /scalp /modp /edivp map_poly_eq0 size_map_poly.
case: eqP; rewrite /= -(rmorph0 (map_poly_rmorphism f)) //; move/eqP=> q_nz.
move: (size p) => m; elim: m 0%N 0 p => [|m IHm] qq r p /=.
  rewrite  !size_map_poly !lead_coef_map //.
  rewrite -(map_polyXn f) -!(map_polyC f).
  by rewrite -!rmorphM -rmorph_sub -rmorphD; case: (_ < _).
rewrite  !size_map_poly !lead_coef_map //.
rewrite -(map_polyXn f) -!(map_polyC f).
by rewrite -!rmorphM -rmorph_sub -rmorphD /= IHm; case: (_ < _).
Qed.

Lemma scalp_map : forall p q, scalp p^f q^f = scalp p q.
Proof. by move=> p q; rewrite /scalp edivp_map. Qed.

Lemma map_divp : forall p q, (p %/ q)^f = p^f %/ q^f.
Proof. by move=> p q; rewrite /divp edivp_map. Qed.

Lemma map_modp : forall p q, (p %% q)^f = p^f %% q^f.
Proof. by move=> p q; rewrite /modp edivp_map. Qed.

Lemma dvdp_map : forall p q, (p^f %| q^f) = (p %| q).
Proof. by move=> p q; rewrite /dvdp -map_modp map_poly_eq0. Qed.

Lemma eqp_map : forall p q, (p^f %= q^f) = (p %= q).
Proof. by move=> p q; rewrite /eqp !dvdp_map. Qed.

Lemma gcdp_map : forall p q, (gcdp p q)^f = gcdp p^f q^f.
Proof.
move=> p q; wlog lt_p_q: p q / size p < size q.
  move=> IH; case: (ltnP (size p) (size q)) => [|le_q_p]; first exact: IH.
  rewrite gcdpE (gcdpE p^f) !size_map_poly ltnNge le_q_p /= -map_modp.
  case: (eqVneq q 0) => [-> | q_nz]; first by rewrite rmorph0 !gcdp0.
  by rewrite IH ?modp_spec.
elim: {q}_.+1 p {-2}q (ltnSn (size q)) lt_p_q => // m IHm p q le_q_m lt_p_q.
rewrite gcdpE (gcdpE p^f) !size_map_poly lt_p_q -map_modp.
case: (eqVneq p 0) => [-> | q_nz]; first by rewrite rmorph0 !gcdp0.
by rewrite IHm ?(leq_trans lt_p_q) ?modp_spec.
Qed.

End FieldMap.


Section Multiplicity.

Variable R : idomainType.
Implicit Types x y c : R.
Implicit Types p q r d : {poly R}.

(* Definition multiplicity (x : R) (p : {poly R}) : nat :=  *)
(*   (odflt ord0 (pick (fun i : 'I_(size p).+1 =>  ((('X - x%:P) ^+ i %| p))  *)
(*                                  && (~~ (('X - x%:P) ^+ i.+1 %| p))))). *)

(* Notation "'\mu_' x" := (multiplicity x) *)
(*   (at level 8, format "'\mu_' x") : ring_scope. *)

(* Lemma mu0 : forall x, \mu_x 0 = 0%N. *)
(* Proof. *)
(* by move=> x; rewrite /multiplicity; case: pickP=> //= i; rewrite !dvdp0. *)
(* Qed. *)

(* Lemma muP : forall p x, p != 0 -> *)
(*   (('X - x%:P) ^+ (\mu_x p) %| p) && ~~(('X - x%:P) ^+ (\mu_x p).+1 %| p). *)
(* Proof. *)
(* move=> p x np0; rewrite /multiplicity; case: pickP=> //= hp. *)
(* have {hp} hip: forall i, i <= size p  *)
(*     -> (('X - x%:P) ^+ i %| p) -> (('X - x%:P) ^+ i.+1 %| p). *)
(*   move=> i; rewrite -ltnS=> hi; move/negbT: (hp (Ordinal hi)).  *)
(*   by rewrite -negb_imply negbK=> /implyP. *)
(* suff: forall i, i <= size p -> ('X - x%:P) ^+ i %| p. *)
(*   move=> /(_ _ (leqnn _)) /(size_dvdp np0). *)
(*   rewrite -[size _]prednK; first by rewrite size_exp_id size_factor mul1n ltnn. *)
(*   by rewrite lt0n size_poly_eq0 expf_eq0 factor_eq0 lt0n size_poly_eq0 np0. *)
(* elim=> [|i ihi /ltnW hsp]; first by rewrite expr0 dvd1p. *)
(* by rewrite hip // ihi. *)
(* Qed. *)

(* Lemma maxdivp : forall p a, p != 0 ->  *)
(*   exists2 q : {poly R}, (~~ root q a) & p = q * ('X - a%:P) ^+ (\mu_a p). *)
(* Proof. *)
(* move=> p a np0. *)

Lemma maxdivp : forall p a, p != 0 ->
  { q : {poly R} & (~~ root q a) &
    { n |  p = q * ('X - a%:P) ^+ n }}.
Proof.
move=> p; move: {-2}p (erefl (size p)); elim: (size p)=> {p} [p sp|n ihn p sp].
  by move=> a; move/eqP: sp; rewrite size_poly_eq0; move/eqP->; rewrite eqxx.
move=> a p0.
case pa0: (root p a); first last.
  by exists p; rewrite ?pa0 //; exists 0%N; rewrite expr0 mulr1.
have /sigW [q /eqP hp]: exists q, p == q * ('X - a%:P).
  by case: (factor_theorem p a _)=> // q /eqP hq; exists q.
(* have: size (p) = n.+1 by rewrite size_scaler // scalp_id. *)
case q0 : (q == 0).
  by move/eqP:q0 hp->; move/eqP; rewrite mul0r (negPf p0).
case: (@ihn q _ a); rewrite ?q0 //.
  move: sp; rewrite hp size_mul_id ?q0 ?factor_eq0 //.
  by rewrite size_factor addnC /=; case.
move=> q' q'a [n' hq]; exists q'=> //; exists n'.+1.
by rewrite hp hq -mulrA exprSr.
Defined.

Definition multiplicity (x : R) (p : {poly R}) :=
  if ((p != 0) =P true) is ReflectT hp
    then let (_, _, Pc) := (maxdivp x hp) in projT1 Pc
    else 0%N.

Notation "'\mu_' x" := (multiplicity x)
  (at level 8, format "'\mu_' x") : ring_scope.

Lemma mu_spec : forall p a, p != 0 ->
  { q : {poly R} & (~~ root q a)
    & ( p = q * ('X - a%:P) ^+ (\mu_a p)) }.
Proof.
move=> p a pn0; rewrite /multiplicity; case: eqP=> //=.
move=> pn0'; case: (maxdivp _ _)=> q qn0 [n hn] /=.
by exists q=> //.
Qed.

Lemma mu0 : forall x, \mu_x 0 = 0%N.
Proof.
by rewrite /multiplicity=> x; case: eqP=> // e; move: {-1}(e); rewrite eqxx.
Qed.

Lemma root_mu : forall p x, ('X - x%:P) ^+ (\mu_x p) %| p.
Proof.
move=> p x; case p0: (p == 0); first by rewrite (eqP p0) mu0 expr0 dvd1p.
case: (@mu_spec p x); first by rewrite p0.
by move=> q qn0 hp //=; rewrite {2}hp dvdp_mulIr.
Qed.

(* Lemma size_factor_exp : forall x n, size (('X - x%:P) ^+ n) = n.+1. *)
(* Proof. *)
(* move=> x n; rewrite -[size _]prednK ?size_exp_id ?size_factor ?mul1n //. *)
(* by rewrite ltnNge leqn0 size_poly_eq0 expf_neq0 // factor_eq0. *)
(* Qed. *)

Lemma root_muN : forall p x, p != 0 ->
  (('X - x%:P)^+(\mu_x p).+1 %| p) = false.
Proof.
move=> p x pn0; case: (mu_spec x pn0)=> q qn0 hp /=.
rewrite {2}hp exprS dvdp_mul2r; last first.
  by rewrite expf_neq0 // factor_eq0.
apply: negbTE; rewrite -dvd_factorP; apply: contra qn0.
by move/eqP->; rewrite root_mul root_factor eqxx orbT.
Qed.

Lemma root_le_mu : forall p x n, p != 0 -> ('X - x%:P)^+n %| p = (n <= \mu_x p).
Proof.
move=> p x n pn0; case: leqP=> hn; last apply/negP=> hp.
  apply: (@dvdp_trans _ (('X - x%:P) ^+ (\mu_x p))); last by rewrite root_mu.
  by rewrite dvdp_exp// size_factor.
suff : ('X - x%:P) ^+ (\mu_x p).+1 %| p by rewrite root_muN.
by apply: dvdp_trans hp; rewrite dvdp_exp// size_factor.
Qed.

Lemma muP : forall p x n, p != 0 ->
  (('X - x%:P)^+n %| p) && ~~(('X - x%:P)^+n.+1 %| p) = (n == \mu_x p).
Proof.
move=> p x n hp0; rewrite !root_le_mu//; case: (ltngtP n (\mu_x p))=> hn.
+ by rewrite ltnW//=.
+ by rewrite leqNgt hn.
+ by rewrite hn leqnn.
Qed.

Lemma mu_gt0 : forall p x, p != 0 -> (0 < \mu_x p)%N = root p x.
Proof. by move=> p x pn0; rewrite -root_le_mu// expr1 root_factor_theorem. Qed.

Lemma muNroot : forall (p : {poly R}) x, ~~ root p x -> \mu_x p = 0%N.
Proof.
move=> p x; case p0: (p == 0); first by rewrite (eqP p0) rootC eqxx.
by move=> pnx0; apply/eqP; rewrite -leqn0 leqNgt mu_gt0 ?p0.
Qed.

Lemma mu_polyC : forall c x, \mu_x (c%:P) = 0%N.
Proof.
move=> c x; case c0: (c == 0); first by rewrite (eqP c0) mu0.
by apply: muNroot; rewrite rootC c0.
Qed.

Lemma maxdivp_mu : forall x p n,
  ~~ root p x -> \mu_x (p * ('X - x%:P) ^+ n) = n.
Proof.
move=> x p n p0; apply/eqP; rewrite eq_sym -muP//; last first.
  apply: contra p0; rewrite mulf_eq0 expf_eq0 factor_eq0 andbF orbF.
  by move/eqP->; rewrite root0.
rewrite dvdp_mulIr /= exprS dvdp_mul2r -?root_factor_theorem //.
by rewrite expf_eq0 factor_eq0 andbF //.
Qed.

Lemma mu_mul : forall p q x, p * q != 0 ->
  \mu_x (p * q) = (\mu_x p + \mu_x q)%N.
Proof.
move=> p q x hpqn0; apply/eqP; rewrite eq_sym -muP//.
rewrite exprn_addr dvdp_mul ?root_mu//=.
move:hpqn0; rewrite mulf_eq0 negb_or; case/andP=> hp0 hq0.
move: (mu_spec x hp0)=> [qp qp0 hp].
move: (mu_spec x hq0)=> [qq qq0 hq].
rewrite {2}hp {2}hq exprS exprn_addr !mulrA [qp * _ * _]mulrAC.
rewrite !dvdp_mul2r ?expf_neq0 ?factor_eq0 // -dvd_factorP.
move: (mulf_neq0 qp0 qq0); rewrite -horner_mul; apply: contra; move/eqP->.
by rewrite horner_mul horner_factor subrr mulr0.
Qed.

Lemma mu_factor : forall x, \mu_x ('X - x%:P) = 1%N.
Proof.
move=> x; apply/eqP; rewrite eq_sym -muP; last by rewrite factor_eq0.
by rewrite expr1 dvdpp/= -{2}[_ - _]expr1 dvdp_exp// size_factor.
Qed.

Lemma mu_mulC : forall c p x, c != 0 -> \mu_x (c *: p) = \mu_x p.
Proof.
move=> c p x cn0; case p0: (p == 0); first by rewrite (eqP p0) scaler0.
by rewrite -mul_polyC mu_mul ?mu_polyC// mulf_neq0 ?p0 ?polyC_eq0.
Qed.

Lemma mu_opp : forall p x, \mu_x (-p) = \mu_x p.
Proof.
move=> p x; rewrite -mulN1r -polyC1 -polyC_opp mul_polyC mu_mulC //.
by rewrite -oppr0 (inj_eq (inv_inj (@opprK _))) oner_eq0.
Qed.

Lemma mu_exp : forall p x n, \mu_x (p ^+ n) = (\mu_x p * n)%N.
Proof.
move=> p x n.
elim: n p => [|n ihn] p; first by rewrite expr0 mu_polyC muln0.
case p0: (p == 0); first by rewrite (eqP p0) exprS mul0r mu0 mul0n.
by rewrite exprS mu_mul ?ihn ?mulnS// mulf_eq0 expf_eq0 p0 andbF.
Qed.

Lemma mu_addr : forall p q x, p != 0 -> \mu_x p < \mu_x q ->
  \mu_x (p + q) = \mu_x p.
Proof.
move=> p q x pn0 mupq.
have pqn0 : p + q != 0.
  move: mupq; rewrite ltnNge; apply: contra.
  by rewrite -[q]opprK subr_eq0; move/eqP->; rewrite opprK mu_opp leqnn.
have qn0: q != 0 by move: mupq; apply: contraL; move/eqP->; rewrite mu0 ltn0.
case: (mu_spec x pn0)=> [qqp qqp0] hp.
case: (mu_spec x qn0)=> [qqq qqq0] hq.
rewrite hp hq -(subnK (ltnW mupq)).
rewrite mu_mul ?mulf_eq0; last first.
  rewrite expf_eq0 factor_eq0 andbF orbF.
  by apply: contra qqp0; move/eqP->; rewrite root0.
rewrite mu_exp mu_factor mul1n [\mu_x qqp]muNroot // add0n.
rewrite exprn_addr mulrA -mulr_addl mu_mul; last first.
  by rewrite mulr_addl -mulrA -exprn_addr subnK 1?ltnW // -hp -hq.
rewrite muNroot ?add0n ?mu_exp ?mu_factor ?mul1n //.
rewrite rootE !horner_lin horner_exp horner_factor subrr.
by rewrite ltn_subS // -predn_sub exprS mul0r mulr0 addr0.
Qed.

Lemma mu_addl : forall p q x, q != 0 -> \mu_x p > \mu_x q ->
  \mu_x (p + q) = \mu_x q.
Proof. by move=> p q x q0 hmu; rewrite addrC mu_addr. Qed.

Lemma mu_div : forall p x n, n <= \mu_x p ->
  \mu_x (p %/ ('X - x%:P) ^+ n) = (\mu_x p - n)%N.
Proof.
move=> p x n hn.
case p0: (p == 0); first by rewrite (eqP p0) div0p mu0 sub0n.
case: (@mu_spec p x); rewrite ?p0 // => q hq hp.
rewrite {1}hp -{1}(subnK hn) exprn_addr mulrA.
rewrite divp_mull ?expf_eq0 ?factor_eq0 ?andbF //.
rewrite lead_coef_exp_id lead_coef_factor !exp1rn scale1r.
rewrite mu_mul ?mulf_eq0 ?expf_eq0 ?factor_eq0 ?andbF ?orbF; last first.
  by apply: contra hq; move/eqP->; rewrite root0.
by rewrite mu_exp muNroot // add0n mu_factor mul1n.
Qed.

End Multiplicity.

Notation "'\mu_' x" := (multiplicity x)
  (at level 8, format "'\mu_' x") : ring_scope.

Section PolyField.

Variable F : fieldType.

Lemma dvdpfP (p q : {poly F}) :
  (p ==  lead_coef q ^- scalp p q *: (p %/ q) * q) = (q %| p).
Proof.
rewrite -dvdpP.
by rewrite !(can2_eq (scalerK _) (scalerKV _)) ?scalp_Ineq0 // -scaler_mull.
Qed.

End PolyField.

Module PolyDivPreClosedField.
Section PolyDivPreClosedField.

Variable F : fieldType.

(* With ClosedField axiom *)
Variable axiom : GRing.ClosedField.axiom F.

Lemma root_size_neq1 : forall p : {poly F},
  reflect (exists x, root p x) (size p != 1%N).
Proof.
move=> p; case p0: (p == 0).
  rewrite (eqP p0) /= size_poly0 /=.
  by constructor; exists 0; rewrite root0.
apply: (iffP idP); last first.
  case=> x; rewrite root_factor_theorem.
  apply: contraL; rewrite size_poly_eq1; move/eqp_dvdr->.
  rewrite dvdp1 -size_poly_eq1 size_addl size_polyX //.
  by rewrite size_opp size_polyC; case: (x != 0).
move/negPf => sp.
case: (ltnP (size p).-1 1)=> [|s2].
  rewrite ltnS leqn0 -subn1 subn_eq0 leq_eqVlt ltnS leqn0.
  by rewrite size_poly_eq0 sp p0.
have := axiom (fun n => -p`_n * (lead_coef p)^-1) s2.
case=> x H; exists x.
have : 0 < size p by apply: leq_trans s2 _; apply: leq_pred.
rewrite rootE horner_coef; move/prednK<-; rewrite big_ord_recr /= H.
apply/eqP; rewrite big_distrr -big_split big1 //= => i _.
rewrite mulrA [ _ * (_ / _)]mulrCA mulfV; last by rewrite lead_coef_eq0 p0.
by rewrite mulr1 mulNr addrN.
Qed.

Lemma ex_px_neq0 : forall p : {poly F}, p != 0 -> exists x, ~~ root p x.
Proof.
move=> p p0.
case sp1: (size p == 1%N).
  by move/size1P: sp1=> [x [x0 ->]]; exists x; rewrite rootC.
have: (size (1 + p) != 1%N).
  rewrite addrC size_addl ?sp1 //.
  move/negPf: p0 => p0f.
  rewrite size_poly1 ltnNge leq_eqVlt sp1.
  by move: p0f; rewrite -size_poly_eq0; case: size.
move/root_size_neq1 => [x rx]; exists x.
move: rx; rewrite rootE horner_add hornerC.
rewrite addrC -(inj_eq (@addIr _ (-1))) addrK sub0r rootE.
move/eqP->; rewrite eq_sym -(inj_eq (addrI 1)).
by rewrite addr0 subrr oner_eq0.
Qed.

End PolyDivPreClosedField.
End PolyDivPreClosedField.

Section PolyDivClosedFields.

(* Same thing with a proper ClosedField *)
Variable F : closedFieldType.

Lemma root_size_neq1 : forall p : {poly F},
  reflect (exists x, root p x) (size p != 1%N).
Proof. by apply: PolyDivPreClosedField.root_size_neq1; case: F=> [? []]. Qed.

Lemma ex_px_neq0 : forall p : {poly F}, p != 0 -> exists x, ~~ root p x.
Proof. by apply: PolyDivPreClosedField.ex_px_neq0; case: F=> [? []]. Qed.

End PolyDivClosedFields.



(* Failed attempts to automate rewrite with eqp using Setoid or CS *)
(* Section EqpRewriteTheory. *)

(* Variable R : idomainType. *)
(* Implicit Types x y c : R. *)
(* Implicit Types p q r d : {poly R}. *)

(* Inductive eqpT (R : idomainType) (p q : {poly R}) : Prop := *)
(*   EqpT : p %= q -> eqpT p q. *)

(* Lemma eqpP : forall (R : idomainType) (p q : {poly R}), reflect (eqpT p q) (p %= q). *)
(* Proof. by move=> R' p q; apply: (iffP idP)=> [|[]]. Qed. *)
(* Implicit Arguments eqpP [R p q]. *)

(* Require Import Relation_Definitions Setoid Morphisms. *)

(* Add Parametric Relation (R : idomainType) : {poly R} (@eqpT R) *)
(*   reflexivity proved by _ *)
(*   symmetry proved by _ *)
(*   transitivity proved by _ as eqp_rel. *)
(* Proof. *)
(* * by split; rewrite eqpxx. *)
(* * by split; rewrite eqp_sym; case: H. *)
(* * by split; move: H H0=> [hpq] [hqr]; apply: eqp_trans hqr. *)
(* Qed. *)

(* Add Parametric Morphism (R : idomainType) : (@eqp _) *)
(* with signature (@eqpT R ==> (@eqpT _ ==> (@eq _)))%signature as eqp_eqp. *)
(* Admitted. *)

(* Add Parametric Morphism (R : idomainType) : (@mul (poly_ringType (IntegralDomain.ringType R))) *)
(* with signature (@eqpT R ==> (@eqpT R ==>  @eqpT R))%signature as mulr_eqp. *)
(* Admitted. *)

(* Lemma toto : forall (R : idomainType), {poly R} -> {poly R} -> {poly R}. Admitted. *)

(* Add Parametric Morphism (R : idomainType) : (@toto _) *)
(* with signature (@eqpT R ==> (@eqpT _ ==> @eqpT _))%signature as toto_eqp. *)
(* Admitted. *)


(* Goal forall p q r, p %= q -> p * q %=  q. *)
(* Proof. *)
(* move=> p q r epq. *)
(* Set Printing All. *)
(* rewrite (eqpP epq). *)
(* (* rewrite -/(eqpT _ _)=> epq. *) *)
(* (* rewrite epq. *) *)


(* (* do 2!rewrite -/(eqpT _ _). *) *)
(* (* move=> epq. *) *)
(* (* rewrite epq. *) *)
(* (* rewrite epq. *) *)

(* (* Print Instances Proper. *) *)
(* (* Print TypeClasses. *) *)

(* (* setoid_rewrite (eqpP epq). *) *)
(* (* apply/eqpP. *) *)
(* (* rewrite (eqpP epq). *) *)
(* (* by move/eqpP:(epq)=> h; rewrite h. *) *)
(* (* rewrite (eqpP epq). *) *)


(* Section EqpMorph. *)
(* (* Quite useful : to refactor +  hide in a module + tactic with locking ? *) *)
(* Record eqp_to (q : {poly R}) : Type := EqpTo { *)
(*   eqp_left :> {poly R}; *)
(*   eqp_morphP : eqp_left %= q *)
(* }. *)

(* Notation "%= q" := (eqp_to q) (at level 10). *)

(* Definition eqpM : forall p q (epq : p %= q), (p = (EqpTo epq)). *)
(* Proof. done. Qed. *)

(* Lemma symeqp : forall p q, p %= q -> q %= p. *)
(* Proof. by move=> *; rewrite eqp_sym. Qed. *)

(* (* Lemma eqp_rightP : forall p q (epq : p %= q),  *) *)
(* (*   eqp_right (EqpMorph epq) = q. *) *)
(* (* Proof. done. Qed. *) *)

(* Lemma eqpM_dvdr : forall d p (q : %= p), d %| q = (d %| p). *)
(* Proof. by move=> d p [q epq] /=; apply: eqp_dvdr. Qed. *)

(* Lemma eqpM_dvdl : forall p (q : %= p) d, q %| d = (p %| d). *)
(* Proof. by move=> p [q epq] d /=; apply: eqp_dvdl. Qed. *)

(* Lemma eqpM_eqpr : forall d p (q : %= p),  d %= q = (d %= p). *)
(* Proof. by move=> d p [q epq] /=; apply: eqp_rtrans. Qed. *)

(* Lemma eqpM_eqpl : forall d p (q : %= p), q %= d = (p %= d). *)
(* Proof. by move=> d p [q epq] /=; apply: eqp_ltrans. Qed. *)

(* Lemma eqp_mulr : forall p q r, q %= r -> q * p %= r * p. *)
(* Proof. by move=> p q r qr; rewrite ![_*p]mulrC eqp_mull. Qed. *)

(* Lemma eqpM_mull : forall p r (q : %= r), *)
(*   p * q = (EqpTo (eqp_mull p (eqp_morphP q))). *)
(* Proof. done. Qed. *)

(* Lemma eqpM_mulr : forall r (p : %= r) q, *)
(*   (eqp_left p) * q = (EqpTo (eqp_mulr q (eqp_morphP p))). *)
(* Proof. done. Qed. *)

(* Lemma eqpM_size : forall q (p : %= q), size p = size q. *)
(* Proof. by move=> q [p eqp]; apply: size_eqp. Qed. *)

(* Definition eqpE' := (eqpM_mull, eqpM_mulr, eqpM_dvdr, eqpM_dvdl, *)
(*   eqpM_eqpr, eqpM_eqpl, eqpM_size). *)

(* Lemma eqp_gcdl : forall q r p, p %= r -> gcdp p q %= gcdp r q. *)
(* Proof. *)
(* move=> r p q pr; rewrite /eqp !dvdp_gcd. *)
(* rewrite (eqpM (symeqp pr)) !eqpE' dvdp_gcdl dvdp_gcdr /=. *)
(* by rewrite (eqpM pr) !eqpE' dvdp_gcdl dvdp_gcdr. *)
(* Qed. *)

(* Lemma eqpM_gcdl : forall r (p : %= r) q, *)
(*   gcdp p q = (EqpTo (eqp_gcdl q (eqp_morphP p))). *)
(* Proof. done. Qed. *)

(* Lemma eqp_gcdr : forall p r q, q %= r -> gcdp p q %= gcdp p r. *)
(* Proof.  *)
(* move=> p r q qr; rewrite (eqpM (gcdpC _ _)) !eqpE'. *)
(* by rewrite (eqpM (eqp_gcdl _ qr)) !eqpE' (eqpM (gcdpC _ _)) !eqpE' eqpxx. *)
(* Qed. *)

(* Lemma eqpM_gcdr : forall p r (q : %= r), *)
(*   gcdp p q = (EqpTo (eqp_gcdr p (eqp_morphP q))). *)
(* Proof. done. Qed. *)

(* Lemma eqp_exp : forall p q, p %= q -> forall n, p ^+ n %= q ^+ n. *)
(* Proof. *)
(* move=> p q pq; elim=> [|n ihn]; first by rewrite !expr0 eqpxx. *)
(* by rewrite !exprS; rewrite (eqpM pq) !eqpE'/= (eqpM ihn) !eqpE' eqpxx. *)
(* Qed. *)

(* Lemma eqpM_exp : forall r (p : %= r) n,  *)
(*   (eqp_left p) ^+ n = (EqpTo (eqp_exp (eqp_morphP p) n)). *)
(* Proof. done. Qed. *)

(* Definition eqpE'' := (eqpE', eqpM_gcdr, eqpM_gcdl, eqpM_exp). *)

(* Lemma eqpM_coprimel : forall r (p : %= r) q, coprimep p q = coprimep r q. *)
(* Proof. *)
(* move=> r [p pr] q; rewrite /coprimep /=. *)
(* by rewrite (eqpM pr) eqpE'' eqpE'. *)
(* Qed. *)

(* Lemma eqpM_coprimer : forall p r (q : %= r), coprimep p q = coprimep p r. *)
(* Proof. *)
(* move=> p r [q qr]; rewrite /coprimep /=. *)
(* by rewrite (eqpM qr) eqpE'' eqpE'. *)
(* Qed. *)

(* Definition eqpE''' := (eqpE'', eqpM_coprimel, eqpM_coprimer). *)

(* Definition eqpE p q (epq : p %= q) := (eqpM epq, eqpE'''). *)

(* Lemma eqWp : forall p q, p == q -> p %= q. *)
(* Proof. by move=> p q; move/eqP->; rewrite eqpxx. Qed. *)

(* End EqpMorph. *)

(* End EqpRewriteTheory. *)
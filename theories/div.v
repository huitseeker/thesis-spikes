(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(**************************************************************************)
(* This file deals with divisibility for natural numbers.                 *)
(* It contains the definitions of:                                        *)
(*      edivn m d   == the pair composed of the quotient and remainder    *)
(*                     of the euclidian division of m by d                *)
(*          m %/ d  == quotient of m by d                                 *)
(*          m %% d  == remainder of m dy d                                *)
(*  m = n %[mod d]  <=> m equals n modulo d                               *)
(*  m == n %[mod d] <=> m equals n modulo d (boolean version)             *)
(*  m <> n %[mod d] <=> m differs from n modulo d                         *)
(*  m != n %[mod d] <=> m differs from n modulo d (boolean version)       *)
(*           d %| m <=> d divides m                                       *)
(*         gcdn m n == the GCD of m and n                                 *)
(*        egcdn m n == the extended GCD of m and n                        *)
(*         lcmn m n == the LCM of m and n                                 *)
(*      coprime m n <=> m and n are coprime                               *)
(*  chinese m n r s == witness of the chinese remainder theorem           *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Euclidian division *)

Definition edivn_rec d := fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).

CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => [// | le_dm].
rewrite -{1}(subnKC le_dm) -addSn addnA -mulSnr; apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_gt0: 0 < d by exact: leq_trans lt_rd.
case: edivnP lt_rd => q' r'; rewrite d_gt0 /=.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
rewrite -(leq_pmul2r d_gt0); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.

Definition divn m d := (edivn m d).1.

Notation "m %/ d" := (divn m d) : nat_scope.

(* We redefine modn so that it is structurally decreasing. *)

Definition modn_rec d := fix loop (m : nat) :=
  if m - d is m'.+1 then loop m' else m.

Definition modn m d := if d > 0 then modn_rec d.-1 m else m.

Notation "m %% d" := (modn m d) : nat_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : nat_scope.
Notation "m == n %[mod d ]" := (m %% d == n %% d) : nat_scope.
Notation "m <> n %[mod d ]" := (m %% d <> n %% d) : nat_scope.
Notation "m != n %[mod d ]" := (m %% d != n %% d) : nat_scope.

Lemma modn_def : forall m d, m %% d = (edivn m d).2.
Proof.
rewrite /modn /edivn => m [|d] //=.
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=.
rewrite ltnS !subn_if_gt; case: (d <= m) => // le_mn.
by apply: IHn; apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_def : forall m d, edivn m d = (m %/ d, m %% d).
Proof. by move=> m d; rewrite /divn modn_def; case edivn. Qed.

Lemma divn_eq : forall m d, m = m %/ d * d + m %% d.
Proof. by move=> m d; rewrite /divn modn_def; case edivnP. Qed.

Lemma div0n : forall d, 0 %/ d = 0. Proof. by case. Qed.
Lemma divn0 : forall m, m %/ 0 = 0. Proof.  by []. Qed.
Lemma mod0n :  forall d, 0 %% d = 0. Proof. by case. Qed.
Lemma modn0 :  forall m, m %% 0 = m. Proof. by []. Qed.

Lemma divn_small : forall m d, m < d -> m %/ d = 0.
Proof. by move=> m d lt_md; rewrite /divn (edivn_eq 0). Qed.

Lemma divn_addl_mul : forall q m d, 0 < d -> (q * d + m) %/ d = q + m %/ d.
Proof.
move=> q m d d_gt0; rewrite {1}(divn_eq m d) addnA -muln_addl.
by rewrite /divn edivn_eq // modn_def; case: edivnP; rewrite d_gt0.
Qed.

Lemma mulnK : forall m d, 0 < d -> m * d %/ d = m.
Proof.
by move=> m d d_gt0; rewrite -[m * d]addn0 divn_addl_mul // div0n addn0.
Qed.

Lemma mulKn : forall m d, 0 < d -> d * m %/ d = m.
Proof. by move=> *; rewrite mulnC mulnK. Qed.

Lemma expn_sub : forall p m n,
   p > 0 -> m >= n -> (p ^ (m - n))%N = p ^ m %/ p ^ n.
Proof.
move=> p m n p_gt0 n_le_m.
by rewrite -{2}(subnK n_le_m) expn_add mulnK // expn_gt0 p_gt0.
Qed.

Lemma modn1 : forall m, m %% 1 = 0.
Proof. by move=> m; rewrite modn_def; case: edivnP => ? []. Qed.

Lemma divn1 : forall m, m %/ 1 = m.
Proof. by move=> m; rewrite {2}(@divn_eq m 1) // modn1 addn0 muln1. Qed.

Lemma divnn : forall d, d %/ d = (0 < d).
Proof. by case=> // d; rewrite -{1}[d.+1]muln1 mulKn. Qed.

Lemma divn_pmul2l : forall p m d, p > 0 -> p * m %/ (p * d) = m %/ d.
Proof.
move=> p m d p_gt0; case: (posnP d) => [-> | d_gt0]; first by rewrite muln0.
rewrite {2}/divn; case: edivnP; rewrite d_gt0 /= => q r ->{m} lt_rd.
rewrite muln_addr mulnCA divn_addl_mul; last by rewrite muln_gt0 p_gt0.
by rewrite addnC divn_small // ltn_pmul2l.
Qed.
Implicit Arguments divn_pmul2l [p m d].

Lemma divn_pmul2r : forall p m d, p > 0 -> m * p %/ (d * p) = m %/ d.
Proof. by move=> p m d p_gt0; rewrite -!(mulnC p) divn_pmul2l. Qed.
Implicit Arguments divn_pmul2r [p m d].

Lemma ltn_mod : forall m d, (m %% d < d) = (0 < d).
Proof. by move=> m [|d] //; rewrite modn_def; case: edivnP. Qed.

Lemma ltn_pmod : forall m d, 0 < d -> m %% d < d.
Proof. by move=> m d; rewrite ltn_mod. Qed.

Lemma leq_floor : forall m d, m %/ d * d <= m.
Proof. by move=> m d; rewrite {2}(divn_eq m d) leq_addr. Qed.

Lemma leq_mod : forall m d, m %% d  <= m.
Proof. by move=> m d; rewrite {2}(divn_eq m d) leq_addl. Qed.

Lemma leq_div : forall m d, m %/ d <= m.
Proof. move=> m [|d] //; exact: leq_trans (leq_pmulr _ _) (leq_floor _ _). Qed.

Lemma ltn_ceil : forall m d, 0 < d -> m < (m %/ d).+1 * d.
Proof.
by move=> m d ? /=; rewrite {1}(divn_eq m d) -addnS mulSnr leq_add2l ltn_mod.
Qed.

Lemma ltn_divl : forall m n d, d > 0 -> (m %/ d < n) = (m < n * d).
Proof.
move=> m n d d_gt0; apply/idP/idP.
  rewrite -(leq_pmul2r d_gt0); exact: leq_trans (ltn_ceil _ _).
rewrite !ltnNge -(@leq_pmul2r d n) //; apply: contra => le_nd_floor.
exact: leq_trans le_nd_floor (leq_floor _ _).
Qed.

Lemma leq_divr : forall m n d, d > 0 -> (m <= n %/ d) = (m * d <= n).
Proof. by move=> m n d d_gt0; rewrite leqNgt ltn_divl // -leqNgt. Qed.

Lemma ltn_Pdiv : forall m d, 1 < d -> 0 < m -> m %/ d < m.
Proof. by move=> m d d_gt1 m_gt0; rewrite ltn_divl ?ltn_Pmulr // ltnW. Qed.

Lemma divn_gt0 : forall d m, 0 < d -> (0 < m %/ d) = (d <= m).
Proof. by move=> d m d_gt0; rewrite leq_divr ?mul1n. Qed.

Lemma divn_divl : forall m n p, m %/ n %/ p = m %/ (n * p).
Proof.
move=> m [|n] [|p]; rewrite ?muln0 ?div0n //.
rewrite {1}(divn_eq m (n.+1 * p.+1)) mulnA mulnAC !divn_addl_mul //.
by rewrite addnC divn_small // ltn_divl // mulnC ltn_mod.
Qed.

Lemma divnAC : forall m n p, m %/ n %/ p =  m %/ p %/ n.
Proof. by move=> m n p; rewrite !divn_divl mulnC. Qed.

Lemma modn_small : forall m d, m < d -> m %% d = m.
Proof. by move=> m d lt_md; rewrite {2}(divn_eq m d) divn_small. Qed.

Lemma modn_mod : forall m d, m %% d = m %[mod d].
Proof. by move=> m [|d] //; apply: modn_small; rewrite ltn_mod. Qed.

Lemma modn_addl_mul : forall p m d, p * d + m = m %[mod d].
Proof.
move=> p m d; case: (posnP d) => [-> | d_gt0]; first by rewrite muln0.
by rewrite {1}(divn_eq m d) addnA -muln_addl modn_def edivn_eq // ltn_mod.
Qed.

Lemma modn_pmul2l : forall p m d, 0 < p -> p * m %% (p * d) = p * (m %% d).
Proof.
move=> p m d p_gt0; apply: (@addnI (p * (m %/ d * d))).
by rewrite -muln_addr -divn_eq mulnCA -(divn_pmul2l p_gt0) -divn_eq.
Qed.
Implicit Arguments modn_pmul2l [p m d].

Lemma modn_addl : forall m d, d + m = m %[mod d].
Proof. by move=> m d; rewrite -{1}[d]mul1n modn_addl_mul. Qed.

Lemma modn_addr : forall m d, m + d = m %[mod d].
Proof. by move=> *; rewrite addnC modn_addl. Qed.

Lemma modnn : forall d, d %% d = 0.
Proof. by move=> d; rewrite -{1}[d]addn0 modn_addl mod0n. Qed.

Lemma modn_mull : forall p d, p * d %% d = 0.
Proof. by move=> p d; rewrite -[p * d]addn0 modn_addl_mul mod0n. Qed.

Lemma modn_mulr : forall p d, d * p %% d = 0.
Proof. by move=> p d; rewrite mulnC modn_mull. Qed.

Lemma modn_addml : forall m n d, m %% d + n = m + n %[mod d].
Proof. by move=> m n d; rewrite {2}(divn_eq m d) -addnA modn_addl_mul. Qed.

Lemma modn_addmr : forall m n d, m + n %% d = m + n %[mod d].
Proof. by move=> m n d; rewrite !(addnC m) modn_addml. Qed.

Lemma modn_add2m : forall m n d, m %% d  + n %% d = m + n %[mod d].
Proof. by move=> m n d; rewrite modn_addml modn_addmr. Qed.

Lemma modn_add2l : forall p m n d,
  (p + m == p + n %[mod d]) = (m == n %[mod d]).
Proof.
move=> p m n [|d]; first by rewrite !modn0 eqn_addl.
apply/eqP/eqP=> eq_mn; last by rewrite -modn_addmr eq_mn modn_addmr.
rewrite -(modn_addl_mul p m) -(modn_addl_mul p n) !mulnSr -!addnA.
by rewrite -modn_addmr eq_mn modn_addmr.
Qed.

Lemma modn_add2r : forall p m n d,
  (m + p == n + p %[mod d]) = (m == n %[mod d]).
Proof. by move=> p *; rewrite -!(addnC p) modn_add2l. Qed.

Lemma modn_mulml : forall m n d, m %% d * n = m * n %[mod d].
Proof.
by move=> m n d; rewrite {2}(divn_eq m d) muln_addl mulnAC modn_addl_mul.
Qed.

Lemma modn_mulmr : forall m n d, m * (n %% d) = m * n %[mod d].
Proof. by move=> m n d; rewrite !(mulnC m) modn_mulml. Qed.

Lemma modn_mul2m : forall m n d, m %% d * (n %% d) = m * n %[mod d].
Proof. by move=> m n d; rewrite modn_mulml modn_mulmr. Qed.

Lemma modn2 : forall m, m %% 2 = odd m.
Proof. by elim=> //= m IHm; rewrite -addn1 -modn_addml IHm; case odd. Qed.

Lemma divn2 : forall m, m %/ 2 = m./2.
Proof.
by move=> m; rewrite {2}(divn_eq m 2) modn2 muln2 addnC half_bit_double.
Qed.

Lemma odd_mod : forall m d, odd d = false -> odd (m %% d) = odd m.
Proof.
by move=> m d d_even; rewrite {2}(divn_eq m d) odd_add odd_mul d_even andbF.
Qed.

Lemma modn_exp : forall m n a, (a %% n) ^ m = a ^ m %[mod n].
Proof.
by elim=> // m Hrec n a; rewrite !expnS -modn_mulmr Hrec modn_mulml modn_mulmr.
Qed.

(** Divisibility **)

Definition dvdn d m := m %% d == 0.

Notation "m %| d" := (dvdn m d) : nat_scope.

Definition multn := [rel m d | d %| m].

Lemma dvdnP : forall d m, reflect (exists k, m = k * d) (d %| m).
Proof.
move=> d m; apply: (iffP eqP) => [Hm | [k ->]]; last by rewrite modn_mull.
by exists (m %/ d); rewrite {1}(divn_eq m d) Hm addn0.
Qed.
Implicit Arguments dvdnP [d m].
Prenex Implicits dvdnP.

Lemma dvdn0 : forall d, d %| 0.
Proof. by case. Qed.

Lemma dvd0n : forall n, (0 %| n) = (n == 0).
Proof. by case. Qed.

Lemma dvdn1 : forall d, (d %| 1) = (d == 1).
Proof. by case=> [|[|n]] //; rewrite /dvdn modn_small. Qed.

Lemma dvd1n : forall m, 1 %| m.
Proof. by move=> m; rewrite /dvdn modn1. Qed.

Lemma dvdn_gt0 : forall d m, m > 0 -> d %| m -> d > 0.
Proof. by do 2!case. Qed.

Lemma dvdnn : forall m, m %| m.
Proof. by move=> m; rewrite /dvdn modnn. Qed.

Lemma dvdn_mull : forall d m n, d %| n -> d %| m * n.
Proof. by move=> d m n; case/dvdnP=> n' ->; rewrite /dvdn mulnA modn_mull. Qed.

Lemma dvdn_mulr : forall d m n, d %| m -> d %| m * n.
Proof. by move=> d m n d_m; rewrite mulnC dvdn_mull. Qed.

Hint Resolve dvdn0 dvd1n dvdnn dvdn_mull dvdn_mulr.

Lemma dvdn_mul : forall d1 d2 m1 m2, d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
move=> d1 d2 m1 m2; case/dvdnP=> q1 ->; case/dvdnP=> q2 ->.
by rewrite mulnCA -mulnA 2?dvdn_mull.
Qed.

Lemma dvdn_trans : forall n d m, d %| n -> n %| m -> d %| m.
Proof. by move=> n d m Hn; move/dvdnP => [n1 ->]; exact: dvdn_mull. Qed.

Lemma dvdn_eq : forall d m, (d %| m) = (m %/ d * d == m).
Proof.
move=> d m; apply/eqP/eqP=> [modm0 | <-]; last exact: modn_mull.
by rewrite {2}(divn_eq m d) modm0 addn0.
Qed.

Lemma dvdn2 : forall n, (2 %| n) = ~~ odd n.
Proof. by move=> n; rewrite /dvdn modn2; case (odd n). Qed.

Lemma dvdn_odd : forall m n, m %| n -> odd n -> odd m.
Proof.
by move=> m n m_dv_n; apply: contraTT; rewrite -!dvdn2; move/dvdn_trans->.
Qed.

Lemma divnK : forall d m, d %| m -> m %/ d * d = m.
Proof. by move=> m d; rewrite dvdn_eq; move/eqP. Qed.

Lemma leq_divl : forall d m n, d %| m -> (m %/ d <= n) = (m <= n * d).
Proof. by case=> [[]//|d] m n dv_d_m; rewrite -(@leq_pmul2r d.+1) ?divnK. Qed.

Lemma ltn_divr : forall d m n, d %| m -> (n < m %/ d) = (n * d < m).
Proof. by move=> d m n dv_d_m; rewrite !ltnNge leq_divl. Qed.

Lemma eqn_div : forall d m n, d > 0 -> d %| m -> (n == m %/ d) = (n * d == m).
Proof. by move=> d m n d_gt0 dv_d_m; rewrite -(eqn_pmul2r d_gt0) divnK. Qed.

Lemma eqn_mul : forall d m n, d > 0 -> d %| m -> (m == n * d) = (m %/ d == n).
Proof. by move=> d m n d_gt0 dv_d_m; rewrite eq_sym -eqn_div // eq_sym. Qed.

Lemma divn_mulAC : forall d m n, d %| m -> m %/ d * n = m * n %/ d.
Proof.
case=> [[]//|d] m n dv_d_m; apply/eqP.
by rewrite eqn_div ?dvdn_mulr // mulnAC divnK.
Qed.

Lemma divn_mulA : forall d m n, d %| n -> m * (n %/ d) = m * n %/ d.
Proof. by move=> d m n dv_d_m; rewrite !(mulnC m) divn_mulAC. Qed.

Lemma divn_mulCA : forall d m n,
  d %| m -> d %| n -> m * (n %/ d) = n * (m %/ d).
Proof. by move=> d m n dv_d_m dv_d_n; rewrite mulnC divn_mulAC ?divn_mulA. Qed.

Lemma divn_divr : forall m n p, p %| n -> m %/ (n %/ p) = m * p %/ n.
Proof. by move=> m n [|p] dv_n; rewrite -{2}(divnK dv_n) // divn_pmul2r. Qed.

Lemma modn_dvdm : forall m n d, d %| m -> n %% m = n %[mod d].
Proof.
move=> m n d; case/dvdnP=> q def_m.
by rewrite {2}(divn_eq n m) {3}def_m mulnA modn_addl_mul.
Qed.

Lemma dvdn_leq : forall d m, 0 < m -> d %| m -> d <= m.
Proof.
by move=> d m m_gt0; case/dvdnP=> [[|k] Dm]; rewrite Dm // leq_addr in m_gt0 *.
Qed.

Lemma gtnNdvd : forall n d, 0 < n -> n < d -> (d %| n) = false.
Proof. by move=> n d n_gt0 ltnd; rewrite /dvdn eqn0Ngt modn_small ?n_gt0. Qed.

Lemma eqn_dvd : forall m n, (m == n) = (m %| n) && (n %| m).
Proof.
case=> [|m] [|n] //; apply/idP/andP; first by move/eqP->; auto.
rewrite eqn_leq => [[Hmn Hnm]]; apply/andP; have:= dvdn_leq; auto.
Qed.

Lemma dvdn_pmul2l : forall p d m, 0 < p -> (p * d %| p * m) = (d %| m).
Proof. by case=> // p d m _; rewrite /dvdn modn_pmul2l // muln_eq0. Qed.
Implicit Arguments dvdn_pmul2l [p m d].

Lemma dvdn_pmul2r : forall p d m, 0 < p -> (d * p %| m * p) = (d %| m).
Proof. by move=> n d m Hn; rewrite -!(mulnC n) dvdn_pmul2l. Qed.
Implicit Arguments dvdn_pmul2r [p m d].

Lemma dvdn_exp2l : forall p m n, m <= n -> p ^ m %| p ^ n.
Proof. by move=> p m n; move/subnK <-; rewrite expn_add dvdn_mull. Qed.

Lemma dvdn_Pexp2l : forall p m n, p > 1 -> (p ^ m %| p ^ n) = (m <= n).
Proof.
move=> p m n p_gt1; case: leqP => [|gt_n_m]; first exact: dvdn_exp2l.
by rewrite gtnNdvd ?ltn_exp2l ?expn_gt0 // ltnW.
Qed.

Lemma dvdn_exp2r : forall m n k, m %| n -> m ^ k %| n ^ k.
Proof. by move=> m n k; case/dvdnP=> q ->; rewrite expn_mull dvdn_mull. Qed.

Lemma dvdn_addr : forall m d n, d %| m -> (d %| m + n) = (d %| n).
Proof. by move=> n d m; move/dvdnP=> [k ->]; rewrite /dvdn modn_addl_mul. Qed.

Lemma dvdn_addl : forall n d m, d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addnC; exact: dvdn_addr. Qed.

Lemma dvdn_add : forall d m n, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdn_addr->. Qed.

Lemma dvdn_add_eq : forall d m n, d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdn_addr <-| move/dvdn_addl <-]. Qed.

Lemma dvdn_subr : forall d m n, n <= m -> d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> d m n le_n_m dv_d_m; apply: dvdn_add_eq; rewrite subnK. Qed.

Lemma dvdn_subl : forall d m n, n <= m -> d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n le_n_m dv_d_m; rewrite -(dvdn_addl _ dv_d_m) subnK. Qed.

Lemma dvdn_sub : forall d m n, d %|m -> d %| n -> d %| m - n.
Proof.
move=> d n m; case: (leqP m n) => Hm; first by move/dvdn_subr <-.
by rewrite (eqnP (ltnW Hm)) dvdn0.
Qed.

Lemma dvdn_exp : forall k d m, 0 < k -> d %| m -> d %| (m ^ k).
Proof. by case=> // *; rewrite expnS dvdn_mulr. Qed.

Hint Resolve dvdn_add dvdn_sub dvdn_exp.

Lemma eqn_mod_dvd : forall d m n, n <= m -> (m == n %[mod d]) = (d %| m - n).
Proof.
by move=> d m n le_mn; rewrite -{1}[n]add0n -{1}(subnK le_mn) modn_add2r mod0n.
Qed.

Lemma divn_addl : forall m n d, d %| m -> (m + n) %/ d = m %/ d + n %/ d.
Proof. by move=> m n [//|d] dv_m; rewrite -{1}(divnK dv_m) divn_addl_mul. Qed.

Lemma divn_addr : forall m n d, d %| n -> (m + n) %/ d = m %/ d + n %/ d.
Proof. by move=> m n d dv_n; rewrite addnC divn_addl // addnC. Qed.

(***********************************************************************)
(*   A function that computes the gcd of 2 numbers                     *)
(***********************************************************************)

Fixpoint gcdn_rec (m n : nat) {struct m} :=
  let n' := n %% m in if n' is 0 then m else
  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'.

Definition gcdn := nosimpl gcdn_rec.

Lemma gcdnE : forall m n, gcdn m n = if m == 0 then n else gcdn (n %% m) m.
Proof.
rewrite /gcdn => m; elim: m {-2}m (leqnn m) => [|s IHs] [|m] le_ms [|n] //=.
case def_n': (_ %% _) => // [n'].
have{def_n'} lt_n'm: n' < m by rewrite -def_n' -ltnS ltn_pmod.
rewrite {}IHs ?(leq_trans lt_n'm) // subn_if_gt ltnW //=; congr gcdn_rec.
by rewrite -{2}(subnK (ltnW lt_n'm)) -addnS modn_addr.
Qed.

Lemma gcdnn : idempotent gcdn.
Proof. by case=> // n; rewrite gcdnE modnn. Qed.

Lemma gcdnC : commutative gcdn.
Proof.
move=> m n; wlog lt_nm: m n / n < m.
  by case: (ltngtP n m) => [||->]; [|symmetry|rewrite gcdnn]; auto.
by rewrite gcdnE -{1}(ltn_predK lt_nm) modn_small.
Qed.

Lemma gcd0n : left_id 0 gcdn. Proof. by case. Qed.
Lemma gcdn0 : right_id 0 gcdn. Proof. by case. Qed.

Lemma gcd1n : left_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnE modn1. Qed.

Lemma gcdn1 : right_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnC gcd1n. Qed.

Lemma dvdn_gcdr : forall m n, gcdn m n %| n.
Proof.
move=> m; elim: m {-2}m (leqnn m) => [|s IHs] [|m] le_ms [|n] //.
rewrite gcdnE; case def_n': (_ %% _) => [|n']; first by rewrite /dvdn def_n'.
have lt_n's: n' < s by rewrite -ltnS (leq_trans _ le_ms) // -def_n' ltn_pmod.
rewrite /= (divn_eq n.+1 m.+1) def_n' dvdn_addr ?dvdn_mull //; last exact: IHs.
by rewrite gcdnE /= IHs // (leq_trans _ lt_n's) // ltnW // ltn_pmod.
Qed.

Lemma dvdn_gcdl : forall m n, gcdn m n %| m.
Proof. by move=> m n; rewrite gcdnC dvdn_gcdr. Qed.

Lemma gcdn_gt0 : forall m n, (0 < gcdn m n) = (0 < m) || (0 < n).
Proof.
move=> [|m] [|n] //; apply: (@dvdn_gt0 _ m.+1) => //; exact: dvdn_gcdl.
Qed.

Lemma gcdn_addl_mul : forall k m n, gcdn m (k * m + n) = gcdn m n.
Proof. by move=> k m n; rewrite !(gcdnE m) modn_addl_mul mulnC; case: m. Qed.

Lemma gcdn_addl : forall m n, gcdn m (m + n) = gcdn m n.
Proof. by move => m n; rewrite -{2}(mul1n m) gcdn_addl_mul. Qed.

Lemma gcdn_addr : forall m n, gcdn m (n + m) = gcdn m n.
Proof. by move=> m n; rewrite addnC gcdn_addl. Qed.

Lemma gcdn_mull : forall n m, gcdn n (m * n) = n.
Proof. by case=> [|n] m; rewrite gcdnE modn_mull gcd0n. Qed.

Lemma gcdn_mulr : forall n m, gcdn n (n * m) = n.
Proof. by move=> n m; rewrite mulnC gcdn_mull. Qed.

Lemma dvdn_gcd_idl : forall m n, m %| n -> gcdn m n = m.
Proof. by move=> m n; case/dvdnP=> q ->; rewrite gcdn_mull. Qed.

Lemma dvdn_gcd_idr : forall m n, n %| m -> gcdn m n = n.
Proof. move=> m n; rewrite gcdnC; exact: dvdn_gcd_idl. Qed.

Lemma gcdn_exp : forall e m n, gcdn (e ^ m) (e ^ n) = e ^ minn m n.
Proof.
rewrite /minn => e m n; case: leqP; [rewrite gcdnC | move/ltnW];
 by move/(dvdn_exp2l e); exact: dvdn_gcd_idl.
Qed.

(* Extended gcd, which computes Bezout coefficients. *)

Fixpoint bezout_rec (km kn : nat) (qs : seq nat) {struct qs} :=
  if qs is q :: qs' then bezout_rec kn (NatTrec.add_mul q kn km) qs'
  else (km, kn).

Fixpoint egcdn_rec (m n s : nat) (qs : seq nat) {struct s} :=
  if s is s'.+1 then
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_rec n r s' (q :: qs) else
    if odd (size qs) then qs else q.-1 :: qs
  else [::0].

Definition egcdn m n := bezout_rec 0 1 (egcdn_rec m n n [::]).

CoInductive egcdn_spec (m n : nat) : nat * nat -> Type :=
  EgcdnSpec km kn of km * m = kn * n + gcdn m n & kn * gcdn m n < m :
    egcdn_spec m n (km, kn).

Lemma egcd0n : forall n, egcdn 0 n = (1, 0).
Proof. by case. Qed.

Lemma egcdnP : forall m n, m > 0 -> egcdn_spec m n (egcdn m n).
Proof.
rewrite /egcdn => m0 n0; have: (n0, m0) = bezout_rec n0 m0 [::] by [].
case: (posnP n0) => [-> /=|]; first by split; rewrite // mul1n gcdn0.
elim: {1 4}n0 {1 3 5 7}n0 {-1 4}m0 [::] (ltnSn n0) => [[]//|s IHs] n m qs /=.
move=> le_ns n_gt0 def_mn0 m_gt0.
case: edivnP => q r def_m; rewrite n_gt0 /= => lt_rn.
case: posnP => [r0 {s le_ns IHs lt_rn}|r_gt0]; last first.
  by apply: IHs => //=; [rewrite (leq_trans lt_rn) | rewrite natTrecE -def_m].
rewrite {r}r0 addn0 in def_m; set b := odd _; pose d := gcdn m n.
pose km := ~~ b : nat; pose kn := if b then 1 else q.-1.
rewrite (_ : bezout_rec _ _ _ = bezout_rec km kn qs); last first.
  by rewrite /kn /km; case b => //=; rewrite natTrecE addn0 muln1.
have def_d: d = n by rewrite /d def_m gcdnC gcdnE modn_mull gcd0n -[n]prednK.
have: km * m + 2 * b * d = kn * n + d.
  rewrite {}/kn {}/km def_m def_d -mulSnr; case: b; rewrite //= addn0 mul1n.
  by rewrite prednK //; apply: dvdn_gt0 m_gt0 _; rewrite def_m dvdn_mulr.
have{def_m}: kn * d <= m.
  have q_gt0 : 0 < q by rewrite def_m muln_gt0 n_gt0 ?andbT in m_gt0.
  by rewrite /kn; case b; rewrite def_d def_m leq_pmul2r // leq_pred.
have{def_d}: km * d <= n by rewrite -[n]mul1n def_d leq_pmul2r // leq_b1.
move: km {q}kn m_gt0 n_gt0 def_mn0; rewrite {}/d {}/b.
elim: qs m n => [|q qs IHq] n r kn kr n_gt0 r_gt0 /=.
  case=> -> -> {m0 n0}; rewrite !addn0 => le_kn_r _ def_d; split=> //.
  have d_gt0: 0 < gcdn n r by rewrite gcdn_gt0 n_gt0.
  have: 0 < kn * n by rewrite def_d addn_gt0 d_gt0 orbT.
  rewrite muln_gt0 n_gt0 andbT; move/ltn_pmul2l <-.
  by rewrite def_d -addn1 leq_add // mulnCA leq_mul2l le_kn_r orbT.
rewrite !natTrecE; set m:= _ + r; set km := _ * _ + kn; pose d := gcdn m n.
have ->: gcdn n r = d by rewrite [d]gcdnC gcdn_addl_mul.
have m_gt0: 0 < m by rewrite addn_gt0 r_gt0 orbT.
have d_gt0: 0 < d by rewrite gcdn_gt0 m_gt0.
move/IHq=> {IHq} IHq le_kn_r le_kr_n def_d; apply: IHq => //; rewrite -/d.
  by rewrite muln_addl leq_add // -mulnA leq_mul2l le_kr_n orbT.
apply: (@addIn d); rewrite -!addnA addnn addnCA muln_addr -addnA addnCA.
rewrite /km muln_addl mulnCA mulnA -addnA; congr (_ + _).
by rewrite -def_d addnC -addnA -muln_addl -muln_addr addn_negb -mul2n.
Qed.

Lemma bezoutl : forall m n, m > 0 -> {a | a < m & m %| gcdn m n + a * n}.
Proof.
move=> m n m_gt0; case: (egcdnP n m_gt0) => km kn def_d lt_kn_m.
exists kn; last by rewrite addnC -def_d dvdn_mull.
apply: leq_ltn_trans lt_kn_m.
by rewrite -{1}[kn]muln1 leq_mul2l gcdn_gt0 m_gt0 orbT.
Qed.

Lemma bezoutr : forall m n, n > 0 -> {a | a < n & n %| gcdn m n + a * m}.
Proof. by move=> m n; rewrite gcdnC; exact: bezoutl. Qed.

(* Back to the gcd. *)

Lemma dvdn_gcd : forall p m n, p %| gcdn m n = (p %| m) && (p %| n).
Proof.
move=> p m n; apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite ?(dvdn_trans dv_pmn) ?dvdn_gcdl ?dvdn_gcdr.
case (posnP n) => [->|n_gt0]; first by rewrite gcdn0.
case: (bezoutr m n_gt0) => // km _; move/(dvdn_trans dv_pn).
by rewrite dvdn_addl // dvdn_mull.
Qed.

Lemma gcdn_mul2l : forall p m n, gcdn (p * m) (p * n) = p * gcdn m n.
Proof.
move=> p m n; case: (posnP p) => [-> //| p_gt0].
elim: {m}m.+1 {-2}m n (ltnSn m) => // s IHs m n; rewrite ltnS => le_ms.
rewrite gcdnE (gcdnE m) muln_eq0 modn_pmul2l // eqn0Ngt p_gt0.
case: posnP => // m_gt0; apply: IHs; apply: leq_trans le_ms.
exact: ltn_pmod.
Qed.

Lemma gcdn_modr : forall m n, gcdn m (n %% m) = gcdn m n.
Proof. by move=> m n; rewrite {2}(divn_eq n m) gcdn_addl_mul. Qed.

Lemma gcdn_modl : forall m n, gcdn (m %% n) n = gcdn m n.
Proof. by move=> m n; rewrite !(gcdnC _ n) gcdn_modr. Qed.

Lemma gcdnAC : right_commutative gcdn.
Proof.
suff dvd: forall m n p, gcdn (gcdn m n) p %| gcdn (gcdn m p) n.
  by move=> m n p; apply/eqP; rewrite eqn_dvd !dvd.
move=> m n p; rewrite !dvdn_gcd dvdn_gcdr.
by rewrite !(dvdn_trans (dvdn_gcdl _ p)) ?dvdn_gcdl ?dvdn_gcdr.
Qed.

Lemma gcdnA : associative gcdn.
Proof. by move=> m n p; rewrite !(gcdnC m) gcdnAC. Qed.

Lemma gcdnCA : left_commutative gcdn.
Proof. by move=> m n p; rewrite !gcdnA (gcdnC m). Qed.

Lemma muln_gcdl : left_distributive muln gcdn.
Proof. by move=> m n p; rewrite -!(mulnC p) gcdn_mul2l. Qed.

Lemma muln_gcdr : right_distributive muln gcdn.
Proof. by move=> m n p; rewrite gcdn_mul2l. Qed.

Lemma gcdn_def : forall d m n,
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d)
  -> gcdn m n = d.
Proof.
move=> d m n dv_dm dv_dn gdv_d; apply/eqP.
by rewrite eqn_dvd dvdn_gcd dv_dm dv_dn gdv_d ?dvdn_gcdl ?dvdn_gcdr.
Qed.

Lemma gcdn_divnC : forall n m, n * (m %/ gcdn n m)  = m * (n %/ gcdn n m).
Proof. by move=> n m; rewrite divn_mulCA ?dvdn_gcdl ?dvdn_gcdr. Qed.

(* We derive the lcm directly. *)

Definition lcmn m n := m * n %/ gcdn m n.

Lemma lcmnC : commutative lcmn.
Proof. by move=> m n; rewrite /lcmn mulnC gcdnC. Qed.

Lemma lcm0n : left_zero 0 lcmn. Proof. move=> n; exact: div0n. Qed.
Lemma lcmn0 : right_zero 0 lcmn. Proof. by move=> n; rewrite lcmnC lcm0n. Qed.

Lemma lcm1n : left_id 1 lcmn.
Proof. by move=> n; rewrite /lcmn gcd1n mul1n divn1. Qed.

Lemma lcmn1 : right_id 1 lcmn.
Proof. by move=> n; rewrite lcmnC lcm1n. Qed.

Lemma muln_lcm_gcd : forall m n, lcmn m n * gcdn m n = m * n.
Proof. by move=> m n; apply/eqP; rewrite divnK ?dvdn_mull ?dvdn_gcdr. Qed.

Lemma lcmn_gt0 : forall m n, (0 < lcmn m n) = (0 < m) && (0 < n).
Proof. by move=> m n; rewrite -muln_gt0 ltn_divr ?dvdn_mull ?dvdn_gcdr. Qed.

Lemma muln_lcmr : right_distributive muln lcmn.
Proof.
case=> // m n p; rewrite /lcmn -muln_gcdr -!mulnA divn_pmul2l // mulnCA.
by rewrite divn_mulA ?dvdn_mull ?dvdn_gcdr.
Qed.

Lemma muln_lcml : left_distributive muln lcmn.
Proof. by move=> m n p; rewrite -!(mulnC p) muln_lcmr. Qed.

Lemma lcmnA : associative lcmn.
Proof.
move=> m n p; rewrite {1 3}/lcmn mulnC !divn_mulAC ?dvdn_mull ?dvdn_gcdr //.
rewrite !divn_divl ?dvdn_mulr ?dvdn_gcdl // mulnC mulnA !muln_gcdr.
by rewrite ![_ * lcmn _ _]mulnC !muln_lcm_gcd !muln_gcdl -!(mulnC m) gcdnA.
Qed.

Lemma dvdn_lcml : forall d1 d2, d1 %| lcmn d1 d2.
Proof. by move=> d1 d2; rewrite /lcmn -divn_mulA ?dvdn_gcdr ?dvdn_mulr. Qed.

Lemma dvdn_lcmr : forall d1 d2, d2 %| lcmn d1 d2.
Proof. by move=> d1 d2; rewrite lcmnC dvdn_lcml. Qed.

Lemma dvdn_lcm : forall d1 d2 m, lcmn d1 d2 %| m = (d1 %| m) && (d2 %| m).
Proof.
case=> [|d1] [|d2] m; try by case: m => [|m]; rewrite ?lcmn0 ?andbF.
rewrite -(@dvdn_pmul2r (gcdn d1.+1 d2.+1)) ?gcdn_gt0 // muln_lcm_gcd.
by rewrite muln_gcdr dvdn_gcd {1}mulnC andbC !dvdn_pmul2r.
Qed.

Lemma lcmn_mull : forall m n, lcmn m (m * n) = m * n.
Proof. by case=> // m n; rewrite /lcmn gcdn_mulr mulKn. Qed.

Lemma lcmn_mulr : forall m n, lcmn n (m * n) = m * n.
Proof. by move=> m n; rewrite mulnC lcmn_mull. Qed.

Lemma dvdn_lcm_idr : forall m n, m %| n -> lcmn m n = n.
Proof. by move=> m n; case/dvdnP=> q ->; rewrite lcmn_mulr. Qed.

Lemma dvdn_lcm_idl : forall m n, n %| m -> lcmn m n = m.
Proof. move=> m n; rewrite lcmnC; exact: dvdn_lcm_idr. Qed.

Lemma lcmn_exp : forall e m n, lcmn (e ^ m) (e ^ n) = e ^ maxn m n.
Proof.
rewrite /maxn => e m n; case: leqP; [rewrite lcmnC | move/ltnW];
 by move/(dvdn_exp2l e); exact: dvdn_lcm_idr.
Qed.

(* Coprime factors *)

Definition coprime m n := gcdn m n == 1.

Lemma coprime1n : forall n, coprime 1 n.
Proof. by move=> n; rewrite /coprime gcd1n. Qed.

Lemma coprimen1 : forall n, coprime n 1.
Proof. by move=> n; rewrite /coprime gcdn1. Qed.

Lemma coprime_sym : forall m n, coprime m n = coprime n m.
Proof. by move => m n; rewrite /coprime gcdnC. Qed.

Lemma coprime_modl : forall m n, coprime (m %% n) n = coprime m n.
Proof. by move=> m n; rewrite /coprime gcdn_modl. Qed.

Lemma coprime_modr : forall m n, coprime m (n %% m) = coprime m n.
Proof. by move=> m n; rewrite /coprime gcdn_modr. Qed.

Lemma coprimeSn : forall n, coprime n.+1 n.
Proof.
by move=> n; rewrite -coprime_modl (modn_addr 1) coprime_modl coprime1n.
Qed.

Lemma coprimenS : forall n, coprime n n.+1.
Proof. by move=> n; rewrite coprime_sym coprimeSn. Qed.

Lemma coprimePn : forall n, n > 0 -> coprime n.-1 n.
Proof. by case=> // n _; rewrite coprimenS. Qed.

Lemma coprimenP : forall n, n > 0 -> coprime n n.-1.
Proof. by case=> // n _; rewrite coprimeSn. Qed.

Lemma coprimeP : forall n m, n > 0 ->
  reflect (exists u, u.1 * n - u.2 * m = 1) (coprime n m).
Proof.
move=> n m n_gt0; apply: (iffP eqP) => [<-| [[kn km] /= kn_km_1]].
  by have [kn km kg _] := egcdnP m n_gt0; exists (kn, km); rewrite kg addKn.
apply gcdn_def; rewrite ?dvd1n // => d dv_d_n dv_d_m.
by rewrite -kn_km_1 dvdn_subr ?dvdn_mull // ltnW // -subn_gt0 kn_km_1.
Qed.

Lemma modn_coprime : forall k n, O < k ->
  (exists u, (k * u) %% n = 1%N) -> coprime k n.
Proof.
move=> k n Hpos [u Hu]; apply/coprimeP; first by [].
by exists (u, k * u %/ n); rewrite /= mulnC {1}(divn_eq (k * u) n) addKn.
Qed.

Lemma gauss_inv : forall m n p,
  coprime m n -> (m * n %| p) = (m %| p) && (n %| p).
Proof.
by move=> m n p co_mn; rewrite -muln_lcm_gcd (eqnP co_mn) muln1 dvdn_lcm.
Qed.

Lemma gauss : forall m n p, coprime m n -> (m %| n * p) = (m %| p).
Proof.
move=> m [|n] p co_mn; first by case: m co_mn => [|[]] // _; rewrite !dvd1n.
by symmetry; rewrite mulnC -(@dvdn_pmul2r n.+1) ?gauss_inv // andbC dvdn_mull.
Qed.

Lemma gauss_gcdr : forall p m n, coprime p m -> gcdn p (m * n) = gcdn p n.
Proof.
move=> p m n co_pm; apply/eqP; rewrite eqn_dvd !dvdn_gcd !dvdn_gcdl /=.
rewrite andbC dvdn_mull ?dvdn_gcdr //= -(@gauss _ m) ?dvdn_gcdr //.
by rewrite /coprime gcdnAC (eqnP co_pm) gcd1n.
Qed.

Lemma gauss_gcdl : forall p m n, coprime p n -> gcdn p (m * n) = gcdn p m.
Proof. by move=> *; rewrite mulnC gauss_gcdr. Qed.

Lemma coprime_mulr : forall p m n,
  coprime p (m * n) = coprime p m && coprime p n.
Proof.
move=> p m n.
case co_pm: (coprime p m) => /=; first by rewrite /coprime gauss_gcdr.
apply/eqP=> co_p_mn; case/eqnP: co_pm; apply gcdn_def => // d dv_dp dv_dm.
by rewrite -co_p_mn dvdn_gcd dv_dp dvdn_mulr.
Qed.

Lemma coprime_mull : forall p m n,
  coprime (m * n) p = coprime m p && coprime n p.
Proof. move=> p m n; rewrite !(coprime_sym _ p); exact: coprime_mulr. Qed.

Lemma coprime_pexpl : forall k m n, 0 < k -> coprime (m ^ k) n = coprime m n.
Proof.
case=> // k m n _; elim: k => [|k IHk]; first by rewrite expn1.
by rewrite expnS coprime_mull -IHk; case coprime.
Qed.

Lemma coprime_pexpr : forall k m n, 0 < k -> coprime m (n ^ k) = coprime m n.
Proof. by move=> k m n k_gt0; rewrite !(coprime_sym m) coprime_pexpl. Qed.

Lemma coprime_expl : forall k m n, coprime m n -> coprime (m ^ k) n.
Proof. by case=> [|k] p m co_pm; rewrite ?coprime1n // coprime_pexpl. Qed.

Lemma coprime_expr : forall k m n, coprime m n -> coprime m (n ^ k).
Proof. by move=> k m n; rewrite !(coprime_sym m); exact: coprime_expl. Qed.

Lemma coprime_dvdl : forall m n p, m %| n -> coprime n p -> coprime m p.
Proof.
by move=> m n p; case/dvdnP=> d ->; rewrite coprime_mull; case/andP.
Qed.

Lemma coprime_dvdr : forall m n p, m %| n -> coprime p n -> coprime p m.
Proof. by move=> m n p; rewrite !(coprime_sym p); exact: coprime_dvdl. Qed.

Lemma coprime_egcdn : forall n m, n > 0 ->
    coprime (egcdn n m).1 (egcdn n m).2.
Proof.
move=> n m n_gt0; case: (egcdnP m n_gt0) => kn km /=; move/eqP.
have [u defn] := dvdnP (dvdn_gcdl n m); have [v defm] := dvdnP (dvdn_gcdr n m).
rewrite -[gcdn n m]mul1n {1}defm {1}defn !mulnA -muln_addl addnC.
rewrite eqn_pmul2r ?gcdn_gt0 ?n_gt0 //; move/eqP; case: kn => // kn def_knu _.
by apply/coprimeP=> //; exists (u, v); rewrite mulnC def_knu mulnC addnK.
Qed.

Lemma dvdn_pexp2r : forall m n k, k > 0 -> (m ^ k %| n ^ k) = (m %| n).
Proof.
move=> m n k k_gt0; apply/idP/idP=> [dv_mn_k|]; last exact: dvdn_exp2r.
case: (posnP n) => [-> | n_gt0]; first by rewrite dvdn0.
have [n' def_n] := dvdnP (dvdn_gcdr m n); set d := gcdn m n in def_n.
have [m' def_m] := dvdnP (dvdn_gcdl m n); rewrite -/d in def_m.
have d_gt0: d > 0 by rewrite gcdn_gt0 n_gt0 orbT.
rewrite def_m def_n !expn_mull dvdn_pmul2r ?expn_gt0 ?d_gt0 // in dv_mn_k.
have: coprime (m' ^ k) (n' ^ k).
  rewrite coprime_pexpl // coprime_pexpr // /coprime -(eqn_pmul2r d_gt0) mul1n.
  by rewrite muln_gcdl -def_m -def_n.
rewrite /coprime -gcdn_modr (eqnP dv_mn_k) gcdn0 -(exp1n k).
by rewrite (inj_eq (expIn k_gt0)) def_m; move/eqP->; rewrite mul1n dvdn_gcdr.
Qed.

Section Chinese.

(***********************************************************************)
(*   The chinese remainder theorem                                     *)
(***********************************************************************)

Variables m1 m2 : nat.
Hypothesis co_m12 : coprime m1 m2.

Lemma chinese_remainder : forall x y,
  (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
Proof.
move=> x y; wlog le_yx : x y / y <= x.
  by case/orP: (leq_total y x); last rewrite !(eq_sym (x %% _)); auto.
by rewrite !eqn_mod_dvd // gauss_inv.
Qed.

(***********************************************************************)
(*   A function that solves the chinese remainder problem              *)
(***********************************************************************)

Definition chinese r1 r2 :=
  r1 * m2 * (egcdn m2 m1).1 + r2 * m1 * (egcdn m1 m2).1.

Lemma chinese_modl : forall r1 r2, chinese r1 r2 = r1 %[mod m1].
Proof.
rewrite /chinese; case: (posnP m2) co_m12 => [->|m2_gt0 _].
  by move/eqnP; rewrite gcdn0 => -> r1 r2 ; rewrite !modn1.
case: egcdnP=> // k2 k1 def_m1 _ r1 r2.
rewrite mulnAC -mulnA def_m1 gcdnC (eqnP co_m12) muln_addr mulnA muln1.
by rewrite addnAC (mulnAC _ m1) -muln_addl modn_addl_mul.
Qed.

Lemma chinese_modr : forall r1 r2, chinese r1 r2 = r2 %[mod m2].
Proof.
rewrite /chinese; case: (posnP m1) co_m12 => [->|m1_gt0 _].
  by move/eqnP; rewrite gcd0n => -> r1 r2 ; rewrite !modn1.
case: (egcdnP m2) => // k1 k2 def_m2 _ r1 r2.
rewrite addnC mulnAC -mulnA def_m2 (eqnP co_m12) muln_addr mulnA muln1.
by rewrite addnAC (mulnAC _ m2) -muln_addl modn_addl_mul.
Qed.

Lemma chinese_modlr : forall x, x = chinese (x %% m1) (x %% m2) %[mod m1 * m2].
Proof.
move=> x; apply/eqP.
by rewrite chinese_remainder // chinese_modl chinese_modr !modn_mod !eqxx.
Qed.

End Chinese.

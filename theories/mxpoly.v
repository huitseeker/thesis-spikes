(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype tuple.
Require Import finfun bigop fingroup perm ssralg zmodp matrix mxalgebra poly.

(******************************************************************************)
(*   This file provides basic support for formal computation with matrices,   *)
(* mainly results combining matrices and univariate polynomials, such as the  *)
(* Cayley-Hamilton theorem; it also contains an extension of the first order  *)
(* representation of algebra introduced in ssralg (GRing.term/formula).       *)
(*      rVpoly v == the little-endian decoding of the row vector v as a       *)
(*                  polynomial p = \sum_i (v 0 i)%:P * 'X^i.                  *)
(*     poly_rV p == the partial inverse to rVpoly, for polynomials of degree  *)
(*                  less than d to 'rV_d (d is inferred from the context).    *)
(* Sylvester_mx p q == the Sylvester matrix of p and q.                       *)
(* resultant p q == the rusultant of p and q, i.e., \det (Sylvester_mx p q).  *)
(*   horner_mx A == the morphism from {poly R} to 'M_n (n of the form n'.+1)  *)
(*                  mapping a (scalar) polynomial p to the value of its       *)
(*                  scalar matrix interpretation at A (this is an instance of *)
(*                  the generic horner_morph construct defined in poly).      *)
(* powers_mx A d == the d x (n ^ 2) matrix whose rows are the mxvec encodings *)
(*                  of the first d powers of A (n of the form n'.+1). Thus,   *)
(*                  vec_mx (v *m powers_mx A d) = horner_mx A (rVpoly v).     *)
(*   char_poly A == the characteristic polynomial of A.                       *)
(* char_poly_mx A == a matrix whose detereminant is char_poly A.              *)
(*   mxminpoly A == the minimal polynomial of A, i.e., the smallest monic     *)
(*                  polynomial that annihilates A (A must be nontrivial).     *)
(* degree_mxminpoly A == the (positive) degree of mxminpoly A.                *)
(* mx_inv_horner A == the inverse of horner_mx A for polynomials of degree    *)
(*                  smaller than degree_mxminpoly A.                          *)
(* This toolkit for building formal matrix expressions is packaged in the     *)
(* MatrixFormula submodule, and comprises the following:                      *)
(*     eval_mx e == GRing.eval lifted to matrices (:= map_mx (GRing.eval e)). *)
(*     mx_term A == GRing.Const lifted to matrices.                           *)
(* mulmx_term A B == the formal product of two matrices of terms.             *)
(* mxrank_form m A == a GRing.formula asserting that the interpretation of    *)
(*                  the term matrix A has rank m.                             *)
(* submx_form A B == a GRing.formula asserting that the row space of the      *)
(*                  interpretation of the term matrix A is included in the    *)
(*                  row space of the interpretation of B.                     *)
(*   seq_of_rV v == the seq corresponding to a row vector.                    *)
(*     row_env e == the flattening of a tensored environment e : seq 'rV_d.   *)
(* row_var F d k == the term vector of width d such that for e : seq 'rV[F]_d *)
(*                  we have eval e 'X_k = eval_mx (row_env e) (row_var d k).  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Monoid.Theory.

Open Local Scope ring_scope.

(* Row vector <-> bounded degree polynomial bijection *)
Section RowPoly.

Variables (R : ringType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

Lemma coef_rVpoly : forall v k,
  (rVpoly v)`_k = if insub k is Some i then v 0 i else 0.
Proof.
by move=> v k; rewrite coef_poly; case: insubP => [i ->|]; rewrite ?if_same.
Qed.

Lemma coef_rVpoly_ord : forall v (i : 'I_d), (rVpoly v)`_i = v 0 i.
Proof. by move=> v i; rewrite coef_rVpoly valK. Qed.

Lemma rVpoly_delta : forall i, rVpoly (delta_mx 0 i) = 'X^i.
Proof.
move=> i; apply/polyP=> j; rewrite coef_rVpoly coef_Xn.
case: insubP => [k _ <- | j_ge_d]; first by rewrite mxE.
by case: eqP j_ge_d => // ->; rewrite ltn_ord.
Qed.

Lemma rVpolyK : cancel rVpoly poly_rV.
Proof. by move=> u; apply/rowP=> i; rewrite mxE coef_rVpoly_ord. Qed.

Lemma poly_rV_K : forall p, size p <= d -> rVpoly (poly_rV p) = p.
Proof.
move=> p le_p_d; apply/polyP=> k; rewrite coef_rVpoly.
case: insubP => [i _ <- | ]; first by rewrite mxE.
by rewrite -ltnNge => le_d_l; rewrite nth_default ?(leq_trans le_p_d).
Qed.

Lemma poly_rV_is_linear : linear poly_rV.
Proof. by move=> a p q; apply/rowP=> i; rewrite !mxE coef_add coef_scaler. Qed.
Canonical Structure poly_rV_additive := Additive poly_rV_is_linear.
Canonical Structure poly_rV_linear := Linear poly_rV_is_linear.

Lemma rVpoly_is_linear : linear rVpoly.
Proof.
move=> a u v; apply/polyP=> k; rewrite coef_add coef_scaler !coef_rVpoly.
by case: insubP => [i _ _ | _]; rewrite ?mxE // mulr0 addr0.
Qed.
Canonical Structure rVpoly_additive := Additive rVpoly_is_linear.
Canonical Structure rVpoly_linear := Linear rVpoly_is_linear.

End RowPoly.

Implicit Arguments poly_rV [R d].
Prenex Implicits rVpoly poly_rV.

Section Resultant.

Variables (F : fieldType) (p q : {poly F}).
Implicit Types m d r : {poly F}.

Let dp := (size p).-1.
Let dq := (size q).-1.

Local Notation band r := (lin1_mx (poly_rV \o r \o* rVpoly)).

Definition Sylvester_mx : 'M[F]_(dq + dp) := col_mx (band p) (band q).

Lemma Sylvester_mxE : forall i j : 'I_(dq + dp),
    let S_ r k := r`_(j - k) *+ (k <= j) in
  Sylvester_mx i j = match split i with inl k => S_ p k | inr k => S_ q k end.
Proof.
move=> i j S_; rewrite mxE; case: {i}(split i) => i; rewrite !mxE /=;
  by rewrite rVpoly_delta coef_Xn_mul ltnNge if_neg -mulrb.
Qed.

Definition resultant := \det Sylvester_mx.

Lemma resultant_eq0 : (resultant == 0) = (size (gcdp p q) > 1).
Proof.
have dvdpp := dvdpp; set r := gcdp p q.
have [r_p r_q]: r %| p /\ r %| q by apply/andP; rewrite -dvdp_gcd.
have dvdpP: forall d m, d %| m -> exists f, m = d * f.
  move=> d m; case/dvdpPc=> c [f [nz_c def_fd]].
  by exists (c^-1 *: f); rewrite mulrC -scaler_mull -def_fd scalerK.
have dvd_nz: forall d m, d %| m -> m != 0 -> d != 0.
  by move=> d m; case/dvdpP=> f ->; rewrite mulf_eq0; case/norP.
apply/det0P/idP=> [[uv nz_uv] | r_nonC].
  have [p0 _ | p_nz] := eqVneq p 0.
    have: dq + dp > 0.
      by rewrite (leq_trans _ (rank_leq_col uv)) // lt0n mxrank_eq0.
    by rewrite /dp /dq /r p0 size_poly0 addn0 gcd0p -subn1 subn_gt0.
  do [rewrite -[uv]hsubmxK -{1}row_mx0 mul_row_col !mul_rV_lin1 /=] in nz_uv *.
  set u := rVpoly _; set v := rVpoly _; pose m := gcdp (v * p) (v * q).
  have lt_vp: size v < size p by rewrite (polySpred p_nz) ltnS size_poly.
  move/(congr1 rVpoly); rewrite linearD linear0 /=; move/(canRL (addKr _)).
  rewrite !poly_rV_K ?(leq_trans (size_mul _ _)) // => [vq_up||]; first 1 last.
  - by rewrite -subn1 leq_sub_add addnCA leq_add ?leqSpred ?size_poly.
  - by rewrite -subn1 leq_sub_add addnC addnA leq_add ?leqSpred ?size_poly.
  have nz_v: v != 0.
    apply: contraNneq nz_uv => v0; apply/eqP.
    congr row_mx; apply: (can_inj (@rVpolyK _ _)); rewrite linear0 // -/u.
    move/eqP: vq_up; apply: contraTeq => nz_u.
    by rewrite v0 mul0r addr0 eq_sym oppr_eq0 mulf_neq0.
  have r_nz: r != 0 := dvd_nz _ _ r_p p_nz.
  have [|w vw] := dvdpP v m; first by rewrite dvdp_gcd !dvdp_mulr.
  have m_wd: forall d, m %| v * d -> w %| d.
    move=> d; case/dvdpP=> f; rewrite vw -mulrA; move/mulfI=> -> //.
    exact: dvdp_mulr.
  have w_r: w %| r by rewrite dvdp_gcd !m_wd ?dvdp_gcdl ?dvdp_gcdr.
  have w_nz: w != 0 := dvd_nz _ _ w_r r_nz.
  have p_m: p %| m by rewrite dvdp_gcd vq_up addr0 -mulNr !dvdp_mull.
  rewrite (leq_trans _ (size_dvdp r_nz w_r)) // -(ltn_add2l (size v)).
  rewrite addnC ltn_add_sub subn1 -size_mul_id // -vw.
  by rewrite (leq_trans lt_vp) // size_dvdp // vw mulf_neq0.
have [[p' p'r] [q' q'r]] := (dvdpP _ _ r_p, dvdpP _ _ r_q).
have def_r := subnKC r_nonC; have r_nz: r != 0 by rewrite -size_poly_eq0 -def_r.
have le_p'_dp: size p' <= dp.
  have [-> | nz_p'] := eqVneq p' 0; first by rewrite size_poly0.
  by rewrite /dp p'r size_mul_id // -def_r leq_addl.
have le_q'_dq: size q' <= dq.
  have [-> | nz_q'] := eqVneq q' 0; first by rewrite size_poly0.
  by rewrite /dq q'r size_mul_id // -def_r leq_addl.
exists (row_mx (- poly_rV q') (poly_rV p')).
  apply: contraNneq r_nz; rewrite -row_mx0; case/eq_row_mx=> q0 p0.
  rewrite /r p'r -(poly_rV_K le_p'_dp) p0 linear0 mulr0 gcd0p -oppr_eq0.
  by rewrite q'r -(poly_rV_K le_q'_dq) -mulrN -linearN q0 linear0 mulr0.
rewrite mul_row_col mulNmx !mul_rV_lin1 /= !poly_rV_K //.
by rewrite  q'r {1}p'r mulrC -mulrA mulrCA addNr.
Qed.

End Resultant.

Section HornerMx.

Variables (R : comRingType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[R]_n.
Implicit Types p q : {poly R}.

Definition horner_mx := horner_morph (fun a => scalar_mx_comm a A).
Canonical Structure horner_mx_additive := [additive of horner_mx].
Canonical Structure horner_mx_rmorphism := [rmorphism of horner_mx].

Lemma horner_mx_C : forall a, horner_mx a%:P = a%:M.
Proof. exact: horner_morphC. Qed.

Lemma horner_mx_X : horner_mx 'X = A. Proof. exact: horner_morphX. Qed.

Lemma horner_mxZ : scalable horner_mx.
Proof.
move=> a p /=; rewrite -mul_polyC rmorphM /=.
by rewrite horner_mx_C [_ * _]mul_scalar_mx.
Qed.

Canonical Structure horner_mx_linear := AddLinear horner_mxZ.
Canonical Structure horner_mx_lrmorphism := [lrmorphism of horner_mx].

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

Lemma horner_rVpoly : forall m (u : 'rV_m),
  horner_mx (rVpoly u) = vec_mx (u *m powers_mx m).
Proof.
move=> m u; rewrite mulmx_sum_row linear_sum [rVpoly u]poly_def rmorph_sum.
apply: eq_bigr => i _.
by rewrite valK !linearZ rmorphX /= horner_mx_X rowK /= mxvecK.
Qed.

End HornerMx.

Section CharPoly.

Variables (R : ringType) (n : nat) (A : 'M[R]_n).
Implicit Types p q : {poly R}.

Definition char_poly_mx := 'X%:M - map_mx (@polyC R) A.
Definition char_poly := \det char_poly_mx.

Let diagA := map (fun i => A i i) (enum 'I_n).
Let size_diagA : size diagA = n.
Proof. by rewrite size_map -cardE card_ord. Qed.

Let split_diagA :
  exists2 q, \prod_(x <- diagA) ('X - x%:P) + q = char_poly & size q <= n.-1.
Proof.
rewrite [char_poly](bigD1 1%g) //=; set q := \sum_(s | _) _; exists q.
  congr (_ + _); rewrite odd_perm1 mul1r big_map enumT; apply: eq_bigr => i _.
  by rewrite !mxE perm1 eqxx.
apply: leq_trans {q}(size_sum _ _ _) _; apply/bigmax_leqP=> s nt_s.
have{nt_s} [i nfix_i]: exists i, s i != i.
  apply/existsP; rewrite -negb_forall; apply: contra nt_s => s_1.
  by apply/eqP; apply/permP=> i; apply/eqP; rewrite perm1 (forallP s_1).
apply: leq_trans (_ : #|[pred j | s j == j]|.+1 <= n.-1).
  rewrite -sum1_card (@big_mkcond nat) /= size_sign_mul.
  apply: (big_rel (fun p m => size p <= m.+1)) => [| p mp q mq IHp IHq | j _].
  - by rewrite size_poly1.
  - apply: leq_trans (size_mul _ _) _.
    by rewrite -subn1 -addnS leq_sub_add addnA leq_add.
  rewrite !mxE eq_sym !inE; case: (s j == j); first by rewrite seq_factor. 
  by rewrite sub0r size_opp size_polyC leq_b1.
rewrite -{8}[n]card_ord -(cardC (pred2 (s i) i)) card2 nfix_i !ltnS.
apply: subset_leq_card; apply/subsetP=> j; move/(_ =P j)=> fix_j.
rewrite !inE -{1}fix_j (inj_eq (@perm_inj _ s)) orbb.
by apply: contraNneq nfix_i => <-; rewrite fix_j.
Qed.   

Lemma size_char_poly : size char_poly = n.+1.
Proof.
have [q <- lt_q_n] := split_diagA; have le_q_n := leq_trans lt_q_n (leq_pred n).
by rewrite size_addl size_prod_factors size_diagA.
Qed.

Lemma char_poly_monic : monic char_poly.
Proof.
rewrite /monic -(eqP (prod_factors_monic diagA)) !lead_coefE size_char_poly.
have [q <- lt_q_n] := split_diagA; have le_q_n := leq_trans lt_q_n (leq_pred n).
by rewrite size_prod_factors size_diagA coef_add (nth_default 0 le_q_n) addr0.
Qed.

Lemma char_poly_trace : n > 0 -> char_poly`_n.-1 = - \tr A.
Proof.
move=> n_gt0; have [q <- lt_q_n] := split_diagA; set p := \prod_(x <- _) _.
rewrite coef_add {q lt_q_n}(nth_default 0 lt_q_n) addr0.
have{n_gt0} ->: p`_n.-1 = ('X * p)`_n by rewrite coef_Xmul eqn0Ngt n_gt0.
have ->: \tr A = \sum_(x <- diagA) x by rewrite big_map enumT.
rewrite -size_diagA {}/p; elim: diagA => [|x d IHd].
  by rewrite !big_nil mulr1 coefX oppr0.
rewrite !big_cons coef_Xmul mulr_subl coef_sub IHd oppr_add addrC.
congr (- _ + _); rewrite mul_polyC coef_scaler [size _]/=. 
by rewrite -size_prod_factors -lead_coefE (eqP (prod_factors_monic d)) mulr1.
Qed.

Lemma char_poly_det : char_poly`_0 = (- 1) ^+ n * \det A.
Proof.
rewrite big_distrr coef_sum [0%N]lock /=; apply: eq_bigr => s _.
rewrite -{1}rmorphN -rmorphX mul_polyC coef_scaler /=.
rewrite mulrA -exprn_addr addnC exprn_addr -mulrA -lock; congr (_ * _).
transitivity (\prod_(i < n) - A i (s i)); last by rewrite prodr_opp card_ord.
elim: (index_enum _) => [|i e IHe]; rewrite !(big_nil, big_cons) ?coef1 //.
rewrite coef_mul big_ord1 IHe !mxE coef_sub coefC coef_natmul coefX.
by rewrite mul0rn sub0r.
Qed.

End CharPoly.

Lemma mx_poly_ring_isom : forall (R : ringType) n' (n := n'.+1),
  exists phi : {rmorphism 'M[{poly R}]_n -> {poly 'M[R]_n}},
  [/\ bijective phi,
      forall p, phi p%:M = map_poly scalar_mx p,
      forall A, phi (map_mx polyC A) = A%:P
    & forall A i j k, (phi A)`_k i j = (A i j)`_k].
Proof.
move=> R n' n; set M_RX := 'M[{poly R}]_n; set MR_X := ({poly 'M[R]_n}).
pose Msize (A : M_RX) := \max_i \max_j size (A i j).
pose phi (A : M_RX) := \poly_(k < Msize A) \matrix_(i, j) (A i j)`_k.
have coef_phi : forall A i j k, (phi A)`_k i j = (A i j)`_k.
  move=> A i j k; rewrite coef_poly.
  case: (ltnP k _) => le_m_k; rewrite mxE // nth_default //.
  apply: leq_trans (leq_trans (leq_bigmax i) le_m_k); exact: (leq_bigmax j).
have phi_is_rmorphism : rmorphism phi.
  do 2?[split=> [A B|]]; apply/polyP=> k; apply/matrixP=> i j; last 1 first.
  - rewrite coef_phi mxE coef_natmul !coefC.
    by case: (k == _); rewrite ?mxE ?mul0rn.
  - by rewrite !(coef_phi, mxE, coef_add, coef_opp).
  rewrite !coef_phi !mxE !coef_mul summxE coef_sum.
  pose F k1 k2 := (A i k1)`_k2 * (B k1 j)`_(k - k2).
  transitivity (\sum_k1 \sum_(k2 < k.+1) F k1 k2); rewrite {}/F.
    by apply: eq_bigr=> k1 _; rewrite coef_mul.
  rewrite exchange_big /=; apply: eq_bigr => k2 _.
  by rewrite mxE; apply: eq_bigr => k1 _; rewrite !coef_phi.
have bij_phi: bijective phi.
  exists (fun P : MR_X => \matrix_(i, j) \poly_(k < size P) P`_k i j) => [A|P].
    apply/matrixP=> i j; rewrite mxE; apply/polyP=> k.
    rewrite coef_poly -coef_phi.
    by case: leqP => // P_le_k; rewrite nth_default ?mxE.
  apply/polyP=> k; apply/matrixP=> i j; rewrite coef_phi mxE coef_poly.
  by case: leqP => // P_le_k; rewrite nth_default ?mxE.
exists (RMorphism phi_is_rmorphism).
split=> // [p | A]; apply/polyP=> k; apply/matrixP=> i j.
  by rewrite coef_phi coef_map !mxE coef_natmul.
by rewrite coef_phi !mxE !coefC; case k; last rewrite /= mxE.
Qed.

Theorem Cayley_Hamilton : forall (R : comRingType) n' (A : 'M[R]_n'.+1),
  horner_mx A (char_poly A) = 0.
Proof.
move=> R n' A; have [phi [_ phiZ phiC _]] := mx_poly_ring_isom R n'.
apply/eqP; apply/factor_theorem; rewrite -phiZ -mul_adj_mx rmorphM.
by move: (phi _) => q; exists q; rewrite rmorph_sub phiC phiZ map_polyX.
Qed.

Lemma eigenvalue_root_char : forall (F : fieldType) n (A : 'M[F]_n) a,
  eigenvalue A a = root (char_poly A) a.
Proof.
move=> F n A a; transitivity (\det (a%:M - A) == 0).
  apply/eigenvalueP/det0P=> [[v Av_av v_nz] | [v v_nz Av_av]]; exists v => //.
    by rewrite mulmx_subr Av_av mul_mx_scalar subrr.
  by apply/eqP; rewrite -mul_mx_scalar eq_sym -subr_eq0 -mulmx_subr Av_av.
congr (_ == 0); rewrite horner_sum; apply: eq_bigr => s _.
rewrite horner_mul horner_exp !horner_lin; congr (_ * _).
rewrite (big_morph _ (fun p q => horner_mul p q a) (hornerC 1 a)).
by apply: eq_bigr => i _; rewrite !mxE !(horner_lin, horner_mulrn).
Qed.

Section MinPoly.

Variables (F : fieldType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[F]_n.
Implicit Types p q : {poly F}.

Fact degree_mxminpoly_proof : exists d, \rank (powers_mx A d.+1) <= d.
Proof. by exists (n ^ 2)%N; rewrite rank_leq_col. Qed.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (powers_mx A d).

Lemma mxminpoly_nonconstant : d > 0.
Proof.
rewrite /d; case: ex_minnP; case=> //; rewrite leqn0 mxrank_eq0; move/eqP.
move/row_matrixP; move/(_ 0); move/eqP; rewrite rowK row0 mxvec_eq0.
by rewrite -mxrank_eq0 mxrank1.
Qed.

Lemma minpoly_mx1 : (1%:M \in Ad)%MS.
Proof.
by apply: (eq_row_sub (Ordinal mxminpoly_nonconstant)); rewrite rowK.
Qed.

Lemma minpoly_mx_free : row_free Ad.
Proof.
have:= mxminpoly_nonconstant; rewrite /d; case: ex_minnP; case=> // d' _.
move/(_ d'); move/implyP; rewrite ltnn implybF -ltnS ltn_neqAle.
by rewrite rank_leq_row andbT negbK.
Qed.

Lemma horner_mx_mem : forall p, (horner_mx A p \in Ad)%MS.
Proof.
apply: poly_ind => [|p a IHp]; first by rewrite rmorph0 // linear0 sub0mx.
rewrite rmorphD rmorphM /= horner_mx_C horner_mx_X.
rewrite addrC -scalemx1 linearP /= -(mul_vec_lin (mulmxr_linear _ A)).
case/submxP: IHp => u ->{p}.
have: (powers_mx A (1 + d) <= Ad)%MS.
  rewrite -(geq_leqif (mxrank_leqif_sup _)).
    by rewrite (eqnP minpoly_mx_free) /d; case: ex_minnP.
  rewrite addnC; apply/row_subP=> i.
  by apply: eq_row_sub (lshift 1 i) _; rewrite !rowK.
apply: submx_trans; rewrite addmx_sub ?scalemx_sub //.
  by apply: (eq_row_sub 0); rewrite rowK.
rewrite -mulmxA mulmx_sub {u}//; apply/row_subP=> i.
rewrite row_mul rowK mul_vec_lin /= mulmxE -exprSr.
by apply: (eq_row_sub (rshift 1 i)); rewrite rowK.
Qed.

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Lemma mx_inv_horner0 :  mx_inv_horner 0 = 0.
Proof. by rewrite /mx_inv_horner !(linear0, mul0mx). Qed.

Lemma mx_inv_hornerK : forall B,
  (B \in Ad)%MS -> horner_mx A (mx_inv_horner B) = B.
Proof. by move=> B sBAd; rewrite horner_rVpoly mulmxKpV ?mxvecK. Qed.

Lemma minpoly_mxM : forall B C, (B \in Ad -> C \in Ad -> B * C \in Ad)%MS.
Proof.
move=> B C AdB AdC; rewrite -(mx_inv_hornerK AdB) -(mx_inv_hornerK AdC).
by rewrite -rmorphM ?horner_mx_mem.
Qed.

Lemma minpoly_mx_ring : mxring Ad.
Proof.
apply/andP; split; first by apply/mulsmx_subP; exact: minpoly_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: minpoly_mx1.
Qed.

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).
Local Notation p_A := mxminpoly.

Lemma size_mxminpoly : size p_A = d.+1.
Proof. by rewrite size_addl ?size_polyXn // size_opp ltnS size_poly. Qed.

Lemma mxminpoly_monic : monic p_A.
Proof.
rewrite /monic /lead_coef size_mxminpoly coef_sub coef_Xn eqxx /=.
by rewrite nth_default ?size_poly // subr0.
Qed.

Lemma size_mod_mxminpoly : forall p, size (p %% p_A) <= d.
Proof.
move=> p; rewrite -ltnS -size_mxminpoly modp_spec //.
by rewrite -size_poly_eq0 size_mxminpoly.
Qed.

Lemma mx_root_minpoly : horner_mx A p_A = 0.
Proof.
rewrite rmorph_sub -{3}(horner_mx_X A) -rmorphX /=.
by rewrite mx_inv_hornerK ?subrr ?horner_mx_mem.
Qed.

Lemma horner_rVpolyK : forall u : 'rV_d,
  mx_inv_horner (horner_mx A (rVpoly u)) = rVpoly u.
Proof.
move=> u; congr rVpoly; rewrite horner_rVpoly vec_mxK.
by apply: (row_free_inj minpoly_mx_free); rewrite mulmxKpV ?submxMl.
Qed.

Lemma horner_mxK : forall p, mx_inv_horner (horner_mx A p) = p %% p_A.
Proof.
move=> p; rewrite {1}(divp_mon_spec p mxminpoly_monic) rmorphD rmorphM /=.
rewrite mx_root_minpoly mulr0 add0r.
by rewrite -(poly_rV_K (size_mod_mxminpoly _)) horner_rVpolyK.
Qed.

Lemma mxminpoly_min : forall p, horner_mx A p = 0 -> p_A %| p.
Proof. by move=> p pA0; rewrite /dvdp -horner_mxK pA0 mx_inv_horner0. Qed.

Lemma horner_rVpoly_inj : @injective 'M_n 'rV_d (horner_mx A \o rVpoly).
Proof.
apply: can_inj (poly_rV \o mx_inv_horner) _ => u.
by rewrite /= horner_rVpolyK rVpolyK.
Qed.

Lemma mxminpoly_linear_is_scalar : (d <= 1) = is_scalar_mx A.
Proof.
have scalP := has_non_scalar_mxP minpoly_mx1.
rewrite leqNgt -(eqnP minpoly_mx_free); apply/scalP/idP=> [|[[B]]].
  case scalA: (is_scalar_mx A); [by right | left].
  by exists A; rewrite ?scalA // -{1}(horner_mx_X A) horner_mx_mem.
move/mx_inv_hornerK=> <- nsB; case/is_scalar_mxP=> a defA; case/negP: nsB.
move: {B}(_ B); apply: poly_ind => [|p c].
  by rewrite rmorph0 ?mx0_is_scalar.
rewrite rmorphD ?rmorphM /= horner_mx_X defA; case/is_scalar_mxP=> b ->.
by rewrite -rmorphM horner_mx_C -rmorphD /= scalar_mx_is_scalar.
Qed.

Lemma mxminpoly_dvd_char : p_A %| char_poly A.
Proof. by apply: mxminpoly_min; exact: Cayley_Hamilton. Qed.

Lemma eigenvalue_root_min : forall a, eigenvalue A a = root p_A a.
Proof.
move=> a; apply/idP/idP=> Aa; last first.
  rewrite eigenvalue_root_char !root_factor_theorem in Aa *.
  exact: dvdp_trans Aa mxminpoly_dvd_char.
have{Aa} [v Av_av v_nz] := eigenvalueP Aa.
apply: contraR v_nz => pa_nz; rewrite -{pa_nz}(eqmx_eq0 (eqmx_scale _ pa_nz)).
apply/eqP; rewrite -(mulmx0 _ v) -mx_root_minpoly.
move: p_A; apply: poly_ind => [|p c IHp].
  by rewrite rmorph0 horner0 scale0r mulmx0.
rewrite !horner_lin rmorphD rmorphM /= horner_mx_X horner_mx_C scaler_addl.
by rewrite -scalerA mulmx_addr mul_mx_scalar mulmxA -IHp -scalemxAl Av_av.
Qed.

End MinPoly.

(* Parametricity. *)
Section MapRing.

Variables (aR rR : ringType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (d n : nat) (A : 'M[aR]_n).

Lemma map_rVpoly : forall u : 'rV_d, fp (rVpoly u) = rVpoly u^f.
Proof.
move=> u; apply/polyP=> k; rewrite coef_map !coef_rVpoly.
by case: (insub k) => [i|]; rewrite  /=  ?rmorph0 // mxE.
Qed.

Lemma map_poly_rV : forall p, (poly_rV p)^f = poly_rV (fp p) :> 'rV_d.
Proof. by move=> p; apply/rowP=> j; rewrite !mxE coef_map. Qed.

Lemma map_char_poly_mx : map_mx fp (char_poly_mx A) = char_poly_mx A^f.
Proof.
rewrite raddf_sub /= map_scalar_mx /= map_polyX; congr (_ - _).
by apply/matrixP=> i j; rewrite !mxE map_polyC.
Qed.

Lemma map_char_poly : fp (char_poly A) = char_poly A^f.
Proof. by rewrite -det_map_mx map_char_poly_mx. Qed.

End MapRing.

Section MapComRing.

Variables (aR rR : comRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (n' : nat) (A : 'M[aR]_n'.+1).

Lemma map_powers_mx : forall e, (powers_mx A e)^f = powers_mx A^f e.
Proof.
by move=> e; apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec rmorphX.
Qed.

Lemma map_horner_mx : forall p, (horner_mx A p)^f = horner_mx A^f (fp p).
Proof.
move=> p; rewrite -[p](poly_rV_K (leqnn _)) map_rVpoly.
by rewrite !horner_rVpoly map_vec_mx map_mxM map_powers_mx.
Qed.

End MapComRing.

Section MapField.

Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Local Notation fp := (map_poly f).
Variables (n' : nat) (A : 'M[aF]_n'.+1).

Lemma degree_mxminpoly_map : degree_mxminpoly A^f = degree_mxminpoly A.
Proof. by apply: eq_ex_minn => e; rewrite -map_powers_mx mxrank_map. Qed.

Lemma mxminpoly_map : mxminpoly A^f = fp (mxminpoly A).
Proof.
rewrite rmorph_sub; congr (_ - _).
  by rewrite /= map_polyXn degree_mxminpoly_map.
rewrite degree_mxminpoly_map -rmorphX /=.
apply/polyP=> i; rewrite coef_map //= !coef_rVpoly degree_mxminpoly_map.
case/insub: i => [i|]; last by rewrite rmorph0.
by rewrite -map_powers_mx -map_pinvmx // -map_mxvec -map_mxM // mxE.
Qed.

Lemma map_mx_inv_horner : forall u,
  fp (mx_inv_horner A u) = mx_inv_horner A^f u^f.
Proof.
move=> u; rewrite map_rVpoly map_mxM map_mxvec map_pinvmx map_powers_mx.
by rewrite /mx_inv_horner degree_mxminpoly_map.
Qed.

End MapField.

(* Lifting term, formula, envs and eval to matrices. Wlog, and for the sake  *)
(* of simplicity, we only lift (tensor) envs to row vectors; we can always   *)
(* use mxvec/vec_mx to store and retrieve matrices.                          *)
(* We don't provide definitions for addition, substraction, scaling, etc,    *)
(* because they have simple matrix expressions.                              *)
Module MatrixFormula.

Section MatrixFormula.

Variable F : fieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation And := GRing.And (only parsing).
Local Notation Add := GRing.Add (only parsing).
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Definition eval_mx (e : seq F) := map_mx (eval e).

Definition mx_term := map_mx (@GRing.Const F).

Lemma eval_mx_term : forall e m n (A : 'M_(m, n)), eval_mx e (mx_term A) = A.
Proof. by move=> e m n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Definition mulmx_term m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) (\big[Add/0]_j (A i j * B j k))%T.

Lemma eval_mulmx : forall e m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)),
  eval_mx e (mulmx_term A B) = eval_mx e A *m eval_mx e B.
Proof.
move=> e m n p A B; apply/matrixP=> i k; rewrite !mxE /=.
rewrite (@big_morph _ _ _ 0 _ +%R (eval e)) //=.
by apply: eq_bigr => j _; rewrite /= !mxE.
Qed.

Local Notation morphAnd := (@big_morph _ _ _ true _ andb).

Let Schur m n (A : 'M[term]_(1 + m, 1 + n)) (a := A 0 0) :=
  \matrix_(i, j) (drsubmx A i j - a^-1 * dlsubmx A i 0%R * ursubmx A 0%R j)%T.

Fixpoint mxrank_form (r m n : nat) : 'M_(m, n) -> form :=
  match m, n return 'M_(m, n) -> form with
  | m'.+1, n'.+1 => fun A : 'M_(1 + m', 1 + n') =>
    let nzA k := A k.1 k.2 != 0 in
    let xSchur k := Schur (xrow k.1 0%R (xcol k.2 0%R A)) in
    let recf k := Bool (r > 0) /\ mxrank_form r.-1 (xSchur k) in
    GRing.Pick nzA recf (Bool (r == 0%N))
  | _, _ => fun _ => Bool (r == 0%N)
  end%T.

Lemma mxrank_form_qf : forall r m n (A : 'M_(m, n)), qf_form (mxrank_form r A).
Proof.
move=> r m; elim: m r => [|m IHm] r [|n] A //=.
by rewrite GRing.Pick_form_qf /=.
Qed.

Lemma eval_mxrank : forall e r m n (A : 'M_(m, n)),
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
Proof.
move=> e r m; elim: m r => [|m IHm] r [|n] A /=; try by case r.
rewrite GRing.eval_Pick /mxrank -lock /=; set pf := fun _ => _.
rewrite -(@eq_pick _ pf) => [|k]; rewrite {}/pf ?mxE // eq_sym.
case: pick => [[i j]|] //=; set B := _ - _; have:= mxrankE B.
case: (gaussian_elimination B) r => [[_ _] _] [|r] //= <-; rewrite {}IHm eqSS.
by congr (\rank _ == r); apply/matrixP=> k l; rewrite !(mxE, big_ord1) !tpermR.
Qed.

Lemma eval_vec_mx : forall e m n (u : 'rV_(m * n)),
  eval_mx e (vec_mx u) = vec_mx (eval_mx e u).
Proof. by move=> e m n u; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eval_mxvec : forall e m n (A : 'M_(m, n)),
  eval_mx e (mxvec A) = mxvec (eval_mx e A).
Proof. by move=> e m n A; rewrite -{2}[A]mxvecK eval_vec_mx vec_mxK. Qed.

Section Subsetmx.

Variables (m1 m2 n : nat) (A : 'M[term]_(m1, n)) (B : 'M[term]_(m2, n)).

Definition submx_form :=
  \big[And/True]_(r < n.+1) (mxrank_form r (col_mx A B) ==> mxrank_form r B)%T.

Lemma eval_col_mx : forall e,
  eval_mx e (col_mx A B) = col_mx (eval_mx e A) (eval_mx e B).
Proof.
by move=> e; apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?].
Qed.

Lemma submx_form_qf : qf_form submx_form.
Proof.
by rewrite (morphAnd (@qf_form _)) ?big1 //= => r _; rewrite !mxrank_form_qf.
Qed.

Lemma eval_submx : forall e,
  qf_eval e submx_form = (eval_mx e A <= eval_mx e B)%MS.
Proof.
move=> e; rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/idP=> [|sAB d]; last first.
  rewrite !eval_mxrank eval_col_mx -addsmxE; apply/implyP; move/eqP <-.
  by rewrite mxrank_leqif_sup ?addsmxSr // addsmx_sub sAB /=.
move/(_ (inord (\rank (eval_mx e (col_mx A B))))).
rewrite inordK ?ltnS ?rank_leq_col // !eval_mxrank eqxx /= eval_col_mx.
by rewrite -addsmxE mxrank_leqif_sup ?addsmxSr // addsmx_sub; case/andP.
Qed.

End Subsetmx.

Section Env.

Variable d : nat.

Definition seq_of_rV (v : 'rV_d) : seq F := fgraph [ffun i => v 0 i].

Lemma size_seq_of_rV : forall v, size (seq_of_rV v) = d.
Proof. by move=> v; rewrite tuple.size_tuple card_ord. Qed.

Lemma nth_seq_of_rV : forall x0 v (i : 'I_d), nth x0 (seq_of_rV v) i = v 0 i.
Proof. by move=> x0 v i; rewrite nth_fgraph_ord ffunE. Qed.

Definition row_var k : 'rV[term]_d := \row_i ('X_(k * d + i))%T.

Definition row_env (e : seq 'rV_d) := flatten (map seq_of_rV e).

Lemma nth_row_env : forall e k (i : 'I_d), (row_env e)`_(k * d + i) = e`_k 0 i.
Proof.
move=> e k i; elim: e k => [|v e IHe] k; first by rewrite !nth_nil mxE.
rewrite /row_env /= nth_cat size_seq_of_rV.
case: k => [|k]; first by rewrite (valP i) nth_seq_of_rV.
by rewrite mulSn -addnA -if_neg -leqNgt leq_addr addKn IHe.
Qed.

Lemma eval_row_var : forall e k,
  eval_mx (row_env e) (row_var k) = e`_k :> 'rV_d.
Proof. by move=> e k; apply/rowP=> i; rewrite !mxE /= nth_row_env. Qed.

Definition Exists_row_form k (f : form) :=
  foldr GRing.Exists f (map (fun i : 'I_d => k * d + i)%N (enum 'I_d)).

Lemma Exists_rowP : forall e k f,
  d > 0 ->
   ((exists v : 'rV[F]_d, holds (row_env (set_nth 0 e k v)) f)
      <-> holds (row_env e) (Exists_row_form k f)).
Proof.
move=> e k f d_gt0; pose i_ j := Ordinal (ltn_pmod j d_gt0).
have d_eq : forall j, (j = j %/ d * d + i_ j)%N := divn_eq^~ d.
split=> [[v f_v] | ]; last case/GRing.foldExistsP=> e' ee' f_e'.
  apply/GRing.foldExistsP; exists (row_env (set_nth 0 e k v)) => {f f_v}// j.
  rewrite [j]d_eq !nth_row_env nth_set_nth /=; case: eqP => // ->.
  by case/mapP; exists (i_ j); rewrite ?mem_enum.
exists (\row_i e'`_(k * d + i)); apply: eq_holds f_e' => j /=.
move/(_ j): ee'; rewrite [j]d_eq !nth_row_env nth_set_nth /=.
case: eqP => [-> | ne_j_k -> //]; first by rewrite mxE.
apply/mapP=> [[r lt_r_d]]; rewrite -d_eq => def_j; case: ne_j_k.
by rewrite def_j divn_addl_mul // divn_small ?addn0.
Qed.

End Env.

End MatrixFormula.

End MatrixFormula.

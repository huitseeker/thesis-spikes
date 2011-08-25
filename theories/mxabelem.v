(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup gseries nilpotent sylow.
Require Import maximal abelian matrix mxalgebra mxrepresentation.

(******************************************************************************)
(*   This file completes the theory developed in mxrepresentation.v with the  *)
(* construction and properties of linear representations over finite fields,  *)
(* and in particular the correspondance between internal action on a (normal) *)
(* elementary abelian p-subgroup and a linear representation on an Fp-module. *)
(*   We provide the following next constructions for a finite field F:        *)
(*        'Zm%act == the action of {unit F} on 'M[F]_(m, n).                  *)
(*         rowg A == the additive group of 'rV[F]_n spanned by the row space  *)
(*                   of the matrix A.                                         *)
(*      rowg_mx L == the partial inverse to rowg; for any 'Zm-stable group L  *)
(*                   of 'rV[F]_n we have rowg (rowg_mx L) = L.                *)
(*     GLrepr F n == the natural, faithful representation of 'GL_n[F].        *)
(*     reprGLm rG == the morphism G >-> 'GL_n[F] equivalent to the            *)
(*                   representation r of G (with rG : mx_repr r G).           *)
(*   ('MR rG)%act == the action of G on 'rV[F]_n equivalent to the            *)
(*                   representation r of G (with rG : mx_repr r G).           *)
(* The second set of constructions defines the interpretation of a normal     *)
(* non-trivial elementary abelian p-subgroup as an 'F_p module. We assume     *)
(* abelE : p.-abelem E and ntE : E != 1, throughout, as these are needed to   *)
(* build the isomorphism between E and a nontrivial 'rV['F_p]_n.              *)
(*         'rV(E) == the type of row vectors of the 'F_p module equivalent    *)
(*                   to E when E is a non-trivial p.-abelem group.            *)
(*          'M(E) == the type of matrices corresponding to E.                 *)
(*         'dim E == the width of vectors/matrices in 'rV(E) / 'M(E).         *)
(* abelem_rV abelE ntE == the one-to-one injection of E onto 'rV(E).          *)
(*  rVabelem abelE ntE == the one-to-one projection of 'rV(E) onto E.         *)
(* abelem_repr abelE ntE nEG == the representation of G on 'rV(E) that is     *)
(*                   equivalent to conjugation by G in E; here abelE, ntE are *)
(*                   as above, and G \subset 'N(E).                           *)
(* This file end with basic results on p-modular representations of p-groups, *)
(* and theorems giving the structure of the representation of extraspecial    *)
(* groups; these results use somewhat more advanced group theory than the     *)
(* rest of mxrepresentation, in particular, results of sylow.v and maximal.v. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* Special results for representations on a finite field. In this case, the   *)
(* representation is equivalent to a morphism into the general linear group   *)
(* 'GL_n[F]. It is furthermore equivalent to a group action on the finite     *)
(* additive group of the corresponding row space 'rV_n. In addition, row      *)
(* spaces of matrices in 'M[F]_n correspond to subgroups of that vector group *)
(* (this is only surjective when F is a prime field 'F_p), with moduleules    *)
(* corresponding to subgroups stabilized by the external action.              *)

Section FiniteRepr.

Variable F : finFieldType.

(* The external group action (by scaling) of the multiplicative unit group   *)
(* of the finite field, and the correspondence between additive subgroups    *)
(* of row vectors that are stable by this action, and the matrix row spaces. *)
Section ScaleAction.

Variables m n : nat.

Definition scale_act (A : 'M[F]_(m, n)) (a : {unit F}) := val a *: A.
Lemma scale_actE : forall A a, scale_act A a = val a *: A. Proof. by []. Qed.
Lemma scale_is_action : is_action setT scale_act.
Proof.
apply: is_total_action=> [A | A a b]; rewrite /scale_act ?scale1r //.
by rewrite ?scalerA mulrC.
Qed.
Canonical Structure scale_action := Action scale_is_action.
Lemma scale_is_groupAction : is_groupAction setT scale_action.
Proof.
move=> a _ /=; rewrite inE; apply/andP.
split; first by apply/subsetP=> ?; rewrite !inE.
by apply/morphicP=> u A _ _ /=; rewrite !actpermE /= /scale_act scaler_addr.
Qed.
Canonical Structure scale_groupAction := GroupAction scale_is_groupAction.

Lemma astab1_scale_act : forall A, A != 0 -> 'C[A | scale_action] = 1%g.
Proof.
move=> A; rewrite -mxrank_eq0=> nzA; apply/trivgP; apply/subsetP=> a.
apply: contraLR; rewrite !inE -val_eqE -subr_eq0 sub1set !inE => nz_a1.
by rewrite -subr_eq0 -scaleN1r -scaler_addl -mxrank_eq0 eqmx_scale.
Qed.

End ScaleAction.

Local Notation "'Zm" := (scale_action _ _) (at level 0) : action_scope.

Section RowGroup.

Variable n : nat.
Local Notation rVn := 'rV[F]_n.

Definition rowg m (A : 'M[F]_(m, n)) : {set rVn} := [set u | u <= A]%MS.

Lemma mem_rowg : forall m A v, (v \in @rowg m A) = (v <= A)%MS.
Proof. by move=> m A v; rewrite inE. Qed.

Lemma rowg_group_set : forall m A, group_set (@rowg m A).
Proof.
move=> m A; apply/group_setP.
by split=> [|u v]; rewrite !inE ?sub0mx //; exact: addmx_sub.
Qed.
Canonical Structure rowg_group m A := Group (@rowg_group_set m A).

Lemma rowg_stable : forall m (A : 'M_(m, n)), [acts setT, on rowg A | 'Zm].
Proof.
by move=> m A; apply/actsP=> a _ v; rewrite !inE eqmx_scale // -unitfE (valP a).
Qed.

Lemma rowgS : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (rowg A \subset rowg B) = (A <= B)%MS.
Proof.
move=> m1 m2 A B; apply/subsetP/idP=> sAB => [| u].
  by apply/row_subP=> i; move/(_ (row i A)): sAB; rewrite !inE row_sub => ->.
by rewrite !inE => suA; exact: submx_trans sAB.
Qed.

Lemma eq_rowg : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MS -> rowg A = rowg B.
Proof.
by move=> m1 m2 A B eqAB; apply/eqP; rewrite eqEsubset !rowgS !eqAB andbb.
Qed.

Lemma rowg0 : forall m, rowg (0 : 'M_(m, n)) = 1%g.
Proof.
by move=> m; apply/trivgP; apply/subsetP=> v; rewrite !inE eqmx0 submx0.
Qed.

Lemma rowg1 : rowg 1%:M = setT.
Proof. by apply/setP=> x; rewrite !inE submx1. Qed.

Lemma trivg_rowg : forall m (A : 'M_(m, n)), (rowg A == 1%g) = (A == 0).
Proof. by move=> m A; rewrite -submx0 -rowgS rowg0 (sameP trivgP eqP). Qed.

Definition rowg_mx (L : {set rVn}) := <<\matrix_(i < #|L|) enum_val i>>%MS.

Lemma rowgK : forall m (A : 'M_(m, n)), (rowg_mx (rowg A) :=: A)%MS.
Proof.
move=> m A; apply/eqmxP; rewrite !genmxE; apply/andP; split.
  by apply/row_subP=> i; rewrite rowK; have:= enum_valP i; rewrite /= inE.
apply/row_subP=> i; set v := row i A.
have Av: v \in rowg A by rewrite inE row_sub.
by rewrite (eq_row_sub (enum_rank_in Av v)) // rowK enum_rankK_in.
Qed.

Lemma rowg_mxS : forall L M : {set 'rV[F]_n},
  L \subset M -> (rowg_mx L <= rowg_mx M)%MS.
Proof.
move=> L M; move/subsetP=> sLM; rewrite !genmxE; apply/row_subP=> i.
rewrite rowK; move: (enum_val i) (sLM _ (enum_valP i)) => v Mv.
by rewrite (eq_row_sub (enum_rank_in Mv v)) // rowK enum_rankK_in.
Qed.

Lemma sub_rowg_mx : forall L : {set rVn}, L \subset rowg (rowg_mx L).
Proof.
move=> L; apply/subsetP=> v Lv; rewrite inE genmxE.
by rewrite (eq_row_sub (enum_rank_in Lv v)) // rowK enum_rankK_in.
Qed.

Lemma stable_rowg_mxK : forall L : {group rVn},
  [acts setT, on L | 'Zm] -> rowg (rowg_mx L) = L.
Proof.
move=> L linL; apply/eqP; rewrite eqEsubset sub_rowg_mx andbT.
apply/subsetP => v; rewrite inE genmxE; case/submxP=> u ->{v}.
rewrite mulmx_sum_row group_prod // => i _.
rewrite rowK; move: (enum_val i) (enum_valP i) => v Lv.
case: (eqVneq (u 0 i) 0) => [-> |]; first by rewrite scale0r group1.
by rewrite -unitfE => aP; rewrite ((actsP linL) (FinRing.Unit _ aP)) ?inE.
Qed.

Lemma rowg_mx1 : rowg_mx 1%g = 0.
Proof. by apply/eqP; rewrite -submx0 -(rowg0 0) rowgK sub0mx. Qed.

Lemma rowg_mx_eq0 : forall L : {group rVn}, (rowg_mx L == 0) = (L :==: 1%g).
Proof.
move=> L; rewrite -trivg_rowg; apply/idP/idP.
  by rewrite !(sameP eqP trivgP); apply: subset_trans; exact: sub_rowg_mx.
by move/eqP->; rewrite rowg_mx1 rowg0.
Qed.

Lemma rowgI : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A :&: B)%MS = rowg A :&: rowg B.
Proof. by move=> m1 m2 A B; apply/setP=> u; rewrite !inE sub_capmx. Qed.

Lemma card_rowg : forall m (A : 'M_(m, n)), #|rowg A| = (#|F| ^ \rank A)%N.
Proof.
move=> m A; rewrite -[\rank A]mul1n -card_matrix.
have injA: injective (mulmxr (row_base A)).
  move=> m'; case/row_freeP: (row_base_free A) => A' A'K.
  by apply: can_inj (mulmxr A') _ => u; rewrite /= -mulmxA A'K mulmx1.
rewrite -(card_image (injA _)); apply: eq_card => v.
by rewrite inE -(eq_row_base A); apply/submxP/imageP=> [] [u]; exists u.
Qed.

Lemma rowgD : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A + B)%MS = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEcard mulG_subG /= !rowgS.
rewrite addsmxSl addsmxSr -(@leq_pmul2r #|rowg A :&: rowg B|) ?cardG_gt0 //=.
by rewrite -mul_cardG -rowgI !card_rowg -!expn_add mxrank_sum_cap.
Qed.

(* An alternative proof, which avoids the counting argument.
   It's outcommented because the mem_mulg rewrite takes forever to execute.
Lemma rowgD' : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A + B)%MS = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEsubset mulG_subG /= !rowgS.
rewrite addsmxSl addsmxSr; apply/subsetP=> u; rewrite !inE.
by case/sub_addsmxP=> v suvA svB; rewrite -(mulgKV v u) mem_mulg ?inE.
Qed.
*)

End RowGroup.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable (rG : mx_representation F G n).

Lemma GL_mx_repr : mx_repr 'GL_n[F] GLval. Proof. by []. Qed.
Canonical Structure GLrepr := MxRepresentation GL_mx_repr.

Lemma GLmx_faithful : mx_faithful GLrepr.
Proof. by apply/subsetP=> A; rewrite !inE mul1mx. Qed.

Definition reprGLm x : {'GL_n[F]} := insubd (1%g : {'GL_n[F]}) (rG x).

Lemma val_reprGLm : forall x, x \in G -> val (reprGLm x) = rG x.
Proof. by move=> x Gx; rewrite val_insubd (repr_mx_unitr rG). Qed.

Lemma comp_reprGLm : {in G, GLval \o reprGLm =1 rG}.
Proof. exact: val_reprGLm. Qed.

Lemma reprGLmM : {in G &, {morph reprGLm : x y / x * y}}%g.
Proof.
by move=> x y Gx Gy; apply: val_inj; rewrite /= !val_reprGLm ?groupM ?repr_mxM.
Qed.
Canonical Structure reprGL_morphism := Morphism reprGLmM.

Lemma ker_reprGLm : 'ker reprGLm = rker rG.
Proof.
apply/setP=> x; rewrite !inE mul1mx; case Gx: (x \in G) => //=.
by rewrite -val_eqE val_reprGLm.
Qed.

Definition mx_repr_act (u : 'rV_n) x := u *m val (reprGLm x).

Lemma mx_repr_actE : forall u x, x \in G -> mx_repr_act u x = u *m rG x.
Proof. by move=> u x Gx; rewrite /mx_repr_act val_reprGLm. Qed.

Lemma mx_repr_is_action : is_action G mx_repr_act.
Proof.
split=> [x | u x y Gx Gy]; last by rewrite /mx_repr_act -mulmxA reprGLmM.
apply: can_inj (mulmx^~ (GLval (reprGLm x))^-1) _ => u.
by rewrite mulmxK ?GL_unitmx.
Qed.
Canonical Structure mx_repr_action := Action mx_repr_is_action.

Lemma mx_repr_is_groupAction : is_groupAction setT mx_repr_action.
Proof.
move=> x Gx /=; rewrite !inE.
apply/andP; split; first by apply/subsetP=> u; rewrite !inE.
by apply/morphicP=> /= u v _ _; rewrite !actpermE /= /mx_repr_act mulmx_addl.
Qed.
Canonical Structure mx_repr_groupAction := GroupAction mx_repr_is_groupAction.

Local Notation "''MR' 'rG'" := mx_repr_action (at level 10) : action_scope.
Local Notation "''MR' 'rG'" := mx_repr_groupAction : groupAction_scope.

Lemma astab_rowg_repr : forall m (A : 'M_(m, n)),
  'C(rowg A | 'MR rG) = rstab rG A.
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
apply/subsetP/eqP=> cAx => [|u]; last first.
  by rewrite !inE mx_repr_actE //; case/submxP=> u' ->; rewrite -mulmxA cAx.
apply/row_matrixP=> i; move/implyP: (cAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul; move/eqP.
Qed.

Lemma astabs_rowg_repr : forall m (A : 'M_(m, n)),
  'N(rowg A | 'MR rG) = rstabs rG A.
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
apply/subsetP/idP=> nAx => [|u]; last first.
  rewrite !inE mx_repr_actE // => Au; exact: (submx_trans (submxMr _ Au)).
apply/row_subP=> i; move/implyP: (nAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul.
Qed.

Lemma acts_rowg : forall A : 'M_n, [acts G, on rowg A | 'MR rG] = mxmodule rG A.
Proof. by move=> A; rewrite astabs_rowg_repr. Qed.

Lemma astab_setT_repr : 'C(setT | 'MR rG) = rker rG.
Proof. by rewrite -rowg1 astab_rowg_repr. Qed.

Lemma mx_repr_action_faithful :
  [faithful G, on setT | 'MR rG] = mx_faithful rG.
Proof.
rewrite /faithful astab_setT_repr (setIidPr _) //.
by apply/subsetP=> x; case/setIdP.
Qed.

Lemma afix_repr : forall H : {set gT},
  H \subset G -> 'Fix_('MR rG)(H) = rowg (rfix_mx rG H).
Proof.
move=> H; move/subsetP=> sHG; apply/setP=> /= u; rewrite !inE.
apply/subsetP/rfix_mxP=> cHu x Hx;
  by move/(_ x Hx): cHu; rewrite !inE /=; move/eqP; rewrite mx_repr_actE ?sHG.
Qed.

Lemma gacent_repr : forall H : {set gT},
  H \subset G -> 'C_(| 'MR rG)(H) = rowg (rfix_mx rG H).
Proof. by move=> H sHG; rewrite gacentE // setTI afix_repr. Qed.

End FiniteRepr.

Notation "''Zm'" := (scale_action _ _ _) (at level 0) : action_scope.
Notation "''Zm'" := (scale_groupAction _ _ _) : groupAction_scope.
Notation "''MR' rG" := (mx_repr_action rG)
  (at level 10, rG at level 8, format "''MR'  rG") : action_scope.
Notation "''MR' rG" := (mx_repr_groupAction rG) : groupAction_scope.

Definition abelem_dim' (gT : finGroupType) (E : {set gT}) :=
  (logn (pdiv #|E|) #|E|).-1.
Notation "''dim' E" := (abelem_dim' E).+1
  (at level 10, E at level 8, format "''dim'  E") : group_scope.

Notation "''rV' ( E )" := 'rV_('dim E)
  (at level 8, format "''rV' ( E )") : group_scope.
Notation "''M' ( E )" := 'M_('dim E)
  (at level 8, format "''M' ( E )") : group_scope.
Notation "''rV[' F ] ( E )" := 'rV[F]_('dim E)
  (at level 8, only parsing) : group_scope.
Notation "''M[' F ] ( E )" := 'M[F]_('dim E)
  (at level 8, only parsing) : group_scope.

Section AbelemRepr.

Import FinRing.Theory.

Section FpMatrix.

Variables p m n : nat.
Local Notation Mmn := 'M['F_p]_(m, n).

Lemma mx_Fp_abelem : prime p -> p.-abelem [set: Mmn].
Proof.
move=> p_pr; apply/abelemP=> //; rewrite zmod_abelian.
split=> //= v _; rewrite FinRing.zmodXgE -scaler_nat.
by case/andP: (char_Fp p_pr) => _; move/eqP->; rewrite scale0r.
Qed.

Lemma mx_Fp_stable : forall L : {group Mmn}, [acts setT, on L | 'Zm].
Proof.
move=> L; apply/subsetP=> a _; rewrite !inE; apply/subsetP=> A L_A.
by rewrite inE /= /scale_act -[val _]natr_Zp scaler_nat groupX.
Qed.

End FpMatrix.

Section FpRow.

Variables p n : nat.
Local Notation rVn := 'rV['F_p]_n.

Lemma rowg_mxK : forall L : {group rVn}, rowg (rowg_mx L) = L.
Proof. move=> L; apply: stable_rowg_mxK; exact: mx_Fp_stable. Qed.

Lemma rowg_mxSK : forall (L : {set rVn}) (M : {group rVn}),
  (rowg_mx L <= rowg_mx M)%MS = (L \subset M).
Proof.
move=> L M; apply/idP/idP; last exact: rowg_mxS.
by rewrite -rowgS rowg_mxK; apply: subset_trans; exact: sub_rowg_mx.
Qed.

End FpRow.

Variables (p : nat) (gT : finGroupType) (E : {group gT}).
Hypotheses (abelE : p.-abelem E) (ntE : E :!=: 1%g).

Let pE : p.-group E := abelem_pgroup abelE.
Let p_pr : prime p. Proof. by have [] := pgroup_pdiv pE ntE. Qed.

Local Notation n' := (abelem_dim' (gval E)).
Local Notation n := n'.+1.
Local Notation rVn := 'rV['F_p](gval E).

Lemma dim_abelemE : n = logn p #|E|.
Proof.
rewrite /n'; have [_ _ [k ->]] :=  pgroup_pdiv pE ntE.
by rewrite /pdiv primes_exp ?primes_prime // pfactorK.
Qed.

Lemma card_abelem_rV : #|rVn| = #|E|.
Proof.
by rewrite dim_abelemE card_matrix mul1n card_Fp // -p_part part_pnat_id.
Qed.

Lemma isog_abelem_rV : E \isog [set: rVn].
Proof.
by rewrite (isog_abelem_card _ abelE) cardsT card_abelem_rV mx_Fp_abelem /=.
Qed.

Let ab_rV_P := (existsP isog_abelem_rV).
Definition abelem_rV : gT -> rVn := xchoose ab_rV_P.

Local Notation ErV := abelem_rV.

Lemma abelem_rV_M : {in E &, {morph ErV : x y / (x * y)%g >-> x + y}}.
Proof. by case/misomP: (xchooseP ab_rV_P) => fM _; move/morphicP: fM. Qed.

Canonical Structure abelem_rV_morphism := Morphism abelem_rV_M.

Lemma abelem_rV_isom : isom E setT ErV.
Proof. by case/misomP: (xchooseP ab_rV_P). Qed.

Lemma abelem_rV_injm : 'injm ErV. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma abelem_rV_inj : {in E &, injective ErV}.
Proof. by apply/injmP; exact: abelem_rV_injm. Qed.

Lemma im_abelem_rV : ErV @* E = setT. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma mem_im_abelem_rV : forall u, u \in ErV @* E.
Proof. by move=> u; rewrite im_abelem_rV inE. Qed.

Lemma sub_im_abelem_rV : forall mA, subset mA (mem (ErV @* E)).
Proof.
by rewrite unlock => mA; apply/pred0P=> v /=; rewrite mem_im_abelem_rV.
Qed.
Hint Resolve mem_im_abelem_rV sub_im_abelem_rV.

Lemma abelem_rV_1 : ErV 1 = 0%R. Proof. by rewrite morph1. Qed.

Lemma abelem_rV_X : forall x i, x \in E -> ErV (x ^+ i) = i%:R *: ErV x.
Proof. by move=> x i Ex; rewrite morphX // scaler_nat. Qed.

Lemma abelem_rV_V : forall x, x \in E -> ErV x^-1 = - ErV x.
Proof. by move=> x Ex; rewrite morphV. Qed.

Definition rVabelem : rVn -> gT := invm abelem_rV_injm.
Canonical Structure rVabelem_morphism := [morphism of rVabelem].
Local Notation rV_E := rVabelem.

Lemma rVabelem0 : rV_E 0 = 1%g. Proof. exact: morph1. Qed.

Lemma rVabelemD : {morph rV_E : u v / u + v >-> (u * v)%g}.
Proof. by move=> u v /=; rewrite -morphM. Qed.

Lemma rVabelemN : {morph rV_E: u / - u >-> (u^-1)%g}.
Proof. by move=> u /=; rewrite -morphV. Qed.

Lemma rVabelemZ : forall m : 'F_p, {morph rV_E : u / m *: u >-> (u ^+ m)%g}.
Proof.
by move=> m u /=; rewrite -morphX /= -?[(u ^+ m)%g]scaler_nat ?natr_Zp.
Qed.

Lemma abelem_rV_K : {in E, cancel ErV rV_E}. Proof. exact: invmE. Qed.

Lemma rVabelemK : cancel rV_E ErV. Proof. by move=> u; rewrite invmK. Qed.

Lemma rVabelem_inj : injective rV_E. Proof. exact: can_inj rVabelemK. Qed.

Lemma rVabelem_injm : 'injm rV_E. Proof. exact: injm_invm abelem_rV_injm. Qed.

Lemma im_rVabelem : rV_E @* setT = E.
Proof. by rewrite -im_abelem_rV im_invm. Qed.

Lemma mem_rVabelem : forall u, rV_E u \in E.
Proof. by move=> u; rewrite -im_rVabelem mem_morphim. Qed.

Lemma sub_rVabelem : forall L, rV_E @* L \subset E.
Proof. by move=> L; rewrite -[_ @* L]morphimIim im_invm subsetIl. Qed.
Hint Resolve mem_rVabelem sub_rVabelem.

Lemma card_rVabelem : forall L, #|rV_E @* L| = #|L|.
Proof. by move=> L; rewrite card_injm ?rVabelem_injm. Qed.

Lemma abelem_rV_mK : forall H : {set gT}, H \subset E -> rV_E @* (ErV @* H) = H.
Proof. exact: morphim_invm abelem_rV_injm. Qed.

Lemma rVabelem_mK : forall L, ErV @* (rV_E @* L) = L.
Proof. by move=> L; rewrite morphim_invmE morphpreK. Qed.

Lemma rVabelem_minj : injective (morphim (MorPhantom rV_E)).
Proof. exact: can_inj rVabelem_mK. Qed.

Lemma rVabelemS : forall L M, (rV_E @* L \subset rV_E @* M) = (L \subset M).
Proof. by move=> L M; rewrite injmSK ?rVabelem_injm. Qed.

Lemma abelem_rV_S : forall H K : {set gT},
  H \subset E -> (ErV @* H \subset ErV @* K) = (H \subset K).
Proof. by move=> H K sHE; rewrite injmSK ?abelem_rV_injm. Qed.

Lemma sub_rVabelem_im : forall L (H : {set gT}),
  (rV_E @* L \subset H) = (L \subset ErV @* H).
Proof. by move=> L H; rewrite sub_morphim_pre ?morphpre_invm. Qed.

Lemma sub_abelem_rV_im : forall (H : {set gT}) (L : {set 'rV['F_p]_n}),
  H \subset E -> (ErV @* H \subset L) = (H \subset rV_E @* L).
Proof. by move=> H L sHE; rewrite sub_morphim_pre ?morphim_invmE. Qed.

Variable G : {group gT}.
Definition abelem_mx_fun (g : subg_of G) v := ErV ((rV_E v) ^ val g).
Definition abelem_mx of G \subset 'N(E) :=
  fun x => lin1_mx (abelem_mx_fun (subg G x)).

Hypothesis nEG : G \subset 'N(E).
Local Notation r := (abelem_mx nEG).

Lemma abelem_mx_linear_proof : forall g, linear (abelem_mx_fun g).
Proof.
rewrite /abelem_mx_fun; case=> x /=; move/(subsetP nEG)=> Nx /= m u v.
rewrite rVabelemD rVabelemZ conjMg conjXg.
by rewrite abelem_rV_M ?abelem_rV_X ?groupX ?memJ_norm // natr_Zp.
Qed.
Canonical Structure abelem_mx_linear g := Linear (abelem_mx_linear_proof g).

Let rVabelemJmx : forall v x, x \in G -> rV_E (v *m r x) = (rV_E v) ^ x.
Proof.
move=> v x Gx; rewrite /= mul_rV_lin1 /= /abelem_mx_fun subgK //.
by rewrite abelem_rV_K // memJ_norm // (subsetP nEG).
Qed.

Lemma abelem_mx_repr : mx_repr G r.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; apply: rVabelem_inj.
  by rewrite rowE -row1 rVabelemJmx // conjg1.
by rewrite !rowE mulmxA !rVabelemJmx ?groupM // conjgM.
Qed.
Canonical Structure abelem_repr := MxRepresentation abelem_mx_repr.
Let rG := abelem_repr.

Lemma rVabelemJ : forall v x, x \in G -> rV_E (v *m rG x) = (rV_E v) ^ x.
Proof. exact: rVabelemJmx. Qed.

Lemma abelem_rV_J : {in E & G, forall x y, ErV (x ^ y) = ErV x *m rG y}.
Proof.
by move=> x y Ex Gy; rewrite -{1}(abelem_rV_K Ex) -rVabelemJ ?rVabelemK.
Qed.

Lemma abelem_rowgJ : forall m (A : 'M_(m, n)) x,
  x \in G -> rV_E @* rowg (A *m rG x) = (rV_E @* rowg A) :^ x.
Proof.
move=> m A x Gx; apply: (canRL (conjsgKV _)); apply/setP=> y.
rewrite mem_conjgV !morphim_invmE !inE memJ_norm ?(subsetP nEG) //=.
case Ey: (y \in E) => //=; rewrite abelem_rV_J //.
by rewrite submxMfree // row_free_unit (repr_mx_unit rG).
Qed.

Lemma rV_abelem_sJ : forall (L : {group gT}) x,
  x \in G -> L \subset E -> ErV @* (L :^ x) = rowg (rowg_mx (ErV @* L) *m rG x).
Proof.
move=> L x Gx sLE; apply: rVabelem_minj; rewrite abelem_rowgJ //.
by rewrite rowg_mxK !morphim_invm // -(normsP nEG x Gx) conjSg.
Qed.

Lemma rstab_abelem : forall m (A : 'M_(m, n)),
  rstab rG A = 'C_G(rV_E @* rowg A).
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx : (x \in G) => //=.
apply/eqP/centP=> cAx => [u|].
  case/morphimP=> u' _; rewrite inE; case/submxP=> u'' -> ->{u u'}.
  symmetry; apply/commgP; apply/conjg_fixP.
  by rewrite -rVabelemJ -?mulmxA ?cAx.
apply/row_matrixP=> i; apply: rVabelem_inj.
by rewrite row_mul rVabelemJ // /conjg -cAx ?mulKg ?mem_morphim // inE row_sub.
Qed.

Lemma rstabs_abelem : forall m (A : 'M_(m, n)),
  rstabs rG A = 'N_G(rV_E @* rowg A).
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx : (x \in G) => //.
by rewrite -rowgS -rVabelemS abelem_rowgJ.
Qed.

Lemma rstabs_abelem_rowg_mx : forall L : {group gT},
  L \subset E -> rstabs rG (rowg_mx (ErV @* L)) = 'N_G(L).
Proof. by move=> L sLE; rewrite rstabs_abelem rowg_mxK morphim_invm. Qed.

Lemma abelem_mx_irrP : reflect (mx_irreducible rG) (minnormal E G).
Proof.
apply: (iffP mingroupP) => [[_ minE]|irrG].
  apply/mx_irrP; split=> // U; rewrite /mxmodule rstabs_abelem //.
  rewrite subsetI subxx /= -trivg_rowg.
  rewrite -(inj_eq rVabelem_minj) morphim1; set L := _ @* _ U => nLG ntL. 
  by rewrite -sub1mx -rowgS -rVabelemS -/L [L]minE ?ntL /=.
rewrite ntE; split=> // L; case/andP=> ntL nLG sLE; apply/eqP.
rewrite eqEsubset sLE -im_rVabelem sub_rVabelem_im //= -rowg_mxSK //.
move/setIidPl: nLG; rewrite -rstabs_abelem_rowg_mx //.
set U := rowg_mx _ => Umod; rewrite submx_full //.
case/mx_irrP: irrG => _ -> //; first by rewrite /mxmodule Umod.
apply: contra ntL; rewrite rowg_mx_eq0 !(sameP eqP trivgP).
by rewrite sub_abelem_rV_im // morphim1.
Qed.

Lemma rfix_abelem : forall H : {set gT},
  H \subset G -> (rfix_mx rG H :=: rowg_mx (ErV @* 'C_E(H)%g))%MS.
Proof.
move=> H; move/subsetP=> sHG; apply/eqmxP; apply/andP; split.
  rewrite -rowgS rowg_mxK -sub_rVabelem_im // subsetI sub_rVabelem /=.
  apply/centsP=> y; case/morphimP=> v _; rewrite inE => cGv ->{y} x Gx.
  by apply/commgP; apply/conjg_fixP; rewrite /= -rVabelemJ ?sHG ?(rfix_mxP H _).
rewrite genmxE; apply/rfix_mxP=> x Hx.
apply/row_matrixP=> i; rewrite row_mul rowK.
case/morphimP: (enum_valP i) => z Ez; case/setIP=> _ cHz ->.
by rewrite -abelem_rV_J ?sHG // conjgE (centP cHz) ?mulKg.
Qed.

Lemma rker_abelem : rker rG = 'C_G(E).
Proof. by rewrite /rker rstab_abelem rowg1 im_rVabelem. Qed.

Lemma abelem_mx_faithful : 'C_G(E) = 1%g -> mx_faithful rG.
Proof. by rewrite /mx_faithful rker_abelem => ->. Qed.
  
End AbelemRepr.

Section ModularRepresentation.

Variables (F : fieldType) (p : nat) (gT : finGroupType).
Hypothesis charFp : p \in [char F].
Implicit Types G H : {group gT}.

(* This is Gorenstein, Lemma 2.6.3. *)
Lemma rfix_pgroup_char : forall G H n (rG : mx_representation F G n),
  n > 0 -> p.-group H -> H \subset G -> rfix_mx rG H != 0.
Proof.
move=> G H n rG n_gt0 pH sHG; rewrite -(rfix_subg rG sHG).
move: {2}_.+1 (ltnSn (n + #|H|)) {rG G sHG}(subg_repr _ _) => m.
elim: m gT H pH => // m IHm gT' G pG in n n_gt0 *; rewrite ltnS => le_nG_m rG.
apply/eqP=> Gregular; have irrG: mx_irreducible rG.
  apply/mx_irrP; split=> // U modU; rewrite -mxrank_eq0 -lt0n => Unz.
  rewrite /row_full eqn_leq rank_leq_col leqNgt; apply/negP=> ltUn. 
  have: rfix_mx (submod_repr modU) G != 0.
    by apply: IHm => //; apply: leq_trans le_nG_m; rewrite ltn_add2r.
  by rewrite -mxrank_eq0 (rfix_submod modU) // Gregular capmx0 linear0 mxrank0.
have{m le_nG_m IHm} faithfulG: mx_faithful rG.
  apply/trivgP; apply/eqP; apply/idPn; set C := _ rG => ntC.
  suffices: rfix_mx (kquo_repr rG) (G / _)%g != 0.
    by rewrite -mxrank_eq0 rfix_quo // Gregular mxrank0.
  apply: (IHm _ _ (morphim_pgroup _ _)) => //.
  by apply: leq_trans le_nG_m; rewrite ltn_add2l ltn_quotient // rstab_sub.
have{Gregular} ntG: G :!=: 1%g.
  apply: contraL n_gt0; move/eqP=> G1; rewrite -leqNgt -(mxrank1 F n).
  rewrite -(mxrank0 F n n) -Gregular mxrankS //; apply/rfix_mxP=> x.
  by rewrite {1}G1 mul1mx; move/set1P->; rewrite repr_mx1.
have p_pr: prime p by case/andP: charFp.
have{ntG pG} [z]: {z | z \in 'Z(G) & #[z] = p}; last case/setIP=> Gz cGz ozp.
  apply: Cauchy => //; apply: contraR ntG; rewrite -p'natE // => p'Z.
  have pZ: p.-group 'Z(G) by rewrite (pgroupS (center_sub G)).
  by rewrite (trivg_center_pgroup pG (card1_trivg (pnat_1 pZ p'Z))).
have{cGz} cGz1: centgmx rG (rG z - 1%:M).
  apply/centgmxP=> x Gx; rewrite mulmx_subl mulmx_subr mulmx1 mul1mx.
  by rewrite -!repr_mxM // (centP cGz).
have{irrG faithfulG cGz1} Urz1: rG z - 1%:M \in unitmx.
  apply: (mx_Schur irrG) cGz1 _; rewrite subr_eq0.
  move/implyP: (subsetP faithfulG z).
  by rewrite !inE Gz mul1mx -order_eq1 ozp -implybNN neq_ltn orbC prime_gt1.
do [case: n n_gt0 => // n' _; set n := n'.+1] in rG Urz1 *.
have charMp: p \in [char 'M[F]_n].
  exact: (rmorph_char (scalar_mx_rmorphism _ _)).
have{Urz1}: GRing.unit (Frobenius_aut charMp (rG z - 1)) by rewrite unitr_exp.
rewrite (Frobenius_aut_sub_comm _ (commr1 _)) Frobenius_aut_1.
by rewrite -[_ (rG z)](repr_mxX rG) // -ozp expg_order repr_mx1 subrr unitr0.
Qed.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).

Lemma pcore_sub_rstab_mxsimple : forall M,
  mxsimple rG M -> 'O_p(G) \subset rstab rG M.
Proof.
move=> M [modM nzM simM]; have sGpG := pcore_sub p G.
rewrite rfix_mx_rstabC //; set U := rfix_mx _ _.
have:= simM (M :&: U)%MS; rewrite sub_capmx submx_refl.
apply; rewrite ?capmxSl //.
  rewrite capmx_module // normal_rfix_mx_module ?pcore_normal //.
rewrite -(in_submodK (capmxSl _ _)) val_submod_eq0 -submx0.
rewrite -(rfix_submod modM) // submx0 rfix_pgroup_char ?pcore_pgroup //.
by rewrite lt0n mxrank_eq0.
Qed.

Lemma pcore_sub_rker_mx_irr : mx_irreducible rG -> 'O_p(G) \subset rker rG.
Proof. exact: pcore_sub_rstab_mxsimple. Qed.

(* This is Gorenstein, Lemma 3.1.3. *)
Lemma pcore_faithful_mx_irr :
  mx_irreducible rG -> mx_faithful rG -> 'O_p(G) = 1%g.
Proof.
move=> irrG ffulG; apply/trivgP; apply: subset_trans ffulG.
exact: pcore_sub_rstab_mxsimple.
Qed.

End ModularRepresentation.

Section Extraspecial.

Variables (F : fieldType) (gT : finGroupType) (S : {group gT}) (p n : nat).
Hypotheses (pS : p.-group S) (esS : extraspecial S).
Hypothesis oSpn : #|S| = (p ^ n.*2.+1)%N.
Hypotheses (splitF : group_splitting_field F S) (F'S : [char F]^'.-group S).

Let p_pr := extraspecial_prime pS esS.
Let p_gt0 := prime_gt0 p_pr.
Let p_gt1 := prime_gt1 p_pr.
Let oZp := card_center_extraspecial pS esS.

Let modIp' : forall i : 'I_p.-1, (i.+1 %% p = i.+1)%N.
Proof. by case=> i; rewrite /= -ltnS prednK //; exact: modn_small. Qed.

(* This is Aschbacher (34.9), parts (1)-(4). *)
Theorem extraspecial_repr_structure : forall sS : irrType F S,
  [/\ #|linear_irr sS| = (p ^ n.*2)%N,
      exists iphi : 'I_p.-1 -> sS, let phi i := irr_repr (iphi i) in
        [/\ injective iphi,
            codom iphi =i ~: linear_irr sS,
            forall i, mx_faithful (phi i),
            forall z, z \in 'Z(S)^# ->
              exists2 w, primitive_root_of_unity p w
                       & forall i, phi i z = (w ^+ i.+1)%:M
          & forall i, irr_degree (iphi i) = (p ^ n)%N]
    & #|sS| = (p ^ n.*2 + p.-1)%N].            
Proof.
move=> sS; have [[defPhiS defS'] prZ] := esS; set linS := linear_irr sS.
have nb_lin: #|linS| = (p ^ n.*2)%N.
  rewrite card_linear_irr // -divgS ?der_sub //=.
  by rewrite oSpn defS' oZp expnS mulKn.
have nb_irr: #|sS| = (p ^ n.*2 + p.-1)%N.
  pose Zcl := classes S ::&: 'Z(S).
  have cardZcl: #|Zcl| = p.
    transitivity #|[set [set z] | z <- 'Z(S)]|; last first.
      by rewrite card_imset //; exact: set1_inj.
    apply: eq_card => zS; apply/setIdP/imsetP=> [[] | [z]].
      case/imsetP=> z Sz ->{zS} szSZ.
      have Zz: z \in 'Z(S) by rewrite (subsetP szSZ) ?class_refl.
      exists z => //; rewrite inE Sz in Zz.
      apply/eqP; rewrite eq_sym eqEcard sub1set class_refl cards1.
      by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
    case/setIP=> Sz cSz ->{zS}; rewrite sub1set inE Sz; split=> //.
    apply/imsetP; exists z; rewrite //.
    apply/eqP; rewrite eqEcard sub1set class_refl cards1.
    by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
  move/eqP: (class_formula S); rewrite (bigID (mem Zcl)) /=.
  rewrite (eq_bigr (fun _ => 1%N)) => [|zS]; last first.
    case/andP=> _; case/setIdP; case/imsetP=> z Sz ->{zS}.
    rewrite subsetI; case/andP=> _ cSzS.
    rewrite (setIidPl _) ?indexgg // sub_cent1 (subsetP cSzS) //.
    exact: mem_repr (class_refl S z).
  rewrite sum1dep_card setIdE (setIidPr _) 1?cardsE ?cardZcl; last first.
    by apply/subsetP=> zS; rewrite 2!inE; case/andP.
  have pn_gt0: p ^ n.*2 > 0 by rewrite expn_gt0 p_gt0.
  rewrite card_irr // oSpn expnS -(prednK pn_gt0) mulnS eqn_addl.
  rewrite (eq_bigr (fun _ => p)) => [|xS]; last first.
    case/andP=> SxS; rewrite inE SxS; case/imsetP: SxS => x Sx ->{xS} notZxS.
    have [y Sy ->] := repr_class S x; apply: p_maximal_index => //.
    apply: cent1_extraspecial_maximal => //; first exact: groupJ.
    apply: contra notZxS => Zxy; rewrite -{1}(lcoset_id Sy) class_lcoset.
    rewrite ((_ ^: _ =P [set x ^ y])%g _) ?sub1set // eq_sym eqEcard.
    rewrite sub1set class_refl cards1 -index_cent1 (setIidPl _) ?indexgg //.
    by rewrite sub_cent1; apply: subsetP Zxy; exact: subsetIr.
  rewrite sum_nat_dep_const mulnC eqn_pmul2l //; move/eqP <-.
  rewrite addSnnS prednK // -cardZcl -[card _](cardsID Zcl) /= addnC.
  by congr (_ + _)%N; apply: eq_card => t; rewrite !inE andbC // andbAC andbb.
have fful_nlin: forall i, i \in ~: linS -> mx_faithful (irr_repr i).
  move=> i; rewrite !inE => nlin_phi.
  apply/trivgP; apply: (TI_center_nil (pgroup_nil pS) (rker_normal _)).
  rewrite setIC; apply: (prime_TIg prZ); rewrite /= -defS' der1_sub_rker //.
  exact: socle_irr.
have [i0 nlin_i0]: exists i0, i0 \in ~: linS.
  by apply/card_gt0P; rewrite cardsCs setCK nb_irr nb_lin addKn -subn1 subn_gt0.
have [z defZ]: exists z, 'Z(S) = <[z]> by apply/cyclicP; rewrite prime_cyclic.
have Zz: z \in 'Z(S) by [rewrite defZ cycle_id]; have [Sz cSz] := setIP Zz.
have ozp: #[z] = p by rewrite -oZp defZ.
have ntz: z != 1%g by rewrite -order_gt1 ozp.
pose phi := irr_repr i0; have irr_phi: mx_irreducible phi := socle_irr i0.
pose w := irr_mode i0 z.
have phi_z: phi z = w%:M by rewrite /phi irr_center_scalar.
have phi_ze: forall e, phi (z ^+ e)%g = (w ^+ e)%:M.
  by move=> e; rewrite /phi irr_center_scalar ?groupX ?irr_modeX.
have wp1: w ^+ p = 1 by rewrite -irr_modeX // -ozp expg_order irr_mode1.
have injw: {in 'Z(S) &, injective (irr_mode i0)}.
  move=> x y Zx Zy /= eq_xy; have [[Sx _] [Sy _]] := (setIP Zx, setIP Zy). 
  apply: mx_faithful_inj (fful_nlin _ nlin_i0) _ _ Sx Sy _.
  by rewrite !{1}irr_center_scalar ?eq_xy; first by split.
have prim_w: forall e, 0 < e < p -> p.-primitive_root (w ^+ e).
  move=> e; case/andP=> e_gt0 lt_e_p; apply/andP; split=> //.
  apply/forallP=> [[d ltdp] /=]; apply/eqP; rewrite unity_rootE -exprn_mulr.
  rewrite -(irr_mode1 i0) -irr_modeX // (inj_in_eq injw) ?groupX ?group1 //.
  rewrite -order_dvdn ozp euclid // gtnNdvd //=; move: ltdp; rewrite leq_eqVlt.
  by case: eqP => [-> _ | _ ltd1p]; rewrite (dvdnn, gtnNdvd).
have [a defAutZ]: exists a, Aut 'Z(S) = <[a]>.
  by apply/cyclicP; rewrite Aut_prime_cyclic ?ozp.
have phi_unitP : forall i : 'I_p.-1, GRing.unit (i.+1%:R : 'Z_#[z]).
  move=> i; rewrite /GRing.unit /= ozp val_Zp_nat ?Zp_cast //.
  by rewrite prime_coprime // -lt0n !modIp'.
pose ephi i := invm (injm_Zpm a) (Zp_unitm (Sub _ (phi_unitP i))).
pose j : 'Z_#[z] := val (invm (injm_Zp_unitm z) a).
have co_j_p: coprime j p.
  rewrite coprime_sym /j; case: (invm _ a) => /=.
  by rewrite ozp /GRing.unit /= Zp_cast.
have [alpha Aut_alpha alphaZ] := center_aut_extraspecial pS esS co_j_p.
have alpha_i_z: forall i, ((alpha ^+ ephi i) z = z ^+ i.+1)%g.
  move=> i; transitivity ((a ^+ ephi i) z)%g.
    elim: (ephi i : nat) => // e IHe; rewrite !expgS !permM alphaZ //.
    have Aut_a: a \in Aut 'Z(S) by rewrite defAutZ cycle_id.
    rewrite -{2}[a](invmK (injm_Zp_unitm z)); last by rewrite im_Zp_unitm -defZ.
    rewrite /= autE ?cycle_id // -/j /= /cyclem.
    rewrite -(autmE (groupX _ Aut_a)) -(autmE (groupX _ Aut_alpha)).
    by rewrite !morphX //= !autmE IHe.
  rewrite [(a ^+ _)%g](invmK (injm_Zpm a)) /=; last first.
    by rewrite im_Zpm -defAutZ defZ Aut_aut.
  by rewrite autE ?cycle_id //= val_Zp_nat ozp ?modIp'.
have rphiP: forall i, S :==: autm (groupX (ephi i) Aut_alpha) @* S.
  by move=> i; rewrite im_autm.
pose rphi i := morphim_repr (eqg_repr phi (rphiP i)) (subxx S).
have rphi_irr: forall i, mx_irreducible (rphi i).
  by move=> i; apply/morphim_mx_irr; exact/eqg_mx_irr.
have rphi_fful: forall i, mx_faithful (rphi i).
  move=> i; rewrite /mx_faithful rker_morphim rker_eqg.
  by rewrite (trivgP (fful_nlin _ nlin_i0)) morphpreIdom; exact: injm_autm.
have rphi_z: forall i, rphi i z = (w ^+ i.+1)%:M.
  move=> i; rewrite /rphi [phi]lock /= /morphim_mx autmE alpha_i_z -lock.
  by rewrite phi_ze.
pose iphi i := irr_comp sS (rphi i); pose phi_ i := irr_repr (iphi i).
have{phi_ze} phi_ze: forall i e, phi_ i (z ^+ e)%g = (w ^+ (e * i.+1)%N)%:M.
  move=> i e; rewrite /phi_ !{1}irr_center_scalar ?groupX ?irr_modeX //.
  suffices ->: irr_mode (iphi i) z = w ^+ i.+1 by rewrite mulnC exprn_mulr.
  have:= mx_rsim_sym (rsim_irr_comp sS F'S (rphi_irr i)).
  case/mx_rsim_def=> B [B' _ homB]; rewrite /irr_mode homB // rphi_z.
  rewrite -{1}scalemx1 -scalemxAr -scalemxAl -{1}(repr_mx1 (rphi i)).
  by rewrite -homB // repr_mx1 scalemx1 mxE.
have inj_iphi: injective iphi.
  move=> i1 i2 eqi12; apply/eqP.
  move/eqP: (congr1 (fun i => irr_mode i (z ^+ 1)) eqi12).
  rewrite /irr_mode !{1}[irr_repr _ _]phi_ze !{1}mxE !mul1n.
  by rewrite (eq_prim_root_expr (prim_w 1%N p_gt1)) !modIp'.
have deg_phi: forall i, irr_degree (iphi i) = irr_degree i0.
  by move=> i; case: (rsim_irr_comp sS F'S (rphi_irr i)).
have im_iphi: codom iphi =i ~: linS.
  apply/subset_cardP.
    by rewrite card_image // card_ord cardsCs setCK nb_irr nb_lin addKn.
  apply/subsetP=> fi; case/imageP=> i _ ->.
  by rewrite !inE /= (deg_phi i) in nlin_i0 *.
split=> //; exists iphi; rewrite -/phi_.
split=> // [i | ze | i].
- have sim_i := rsim_irr_comp sS F'S (rphi_irr i).
  by rewrite -(mx_rsim_faithful sim_i) rphi_fful.
- rewrite {1}defZ 2!inE andbC; case/andP.
  case/cyclePmin=> e; rewrite ozp => lt_e_p ->{ze}.
  case: (posnP e) => [-> | e_gt0 _]; first by rewrite eqxx.
  exists (w ^+ e) => [|i]; first by rewrite prim_w ?e_gt0.
  by rewrite phi_ze exprn_mulr.
rewrite deg_phi {i}; set d := irr_degree i0.
apply/eqP; move/eqP: (sum_irr_degree sS F'S splitF).
rewrite (bigID (mem linS)) /= -/irr_degree.
rewrite (eq_bigr (fun _ => 1%N)) => [|i]; last by rewrite !inE; move/eqP->.
rewrite sum1_card nb_lin.
rewrite (eq_bigl (codom iphi)) // => [|i]; last by rewrite -in_setC -im_iphi.
rewrite (eq_bigr (fun _ => d ^ 2))%N => [|fi]; last first.
  by case/imageP=> i _ ->; rewrite deg_phi.
rewrite sum_nat_const card_image // card_ord oSpn (expnS p) -{3}[p]prednK //.
rewrite mulSn eqn_addl eqn_pmul2l; last by rewrite -ltnS prednK.
by rewrite -muln2 expn_mulr eqn_sqr.
Qed.

(* This is the corolloray of the above that is actually used in the proof of  *)
(* B & G, Theorem 2.5. It encapsulates the dependency on a socle of the       *)
(* regular representation.                                                    *)

Variables (m : nat) (rS : mx_representation F S m) (U : 'M[F]_m).
Hypotheses (simU :  mxsimple rS U) (ffulU : rstab rS U == 1%g).
Let sZS := center_sub S.
Let rZ := subg_repr rS sZS.

Lemma faithful_repr_extraspecial :
 \rank U = (p ^ n)%N /\
   (forall V, mxsimple rS V -> mx_iso rZ U V -> mx_iso rS U V).
Proof.
suffices IH: forall V, mxsimple rS V -> mx_iso rZ U V ->
  [&& \rank U == (p ^ n)%N & mxsimple_iso rS U V].
- split=> [|/= V simV isoUV].
    by case/andP: (IH U simU (mx_iso_refl _ _)); move/eqP.
  by case/andP: (IH V simV isoUV) => _; move/(mxsimple_isoP simU).
move=> V simV isoUV; wlog sS: / irrType F S by exact: socle_exists.
have [[_ defS'] prZ] := esS.
have{prZ} ntZ: 'Z(S) :!=: 1%g by case: eqP prZ => // ->; rewrite cards1.
have [_ [iphi]] := extraspecial_repr_structure sS.
set phi := fun i => _ => [] [inj_phi im_phi _ phiZ dim_phi] _.
have [modU nzU _]:= simU; pose rU := submod_repr modU.
have nlinU: \rank U != 1%N.
  apply/eqP; move/(rker_linear rU); apply/negP; rewrite /rker rstab_submod.
  by rewrite (eqmx_rstab _ (val_submod1 _)) (eqP ffulU) defS' subG1.
have irrU: mx_irreducible rU by exact/submod_mx_irr.
have rsimU := rsim_irr_comp sS F'S irrU.
set iU := irr_comp sS rU in rsimU; have [_ degU _ _]:= rsimU.
have phiUP: iU \in codom iphi by rewrite im_phi !inE -degU.
rewrite degU -(f_iinv phiUP) dim_phi eqxx /=; apply/(mxsimple_isoP simU).
have [modV _ _]:= simV; pose rV := submod_repr modV.
have irrV: mx_irreducible rV by exact/submod_mx_irr.
have rsimV := rsim_irr_comp sS F'S irrV.
set iV := irr_comp sS rV in rsimV; have [_ degV _ _]:= rsimV.
have phiVP: iV \in codom iphi by rewrite im_phi !inE -degV -(mxrank_iso isoUV).
pose jU := iinv phiUP; pose jV := iinv phiVP.
have [z Zz ntz]:= trivgPn _ ntZ.
have [|w prim_w phi_z] := phiZ z; first by rewrite 2!inE ntz.
suffices eqjUV: jU == jV.
  apply/(mx_rsim_iso modU modV); apply: mx_rsim_trans rsimU _.
  by rewrite -(f_iinv phiUP) -/jU (eqP eqjUV) f_iinv; exact: mx_rsim_sym.
have rsimUV: mx_rsim (subg_repr (phi jU) sZS) (subg_repr (phi jV) sZS).
  have [bU _ bUfree bUhom] := mx_rsim_sym rsimU.
  have [bV _ bVfree bVhom] := rsimV.
  have modUZ := mxmodule_subg sZS modU; have modVZ := mxmodule_subg sZS modV.
  case/(mx_rsim_iso modUZ modVZ): isoUV => [bZ degZ bZfree bZhom].
  rewrite /phi !f_iinv; exists (bU *m bZ *m bV)=> [||x Zx].
  - by rewrite -degU degZ degV.
  - by rewrite /row_free !mxrankMfree.
  have Sx := subsetP sZS x Zx.
  by rewrite 2!mulmxA bUhom // -(mulmxA _ _ bZ) bZhom // -4!mulmxA bVhom.
have{rsimUV} [B [B' _ homB]] := mx_rsim_def rsimUV.
have:= eqxx (irr_mode (iphi jU) z); rewrite /irr_mode; set i0 := Ordinal _.
rewrite {2}[_ z]homB // ![_ z]phi_z mxE mulr1n -scalemx1 -scalemxAr -scalemxAl.
rewrite -(repr_mx1 (subg_repr (phi jV) sZS)) -{B B'}homB // repr_mx1 scalemx1.
by rewrite mxE (eq_prim_root_expr prim_w) !modIp'.
Qed.

End Extraspecial.

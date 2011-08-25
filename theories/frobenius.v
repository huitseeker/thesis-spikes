(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype bigop prime.
Require Import finset fingroup morphism perm action quotient gproduct.
Require Import cyclic center pgroup abelian.

(******************************************************************************)
(*  Definition of Frobenius groups, some basic results, and the Frobenius     *)
(* theorem on the number of solutions of x ^+ n = 1.                          *)
(*    semiregular K H <->                                                     *)
(*       the internal action of H on K is semiregular, i.e., no nontrivial    *)
(*       elements of H and K commute; note that this is actually a symmetric  *)
(*       condition.                                                           *)
(*    semiprime K H <->                                                       *)
(*       the internal action of H on K is "prime", i.e., an element of K that *)
(*       centralises a nontrivial element of H must actually centralise all   *)
(*       of H.                                                                *)
(*    [Frobenius G = K ><| H] <=>                                             *)
(*       G is (isomorphic to) a Frobenius group with kernel K and complement  *)
(*       H. This is an effective predicate (in bool), which tests the         *)
(*       equality with the semidirect product, and then the fact that H is a  *)
(*       proper self-normalizing TI-subgroup of G.                            *)
(*    [Frobenius G with complement H] <=>                                     *)
(*       G is (isomorphic to) a Frobenius group with complement H; same as    *)
(*       above, but without the semi-direct product.                          *)
(*    Frobenius_action G H S to <->                                           *)
(*       The action to of G on S defines an isomorphism of G with a           *)
(*       (permutation) Frobenius group, i.e., to is faithful and transitive   *)
(*       on S, no nontrivial element of G fixes more than one point in S, and *)
(*       H is the stabilizer of some element of S, and non-trivial. Thus,     *)
(*        Frobenius_action G H S 'P                                           *)
(*       asserts that G is a Frobenius group in the classic sense.            *)
(*    has_Frobenius_action G H <->                                            *)
(*        Frobenius_action G H S to holds for some sT : finType, S : {set st} *)
(*        and to : {action gT &-> sT}. This is a predicate in Prop, but is    *)
(*        exactly reflected by [Frobenius G with complement H] : bool.        *)
(* Note that at this point we do not have the existence or nilpotence of      *)
(* Frobenius kernels. This is not a problem, because in all the applications  *)
(* we make of Frobenius groups, the kernel and complement are already known.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Definitions.

Variable gT : finGroupType.
Implicit Types G K H : {set gT}.

(* Corresponds to "H acts on K in a regular manner" in B & G. *)
Definition semiregular K H := {in H^#, forall x, 'C_K[x] = 1}.

(* Corresponds to "H acts on K in a prime manner" in B & G. *)
Definition semiprime K H := {in H^#, forall x, 'C_K[x] = 'C_K(H)}.

Definition Frobenius_group_with_complement G H :=
  [&& H \proper G, trivIset (H^# :^: G) & 'N_G(H) == H].

Definition Frobenius_group_with_kernel_and_complement G K H :=
  (K ><| H == G) && Frobenius_group_with_complement G H.

Section FrobeniusAction.

Variables G H : {set gT}.
Variables (sT : finType) (S : {set sT}) (to : {action gT &-> sT}).

Definition Frobenius_action :=
  [/\ [faithful G, on S | to],
      [transitive G, on S | to],
      {in G^#, forall x, #|'Fix_(S | to)[x]| <= 1},
      H != 1
    & exists2 u, u \in S & H = 'C_G[u | to]].

End FrobeniusAction.

CoInductive has_Frobenius_action G H : Prop :=
  HasFrobeniusAction sT S to of @Frobenius_action G H sT S to.

End Definitions.

Notation "[ 'Frobenius' G 'with' 'complement' H ]" :=
  (Frobenius_group_with_complement G H)
  (at level 0, G at level 50, H at level 35,
   format "[ 'Frobenius'  G  'with'  'complement'  H ]") : group_scope.

Notation "[ 'Frobenius' G = K ><| H ]" :=
  (Frobenius_group_with_kernel_and_complement G K H)
  (at level 0, G at level 50, K, H at level 35,
   format "[ 'Frobenius'  G  =  K  ><|  H ]") : group_scope.

Section FrobeniusBasics.

Variable gT : finGroupType.
Implicit Type G H K R X : {group gT}.

Lemma semiregular1l : forall H, semiregular 1 H.
Proof. by move=> H x _; rewrite setI1g. Qed.

Lemma semiregular1r : forall K, semiregular K 1.
Proof. by move=> K x; rewrite setDv inE. Qed.

Lemma semiregular_sym : forall H K, semiregular K H -> semiregular H K.
Proof.
move=> H K regH x; case/setD1P=> ntx Kx; apply: contraNeq ntx.
rewrite -subG1 -setD_eq0 setDE setIAC -setDE (sameP eqP set1gP).
by case/set0Pn=> y; case/setIP=> Hy cxy; rewrite -(regH y Hy) inE Kx cent1C.
Qed.

Lemma semiregular_prime : forall H K, semiregular K H -> semiprime K H.
Proof.
move=> H K regH x Hx; apply/eqP; rewrite eqEsubset {1}regH // sub1G.
by rewrite -cent_set1 setIS ?centS // sub1set; case/setD1P: Hx.
Qed.

Lemma semiprime_regular : forall H K,
  semiprime K H -> 'C_K(H) = 1 -> semiregular K H.
Proof. by move=> H K prKH tiKcH x Hx; rewrite prKH. Qed.

Lemma cent_semiprime : forall H K X,
   semiprime K H -> X \subset H -> X :!=: 1 -> 'C_K(X) = 'C_K(H).
Proof.
move=> H K X prKH sXH; case/trivgPn=> x Xx ntx; apply/eqP.
rewrite eqEsubset -{1}(prKH x) ?inE ?(subsetP sXH) ?ntx //=.
by rewrite -cent_cycle !setIS ?centS ?cycle_subG.
Qed.

Lemma stab_semiprime : forall H K X,
   semiprime K H -> X \subset K -> 'C_H(X) != 1 -> 'C_H(X) = H.
Proof.
move=> H K X prKH sXK ntCHX; apply/setIidPl; rewrite centsC -subsetIidl.
rewrite -{2}(setIidPl sXK) -setIA -(cent_semiprime prKH _ ntCHX) ?subsetIl //.
by rewrite !subsetI subxx sXK centsC subsetIr.
Qed.

Lemma cent_semiregular : forall H K X,
   semiregular K H -> X \subset H -> X :!=: 1 -> 'C_K(X) = 1.
Proof.
move=> H K X regKH sXH; case/trivgPn=> x Xx ntx; apply/trivgP.
rewrite -(regKH x) ?inE ?(subsetP sXH) ?ntx ?setIS //=.
by rewrite -cent_cycle centS ?cycle_subG.
Qed.

Lemma regular_norm_dvd_pred : forall K H,
  H \subset 'N(K) -> semiregular K H -> #|H| %| #|K|.-1.
Proof.
move=> K H nKH regH.
have actsH: [acts H, on K^# | 'J] by rewrite astabsJ normD1.
rewrite (cardsD1 1 K) group1 -(acts_sum_card_orbit actsH) /=.
rewrite (eq_bigr (fun _ => #|H|)) ?sum_nat_const ?dvdn_mull // => xH.
case/imsetP=> x; case/setIdP=> ntx Kx ->; rewrite card_orbit astab1J.
rewrite ['C_H[x]](trivgP _) ?indexg1 //=.
apply/subsetP=> y; case/setIP=> Hy cxy; apply: contraR ntx => nty.
by rewrite -[[set 1]](regH y) inE ?nty // Kx cent1C.

Qed.

Lemma regular_norm_coprime : forall K H,
  H \subset 'N(K) -> semiregular K H -> coprime #|K| #|H|.
Proof.
move=> K H nKH regH.
by rewrite (coprime_dvdr (regular_norm_dvd_pred nKH regH)) ?coprimenP.
Qed.

Lemma TIconjP : forall G H,
  reflect {in G &, forall x y, x * y^-1 \in 'N_G(H) \/ H :^ x :&: H :^ y = 1}
          (trivIset (H^# :^: G)).
Proof.
move=> G H; have defH := setD1K (group1 H).
apply: (iffP trivIsetP) => [tiHG x y Gx Gy | tiHG Hx Hy].
  have [||defHx|tiHxy] := tiHG (H^# :^ x) (H^# :^ y); rewrite ?mem_imset //.
    left; rewrite !inE groupM ?groupV //=.
    by rewrite -defH conjUg conjs1g conjsgM defHx actK.
  by right; apply/trivgP; rewrite -setD_eq0 setDIl -!conjD1g disjoint_setI0.
case/imsetP=> x Gx ->{Hx}; case/imsetP=> y Gy ->{Hy}.
rewrite -setI_eq0 !conjD1g -setDIl setD_eq0.
have [nHxy|->] := tiHG x y Gx Gy; [left | by right].
by case/setIP: nHxy => _ nHxy; rewrite -{2}(normP nHxy) actM actKV.
Qed.
Implicit Arguments TIconjP [G H].

Lemma TIconj_SN_P : forall G H,
    H :!=: 1 -> H \subset G ->
  reflect {in G :\: H, forall x, H :&: H :^ x = 1}
          (trivIset (H^# :^: G) && ('N_G(H) == H)).
Proof.
move=> G H ntH sHG; apply: (iffP idP) => [|sntiHG].
  case/andP; move/TIconjP=> tiHG; move/eqP=> snHG x; case/setDP=> Gx notHx.
  have [//||] := tiHG 1 x _ Gx; rewrite ?conjsg1 //.
  by rewrite  mul1g snHG groupV (negPf notHx).
apply/andP; split.
  apply/TIconjP=> x y Gx Gy.
  have Gxy: x * y^-1 \in G by rewrite groupM ?groupV.
  case Hxy: (x * y^-1 \in H); [left | right].
    by rewrite inE Gxy (subsetP (normG H)).
  by rewrite -(mulgKV y x) actM -conjIg setIC sntiHG ?conjs1g ?inE ?Hxy.
rewrite eqEsubset subsetI sHG normG !andbT -setD_eq0 setDE setIAC -setDE.
apply: contraR ntH; case/set0Pn=> x; case/setIP=> Gx nHx.
by rewrite -(sntiHG x Gx) (normP nHx) setIid.
Qed.

Lemma Frobenius_actionP : forall G H,
  reflect (has_Frobenius_action G H) [Frobenius G with complement H].
Proof.
move=> G H; apply: (iffP andP) => [[] | [sT S to [ffulG transG regG ntH]]].
  rewrite properEneq; case/andP=> neqHG sHG; case/andP=> tiHG; move/eqP=> snHG.
  suffices: Frobenius_action G H (rcosets H G) 'Rs by exact: HasFrobeniusAction.
  pose Hfix x := 'Fix_(rcosets H G | 'Rs)[x].
  have regG: {in G^#, forall x, #|Hfix x| <= 1}.
  - move=> x; case/setD1P=> nt_x Gx.
    have [->|[Hy]] := set_0Vmem (Hfix x); first by rewrite cards0.
    rewrite -(card1 Hy); case/setIP; case/imsetP=> y Gy ->{Hy} cHyx.
    apply: subset_leq_card; apply/subsetP=> Hz.
    case/setIP; case/imsetP=> z Gz ->{Hz} cHzx.
    rewrite -!sub_astab1 !astab1_act !sub1set astab1Rs in cHyx cHzx *.
    rewrite !inE (canF_eq (actK _ _)) -actM /= rcosetE rcoset_id // -snHG.
    have [//| tiHyz] := TIconjP tiHG y z Gy Gz.
    by case/negP: nt_x; rewrite -in_set1 -[[set 1]]tiHyz inE cHyx.
  have ntH: H :!=: 1.
    by apply: contra neqHG; move/eqP=> H1; rewrite -snHG H1 norm1 setIT.
  split=> //; first 1 last; first exact: transRs_rcosets.
    by exists (H : {set gT}); rewrite ?orbit_refl // astab1Rs (setIidPr sHG).
  apply/subsetP=> y; case/setIP=> Gy cHy; apply: contraR neqHG => nt_y.
  rewrite (index1g sHG) //; apply/eqP; rewrite eqn_leq indexg_gt0 andbT.
  apply: leq_trans (regG y _); last by rewrite setDE 2!inE Gy nt_y /=.
  by rewrite /Hfix (setIidPl _) -1?astabC ?sub1set.
case=> u Su defH; have sHG: H \subset G by rewrite defH subsetIl.
rewrite properEneq sHG andbT; split.
  apply: contra ntH; move/eqP=> /= defG.
  suffices defS: S = [set u] by rewrite -(trivgP ffulG) /= defS defH.
  apply/eqP; rewrite eq_sym eqEcard sub1set Su.
  by rewrite -(atransP transG u Su) card_orbit -defH defG indexgg cards1.
apply/(TIconj_SN_P ntH sHG)=> x; case/setDP=> Gx notHx.
apply/trivgP; apply/subsetP=> y; rewrite /= -sub1set defH conjIg -astab1_act.
rewrite !(sub_astab1, subsetI) sub1set -andbA; case/and4P=> Gy cuy _ cuxy.
move/implyP: (regG y); rewrite in_setD Gy; apply: contraLR => -> /=.
rewrite (cardD1 u) (cardD1 (to u x)) inE Su cuy inE /= inE cuxy.
rewrite (actsP (atrans_acts transG)) // Su; case: eqP => //.
by move/astab1P=> cux; case/negP: notHx; rewrite defH inE Gx.
Qed.

Lemma Frobenius_context : forall G H K,
    [Frobenius G = K ><| H] ->
  [/\ K ><| H = G, K :!=: 1, H :!=: 1, K \proper G & H \proper G].
Proof.
move=> G H K; case/andP; move/eqP=> defG frobG; have [ltHG _] := andP frobG.
have [_ _ _ [_ _ _ ntH _]] := Frobenius_actionP _ _ frobG.
split=> //.
  by apply: contra (proper_subn ltHG); move/eqP=> K1; rewrite -defG K1 sdprod1g.
have [_ <- _ tiHK] := sdprodP defG.
by rewrite properEcard mulG_subl TI_cardMg // ltn_Pmulr ?cardG_gt1.
Qed.

Lemma Frobenius_partition : forall G H K,
  [Frobenius G = K ><| H] -> partition (gval K |: (H^# :^: K)) G.
Proof.
move=> G H K frobG; have [defG _ ntH ltKG ltHG] := Frobenius_context frobG.
have{defG} [_ defG nKH tiKH] := sdprodP defG.
have [sKG sHG] := (proper_sub ltKG, proper_sub ltHG).
have [_ _ tiHG] := and4P frobG; move/eqP=> snHG.
set HG := H^# :^: K; set KHG := _ |: _.
have defHG: HG = H^# :^: G.
  apply: atransP (orbit_refl _ _ _).
  apply/(subgroup_transitiveP (orbit_refl _ _ _) sKG (atrans_orbit _ _ _)).
  by rewrite astab1Js normD1 snHG (normC nKH).
have tiKHG: forall Hx, Hx \in HG -> [disjoint K & Hx].
  move=> Hx; case/imsetP=> x Kx ->{Hx}; rewrite -setI_eq0.
  by rewrite conjD1g -(conjGid Kx) setDE setIA -conjIg tiKH conjs1g setICr.
have{tiKHG} tiKHG: trivIset KHG.
  apply/trivIsetP=> U V.
  case/setU1P=> [-> | HG_U]; case/setU1P=> [-> | HG_V]; auto.
    by right; rewrite disjoint_sym tiKHG.
  by apply: (trivIsetP tiHG); rewrite -defHG.
apply/and3P; split=> //; last first.
  rewrite !inE eqEcard cards0 leqNgt cardG_gt0 andbF /=.
  apply/imsetP=> [[x _]]; move/eqP; apply/negP.
  by rewrite eq_sym conjD1g setD_eq0 sub_conjg conjs1g subG1.
rewrite eqEcard; apply/andP; split.
  apply/bigcupsP=> U; case/setU1P=> [-> // |].
  case/imsetP=> x Kx ->{U}; rewrite conj_subG ?(subsetP sKG) //.
  by rewrite subDset subsetU ?sHG ?orbT.
rewrite -(eqnP tiKHG) big_setU1 /=; last first.
  apply/imsetP=> [[x _]]; move/setP; move/(_ 1).
  by rewrite conjD1g group1 !inE eqxx.
rewrite (eq_bigr (fun _ => #|H|.-1)) => [|Hx]; last first.
  by case/imsetP=> x _ ->; rewrite cardJg (cardsD1 1 H) group1.
rewrite sum_nat_const card_conjugates normD1.
rewrite -{3}(setIidPl sKG) -setIA snHG tiKH indexg1 -mulnS prednK //.
by rewrite -TI_cardMg ?defG.
Qed.

Lemma Frobenius_action_kernel_def : forall G H K sT S to,
    K ><| H = G -> @Frobenius_action _ G H sT S to ->
  K :=: 1 :|: [set x \in G | 'Fix_(S | to)[x] == set0].
Proof.
move=> G H K sT S to defG FrobG.
have partG: partition (gval K |: (H^# :^: K)) G.
  apply: Frobenius_partition; apply/andP; rewrite defG; split=> //.
  by apply/Frobenius_actionP; exact: HasFrobeniusAction FrobG.
have{FrobG} [ffulG transG regG ntH [u Su defH]]:= FrobG.
apply/setP=> x; rewrite !inE.
have [-> | ntx]:= eqVneq x 1; first by rewrite group1 eqxx.
have [coverG _]:= andP partG.
have neKHy: forall y, gval K <> H^# :^ y.
  by move=> y; move/setP; move/(_ 1); rewrite group1 conjD1g setD11.
rewrite (negPf ntx) -(eqP coverG) /cover.
rewrite big_setU1 /= ?inE; last by apply/imsetP=> [[y _]]; exact: neKHy.
have [nsKG sHG _ _ tiKH] := sdprod_context defG; have [sKG nKG]:= andP nsKG.
symmetry; case Kx: (x \in K) => /=.
  apply/set0Pn=> [[v]]; case/setIP=> Sv.
  have [y Gy ->] := atransP2 transG Su Sv.
  rewrite -sub1set -astabC sub1set astab1_act mem_conjg => Hxy.
  case/negP: ntx; rewrite -in_set1 -(conjgKV y x) -mem_conjgV conjs1g -tiKH.
  by rewrite defH setIA inE -mem_conjg (setIidPl sKG) (normsP nKG) ?Kx.
apply/andP; case; case/bigcupP=> Hy; case/imsetP=> y Ky ->{Hy} Hyx.
case/set0Pn; exists (to u y).
rewrite inE (actsP (atrans_acts transG)) ?(subsetP sKG) // Su.
rewrite -sub1set -astabC sub1set astab1_act.
by rewrite conjD1g defH conjIg !inE in Hyx; case/and3P: Hyx.
Qed.

Lemma Frobenius_cent1_ker : forall G H K,
  [Frobenius G = K ><| H] -> {in K^#, forall x, 'C_G[x] \subset K}.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Kx.
rewrite -setD_eq0 setDE -setIA setI_eq0 disjoint_sym.
have [partG _ _] := and3P (Frobenius_partition frobG).
rewrite -(eqP partG) bigcup_disjoint // => U; case/setU1P=> [-> |].
  by rewrite -setI_eq0 setIAC -setIA setICr setI0.
case/imsetP=> y Ky ->{U}; rewrite -setI_eq0 setIAC -subset0 subIset //.
apply/orP; left; rewrite conjD1g setDE setIA -setDE subDset setU0.
rewrite -[x](conjgKV y) -conjg_set1 normJ -conjIg sub_conjg conjs1g.
apply/subsetP=> z; case/setIP=> cxz Hz; have [_ _ sntiHG]:= and3P frobG.
have{frobG} [defG _ ntH] := Frobenius_context frobG.
case/andP=> sKG _; case/andP=> sHG _; have [_ _ _ tiKH] := sdprodP defG.
rewrite -(TIconj_SN_P ntH sHG sntiHG (x ^ y^-1)).
  by rewrite inE Hz mem_conjg conjgE invgK mulgA -(cent1P cxz) mulgK.
have Kxy: x ^ y^-1 \in K by rewrite groupJ ?groupV.
rewrite inE (subsetP sKG) // andbT; apply: contra nt_x => Hxy.
by rewrite -in_set1 -(memJ_conjg _ y^-1) conjs1g -tiKH inE Kxy.
Qed.

Lemma Frobenius_reg_ker : forall G H K,
  [Frobenius G = K ><| H] -> semiregular K H.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Hx; apply/trivgP.
apply/subsetP=> y; case/setIP=> Ky cxy; apply: contraR nt_x => nty.
have K1y: y \in K^# by rewrite inE nty.
have [sHG tiKH]: H \subset G /\ K :&: H = 1.
  by case/Frobenius_context: frobG; case/sdprod_context.
suffices: x \in K :&: H by rewrite tiKH inE.
rewrite inE (subsetP (Frobenius_cent1_ker frobG K1y)) //.
by rewrite inE cent1C (subsetP sHG).
Qed.

Lemma Frobenius_reg_compl : forall K H G,
  [Frobenius G = K ><| H] -> semiregular H K.
Proof.
by move=> K H G frobG; apply: semiregular_sym; exact: Frobenius_reg_ker frobG.
Qed.

Lemma Frobenius_dvd_ker1 : forall G H K,
  [Frobenius G = K ><| H] -> #|H| %| #|K|.-1.
Proof.
move=> G H K frobG; apply: regular_norm_dvd_pred (Frobenius_reg_ker frobG).
by case/Frobenius_context: frobG; case/sdprodP.
Qed.

Lemma Frobenius_coprime : forall G H K,
  [Frobenius G = K ><| H] -> coprime #|K| #|H|.
Proof.
move=> G H K frobG.
by rewrite (coprime_dvdr (Frobenius_dvd_ker1 frobG)) ?coprimenP.
Qed.

Lemma Frobenius_ker_Hall : forall G H K,
  [Frobenius G = K ><| H] -> Hall G K.
Proof.
move=> G H K frobG; have [defG _ _ ltKG _] := Frobenius_context frobG.
rewrite /Hall -divgS (proper_sub ltKG) //= -(sdprod_card defG) mulKn //.
exact: Frobenius_coprime frobG.
Qed.

Lemma Frobenius_compl_Hall : forall G H K,
  [Frobenius G = K ><| H] -> Hall G H.
Proof.
move=> G H K frobG; have [defG _ _ _ ltHG] := Frobenius_context frobG.
rewrite /Hall -divgS (proper_sub ltHG) //= -(sdprod_card defG) mulnK //.
by rewrite coprime_sym; exact: Frobenius_coprime frobG.
Qed.

(*
Theorem Frobenius_kernel_exists : forall G H,
  [Frobenius G with complement H] -> group_set (G :\: cover (H^# :^: G)).
Admitted.
*)

End FrobeniusBasics.

Theorem Frobenius_Ldiv : forall (gT : finGroupType) (G : {group gT}) n,
  n %| #|G| -> n %| #|'Ldiv_n(G)|.
Proof.
move=> gT G n nG; move: {2}_.+1 (ltnSn (#|G| %/ n)) => mq.
elim: mq => // mq IHm in gT G n nG *; case/dvdnP: nG => q oG.
have [q_gt0 n_gt0] : 0 < q /\ 0 < n by apply/andP; rewrite -muln_gt0 -oG.
rewrite ltnS oG mulnK // => leqm.
have:= q_gt0; rewrite leq_eqVlt; case/predU1P=> [q1 | lt1q].
  rewrite -(mul1n n) q1 -oG (setIidPl _) //.
  by apply/subsetP=> x Gx; rewrite inE -order_dvdn order_dvdG.
pose p := pdiv q; have pr_p: prime p by exact: pdiv_prime.
have lt1p: 1 < p := prime_gt1 pr_p; have p_gt0 := ltnW lt1p.
have{leqm} lt_qp_mq: q %/ p < mq by apply: leq_trans leqm; rewrite ltn_Pdiv.
have: n %| #|'Ldiv_(p * n)(G)|.
  have: p * n %| #|G| by rewrite oG dvdn_pmul2r ?pdiv_dvd.
  move/IHm=> IH; apply: dvdn_trans (IH _); first exact: dvdn_mull.
  by rewrite oG divn_pmul2r.
rewrite -(cardsID 'Ldiv_n()) dvdn_addl.
  rewrite -setIA ['Ldiv_n(_)](setIidPr _) //.
  apply/subsetP=> x; rewrite !inE -!order_dvdn; exact: dvdn_mull.
rewrite setDE -setIA -setDE; set A := _ :\: _.
have pA: forall x, x \in A -> #[x]`_p = (n`_p * p)%N.
  move=> x; rewrite !inE -!order_dvdn; case/andP=> xn xnp.
  rewrite !p_part // -expnSr; congr (p ^ _)%N; apply/eqP.
  rewrite eqn_leq -{1}addn1 -(pfactorK 1 pr_p) -logn_mul ?expn1 // mulnC.
  rewrite dvdn_leq_log ?muln_gt0 ?p_gt0 //= ltnNge; apply: contra xn => xn.
  move: xnp; rewrite -[#[x]](partnC p) //.
  rewrite !gauss_inv ?coprime_partC //; case/andP=> _.
  rewrite p_part ?pfactor_dvdn // xn gauss // coprime_sym.
  exact: pnat_coprime (pnat_id _) (part_pnat _ _).
rewrite -(partnC p n_gt0) gauss_inv ?coprime_partC //; apply/andP; split.
  rewrite -sum1_card (partition_big_imset (@cycle _)) /=.
  apply: dvdn_sum => X; case/imsetP=> x; case/setIP=> Gx Ax ->{X}.
  rewrite (eq_bigl (generator <[x]>)) => [|y].
    rewrite sum1dep_card -phi_gen -[#[x]](partnC p) //.
    rewrite phi_coprime ?coprime_partC // dvdn_mulr // .
    by rewrite (pA x Ax) p_part // -expnSr phi_pfactor // dvdn_mull.
  rewrite /generator eq_sym andbC; case xy: {+}(_ == _) => //.
  rewrite !inE -!order_dvdn in Ax *.
  by rewrite -cycle_subG /order -(eqP xy) cycle_subG Gx.
rewrite -sum1_card (partition_big_imset (fun x => x.`_p ^: G)) /=.
apply: dvdn_sum => X; case/imsetP=> x; case/setIP=> Gx Ax ->{X}.
set y := x.`_p; have oy: #[y] = (n`_p * p)%N by rewrite order_constt pA.
rewrite (partition_big (fun x => x.`_p) (mem (y ^: G))) /= => [|z]; last first.
  by case/andP=> _; move/eqP <-; rewrite /= class_refl.
pose G' := ('C_G[y] / <[y]>)%G; pose n' := gcdn #|G'| n`_p^'.
have n'_gt0: 0 < n' by rewrite gcdn_gt0 cardG_gt0.
rewrite (eq_bigr (fun _ => #|'Ldiv_n'(G')|)) => [|ya].
  rewrite sum_nat_const -index_cent1 indexgI.
  rewrite -(dvdn_pmul2l (cardG_gt0 'C_G[y])) mulnA LaGrangeI.
  have oCy: #|'C_G[y]| = (#[y] * #|G'|)%N.
    rewrite card_quotient ?subcent1_cycle_norm // LaGrange //.
    by rewrite subcent1_cycle_sub ?groupX.
  rewrite oCy -mulnA -(muln_lcm_gcd #|G'|) -/n' mulnA dvdn_mul //.
    rewrite muln_lcmr -oCy order_constt pA // mulnAC partnC // dvdn_lcm.
    by rewrite cardSg ?subsetIl // mulnC oG dvdn_pmul2r ?pdiv_dvd.
  apply: IHm; [exact: dvdn_gcdl | apply: leq_ltn_trans lt_qp_mq].
  rewrite -(@divn_pmul2r n`_p^') // -muln_lcm_gcd mulnC divn_pmul2l //.
  rewrite leq_divr // divn_mulAC ?leq_divl ?dvdn_mulr ?dvdn_lcmr //.
  rewrite dvdn_leq ?muln_gt0 ?q_gt0 //= mulnC muln_lcmr dvdn_lcm.
  rewrite -(@dvdn_pmul2l n`_p) // mulnA -oy -oCy mulnCA partnC // -oG.
  by rewrite cardSg ?subsetIl // dvdn_mul ?pdiv_dvd.
case/imsetP=> a Ga ->{ya}.
pose h := [fun z => coset <[y]> (z ^ a^-1)].
pose h' := [fun Z : coset_of <[y]> => (y * (repr Z).`_p^') ^ a].
rewrite -sum1_card (reindex_onto h h') /= => [|Z]; last first.
  rewrite conjgK coset_kerl ?cycle_id ?morph_constt ?repr_coset_norm //.
  rewrite /= coset_reprK 2!inE -order_dvdn dvdn_gcd; case/and3P=> _ _ p'Z.
  apply: constt_p_elt (pnat_dvd p'Z _); exact: part_pnat.
apply: eq_bigl => z; apply/andP/andP=> [[]|[]].
  rewrite inE -andbA; case/and3P=> Gz Az _; move/eqP=> zp_ya.
  have czy: z ^ a^-1 \in 'C[y].
    rewrite -mem_conjg -normJ conjg_set1 -zp_ya.
    by apply/cent1P; exact: commuteX.
  have Nz:  z ^ a^-1 \in 'N(<[y]>) by apply: subsetP czy; exact: norm_gen.
  have G'z: h z \in G' by rewrite mem_morphim //= inE groupJ // groupV.
  rewrite inE G'z inE -order_dvdn dvdn_gcd order_dvdG //=.
  rewrite /order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
  rewrite -(@dvdn_pmul2l #[y]) // LaGrange; last first.
    by rewrite /= cycleJ cycle_subG mem_conjgV -zp_ya mem_cycle.
  rewrite oy mulnAC partnC // [#|_|]orderJ; split.
    by rewrite !inE -!order_dvdn mulnC in Az; case/andP: Az.
  set Z := coset _ _; have NZ := repr_coset_norm Z; have:= coset_reprK Z.
  case/kercoset_rcoset=> {NZ}// yi; case/cycleP=> i -> -> {yi Z}.
  rewrite consttM; last by apply commute_sym; apply: commuteX; apply/cent1P.
  rewrite (constt1P _) ?p_eltNK 1?p_eltX ?p_elt_constt // mul1g.
  by rewrite conjMg consttJ conjgKV -zp_ya consttC.
rewrite 2!inE -order_dvdn; set Z := coset _ _.
case/andP=> Cz n'Z; move/eqP=> def_z.
have Nz: z ^ a^-1 \in 'N(<[y]>).
  rewrite -def_z conjgK groupMr; first by rewrite -(cycle_subG y) normG.
  by rewrite groupX ?repr_coset_norm.
have{Cz}: z ^ a^-1 \in 'C_G[y]; last case/setIP=> Gz Cz.
  case/morphimP: Cz => u Nu Cu.
  case/kercoset_rcoset=> // yi; case/cycleP=> i ->{yi} ->.
  by rewrite groupMr // groupX // inE groupX //; exact/cent1P.
have{def_z} zp_ya: z.`_p = y ^ a.
  rewrite -def_z consttJ consttM.
    rewrite constt_p_elt ?p_elt_constt //.
    by rewrite (constt1P _) ?p_eltNK ?p_elt_constt ?mulg1.
  apply: commute_sym; apply/cent1P.
  rewrite -def_z conjgK groupMl // in Cz; exact/cent1P.
have ozp: #[z ^ a^-1]`_p = #[y].
  by rewrite -order_constt consttJ zp_ya conjgK.
split; rewrite zp_ya // -class_lcoset lcoset_id // eqxx andbT.
rewrite -(conjgKV a z) !inE groupJ //= -!order_dvdn orderJ; apply/andP; split.
  apply/negP; move/(partn_dvd p n_gt0); apply/negP.
  by rewrite ozp -(muln1 n`_p) oy dvdn_pmul2l // dvdn1 neq_ltn lt1p orbT.
rewrite -(partnC p n_gt0) mulnCA mulnA -oy -(@partnC p #[_]) // ozp.
apply dvdn_mul => //; apply: dvdn_trans (dvdn_trans n'Z (dvdn_gcdr _ _)).
rewrite {2}/order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
rewrite -(@dvdn_pmul2l #|<[z ^ a^-1]> :&: <[y]>|) ?cardG_gt0 // LaGrangeI.
rewrite -[#|<[_]>|](partnC p) ?order_gt0 // dvdn_pmul2r // ozp.
by rewrite cardSg ?subsetIr.
Qed.

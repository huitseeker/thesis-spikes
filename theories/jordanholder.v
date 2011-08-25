(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice fintype.
Require Import bigop finset fingroup morphism automorphism quotient action.
Require Import gseries.

(******************************************************************************)
(* This files establishes Jordan-Hölder theorems for finite groups. These     *)
(* theorems state the uniqueness up to permutation and isomorphism for the    *)
(* series of quotient built from the successive elements of any composition   *)
(* series of the same group. These quotients are also called factors of the   *)
(* composition series. To avoid the heavy use of highly polymorphic lists     *)
(* describing these quotient series, we introduce sections.                   *)
(* This library defines:                                                      *)
(*         (G1 / G2)%sec == alias for the pair (G1, G2) of groups in the same *)
(*                          finGroupType, coerced to the actual quotient group*)
(*                          G1 / G2. We call this pseudo-quotient a section of*)
(*                          G1 and G2.                                        *)
(*    section_isog s1 s2 == s1 and s2 respectively coerce to isomorphic       *)
(*                          quotient groups.                                  *)
(*        section_repr s == canonical representative of the isomorphism class *)
(*                          of the section s.                                 *)
(*         mksrepr G1 G2 == canonical representative of the isomorphism class *)
(*                          of (G1 / G2)%sec.                                 *)
(*         mkfactors G s == if s is [:: s1, s2, ..., sn], constructs the list *)
(*                      [:: mksrepr G s1, mksrepr s1 s2, ..., mksrepr sn-1 sn]*)
(*             comps G s == s is a composition series for G i.e. s is a       *)
(*                          decreasing sequence of subgroups of G             *)
(*                          in which two adjacent elements are maxnormal one  *)
(*                          in the other and the last element of s is 1.      *)
(* Given aT and rT two finGroupTypes, (D : {group rT}), (A : {group aT}) and  *)
(* (to : groupAction A D) an external action.                                 *)
(*        maxainv to B C == C is a maximal proper normal subgroup of B        *)
(*                          invariant by (the external action of A via) to.   *)
(*          asimple to B == the maximal proper normal subgroup of B invariant *)
(*                          by the external action to is trivial.             *)
(*         acomps to G s == s is a composition series for G invariant by to,  *)
(*                          i.e. s is a decreasing sequence of subgroups of G *)
(*                          in which two adjacent elements are maximally      *)
(*                          invariant by to one in the other and the          *)
(*                          last element of s is 1.                           *)
(* We prove two versions of the result:                                       *)
(*    - JordanHolderUniqueness establishes the uniqueness up to permutation   *)
(*       and isomorphism of the lists of factors in composition series of a   *)
(*       given group.                                                         *)
(*    - StrongJordanHolderUniqueness extends the result to composition series *)
(*       invariant by an external group action.                               *)
(******************************************************************************)

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive section (gT : finGroupType) : Type := Sec of {group gT} * {group gT}.

Delimit Scope section_scope with sec.
Bind Scope section_scope with section.

Definition mkSec (gT : finGroupType)(G1 G2 : {group gT}) := Sec (G1, G2).

Infix "/" := mkSec : section_scope.

Coercion pair_of_section gT (s : section gT) := let: Sec u := s in u.

Coercion quotient_of_section gT (s : section gT) : GroupSet.sort _ := 
  s.1 / s.2.

Coercion section_group gT (s : section gT) : {group (coset_of s.2)} :=
  Eval hnf in [group of s].

Section Sections.

Variables (gT : finGroupType).

Implicit Types G : {group gT}.
Implicit Types s : section gT.

Canonical Structure section_subType :=
  Eval hnf in [newType for (@pair_of_section _) by (@section_rect gT)].
Definition section_eqMixin := Eval hnf in [eqMixin of (section _) by <:].
Canonical Structure section_eqType :=
  Eval hnf in EqType (section _) section_eqMixin.
Definition section_choiceMixin := [choiceMixin of (section _) by <:].
Canonical Structure section_choiceType :=
  Eval hnf in ChoiceType (section _) section_choiceMixin.
Definition section_countMixin := [countMixin of (section _) by <:].
Canonical Structure section_countType :=
   Eval hnf in CountType (section _) section_countMixin.
Canonical Structure section_subCountType :=
  Eval hnf in [subCountType of (section _)].
Definition section_finMixin := [finMixin of (section _) by <:].
Canonical Structure section_finType :=
  Eval hnf in FinType (section _) section_finMixin.
Canonical Structure section_subFinType := 
  Eval hnf in [subFinType of (section _)].
Canonical Structure section_group.

(* Isomorphic sections *)

Definition section_isog := [rel x y : section gT | x \isog y].

(* A witness of the isomorphism class of a section *)
Definition section_repr s :=
  if (pick (section_isog ^~ s)) is Some s then s else (mkSec 1 1)%sec.

Definition mksrepr G1 G2 := section_repr (mkSec G1 G2).

Lemma section_reprP : forall s, (section_repr s) \isog s.
Proof.
move=> H; rewrite /section_repr; case: pickP => //; move/(_ H).
by rewrite /= isog_refl.
Qed.

Lemma section_repr_isog : forall s1 s2,
  s1 \isog s2 -> section_repr s1 = section_repr s2.
Proof.
move=> s1 s2 is12; rewrite /section_repr.
suff siso12 : (section_isog ^~ s1) =1 (section_isog ^~ s2) .
  by rewrite (eq_pick siso12).
by move=> x /=; apply:isog_transr.
Qed.


Definition mkfactors (G : {group gT}) (s : seq {group gT}) :=
  map section_repr (pairmap (@mkSec _) G s).

End Sections.



Section CompositionSeries.

Variables (gT : finGroupType).
Local Notation gTg := {group gT}.

Implicit Type G : gTg.
Implicit Type s : seq gTg.


Local Notation compo := [rel x y : {set gT} | maxnormal y x x].

Definition comps G s := ((last G s) == 1%G) && compo.-series G s.

Lemma compsP : forall G s, reflect
  (last G s = 1%G /\  path [rel x y : gTg | maxnormal y x x] G s) (comps G s).
Proof. by move=> G s; apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_comps : forall G s, comps G s -> (G :==: 1) = (s == [::]).
Proof.
move=> G s; case/andP=> ls cs; apply/eqP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxgroupP.
by rewrite G1 /proper sub1set group1 andbF.
Qed.

Lemma comps_cons : forall G H s, comps G (H :: s) -> comps H s.
Proof.
by move=> G H s; case/andP => /= ls; case/andP=> _ p; rewrite /comps ls.
Qed.

Lemma simple_compsP : forall G s, comps G s ->
  reflect (s = [:: (1%G : gTg) ]) (simple G).
Proof.
move=> G s cs; apply: (iffP idP); last first.
  move=> se; move: cs; rewrite se /=; case/andP=> /=.
  by rewrite andbT simple_maxnormal.
case: s cs.
  by rewrite /comps /= andbT; move/eqP->; case/simpleP; rewrite eqxx.
move=> H s cs sG; apply/eqP; rewrite eqseq_cons -(trivg_comps (comps_cons cs)).
suff H1: H :=: 1 by rewrite H1 eqxx andbT; apply/eqP; apply: val_inj=> /=.
case/compsP: cs=> /= ls; case/andP=> mH ps; move: sG; rewrite simple_maxnormal.
case/maxgroupP=> _; apply; rewrite ?sub1set //.
by rewrite (maxnormal_proper mH) normal_norm // maxnormal_normal.
Qed.

Lemma exists_comps : forall G : gTg, exists s, comps G s.
Proof.
move=> G; elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
case/orP: (orbN (simple G)) => [sG | nsG].
  exists [:: (1%G : gTg) ].
  by rewrite /comps eqxx /=  -simple_maxnormal andbT.
case/orP: (orbN (G :==: 1))=> [tG | ntG].
  by exists (Nil gTg); rewrite /comps /= andbT.
case: (ex_maxnormal_ntrivg ntG)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // (maxnormal_proper pmN).
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /comps.
by rewrite last_cons lasts /=  pmN.
Qed.


(******************************************************************************)
(* The factors associated to two composition series of the same group are     *)
(* the same up to isomorphism and permutation                                 *)
(******************************************************************************)

Lemma JordanHolderUniqueness : forall (G : gTg) (s1 s2 : seq gTg),
  comps G s1 -> comps G s2 -> perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
move=> G; elim: {G} #|G| {-2}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
move=> s1 s2 cs1 cs2; case/orP: (orbN (G :==: 1)) => [tG | ntG].
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_comps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_comps cs2).
  by rewrite /= perm_eq_refl.
case/orP: (orbN (simple G))=> [sG | nsG].
  have -> : s1 = [:: 1%G ] by apply/(simple_compsP cs1).
  have -> : s2 = [:: 1%G ] by apply/(simple_compsP cs2).
  by rewrite /= perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_1).
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /comps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: maxnormal_normal.
have nN2G : N2 <| G by apply: maxnormal_normal.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_comps N)=> sN; case/andP=> lsN csN.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso2) quotient_simple.
  by rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)).
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso1) quotient_simple.
  by rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)).
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
apply: perm_eq_trans i2; exact: perm_eq_refl.
Qed.

End CompositionSeries.

(******************************************************************************)
(* Helper lemmas for group actions.                                           *) 
(******************************************************************************)

Section MoreGroupAction.

Variables (aT rT : finGroupType).
Variables (A : {group aT})(D : {group rT}).
Variable to : groupAction A D.


Lemma gactsP : forall G : {set rT}, 
  reflect {acts A, on G | to} [acts A, on G | to].
Proof.
move=> G; apply: (iffP idP) => [nGA x|nGA]; first exact: acts_act.
apply/subsetP=> a Aa; rewrite !inE; rewrite Aa.
by  apply/subsetP=> x; rewrite inE nGA.
Qed.

Lemma gactsM : forall N1 N2 : {set rT}, 
  N1 \subset D -> N2 \subset D ->
  [acts A, on N1 | to] -> [acts A, on N2 | to] -> [acts A, on N1 * N2 | to].
Proof.
move=> N1 N2 sN1D sN2D aAN1 aAN2; apply/gactsP=> x Ax y.
apply/idP/idP; case/mulsgP=> y1 y2 N1y1 N2y2 e.
  move: (actKin to Ax y); rewrite e; move<-.
  rewrite gactM ?groupV ?(subsetP sN1D y1) ?(subsetP sN2D) //.
  by apply: mem_mulg; rewrite ?(gactsP _ aAN1) ?(gactsP _ aAN2) // groupV.
rewrite e gactM // ?(subsetP sN1D y1) ?(subsetP sN2D) //.
by apply: mem_mulg; rewrite ?(gactsP _ aAN1) // ?(gactsP _ aAN2).
Qed.

Lemma gactsI : forall N1 N2 : {set rT}, 
  [acts A, on N1 | to] -> [acts A, on N2 | to] -> [acts A, on N1 :&: N2 | to].
Proof.
move=> N1 N2 aAN1 aAN2.
apply/subsetP=> x Ax; rewrite !inE Ax /=; apply/subsetP=> y Ny; rewrite inE.
case/setIP: Ny=> N1y N2y; rewrite inE ?astabs_act  ?N1y ?N2y //.
- by move/subsetP: aAN2; move/(_ x Ax).
- by move/subsetP: aAN1; move/(_ x Ax).
Qed.
  
Lemma gastabsP : forall (S : {set rT}) (a : aT), a \in A ->
       reflect (forall x : rT, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> S a Aa; apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
by rewrite !inE Aa; apply/subsetP=> x; rewrite inE nSa.
Qed.



End MoreGroupAction.

(******************************************************************************)
(* Helper lemmas for quotient actions.                                        *)
(******************************************************************************)

Section MoreQuotientAction.

Variables (aT rT : finGroupType).
Variables (A : {group aT})(D : {group rT}).
Variable to : groupAction A D.

Lemma qact_dom_doms : forall H : {group rT},
  H \subset D -> qact_dom to H \subset A.
Proof.
by move=> H sHD; apply/subsetP=> x; rewrite qact_domE // inE; case/andP.
Qed.

Lemma acts_qact_doms : forall H : {group rT}, H \subset D -> 
  [acts A, on H | to] -> qact_dom to H :=: A.
Proof.
move=> H sHD aH; apply/eqP; rewrite eqEsubset; apply/andP. 
split; first exact: qact_dom_doms.
apply/subsetP=> x Ax; rewrite qact_domE //; apply/gastabsP=> //.
by move/gactsP: aH; move/(_ x Ax).
Qed.

Lemma qacts_cosetpre : forall (H : {group rT})(K' : {group coset_groupType H}),
  H \subset D -> [acts A, on H | to] -> [acts qact_dom to H, on K' | to / H] ->
  [acts A, on (coset H @*^-1 K') | to].
Proof.
move=> H K' sHD aH aK'.
apply/subsetP=> x Ax; move/subsetP: aK'.
move: (Ax); rewrite -{1}(acts_qact_doms sHD aH)=> qdx; move/(_ x qdx) => nx.
rewrite !inE Ax; apply/subsetP=> y; case/morphpreP=> Ny /= K'Hy; rewrite inE.
apply/morphpreP; split; first by rewrite acts_qact_dom_norm.
by move/gastabsP: nx; move/(_  qdx (coset H y)); rewrite K'Hy qactE.
Qed.

Lemma qacts_coset : forall (H K : {group rT}), 
 H \subset D -> [acts A, on K | to] -> 
 [acts qact_dom to H, on (coset H) @* K | to / H].
Proof.
move=> H K sHD  aK.
apply/subsetP=> x qdx; rewrite inE qdx inE; apply/subsetP=> y.
case/morphimP=> z Nz Kz /= e; rewrite e inE qactE // mem_imset // inE.
move/gactsP: aK; move/(_ x (subsetP (qact_dom_doms sHD) _ qdx) z); rewrite Kz.
move->; move/acts_act: (acts_qact_dom to H); move/(_ x qdx z).
by rewrite Nz andbT.
Qed.

End MoreQuotientAction.

Section StableCompositionSeries.

Variables (aT rT : finGroupType).
Variables (D : {group rT})(A : {group aT}).
Variable to : groupAction A D.

Definition maxainv (B C : {set rT}) :=
  [max C of H | 
    [&& (H <| B), ~~ (B \subset H) & [acts A, on H | to]]].



Section MaxAinvProps.

Variables K N : {group rT}.

Lemma maxainv_norm : maxainv K N -> N <| K.
Proof. by move/maxgroupp; case/andP. Qed.

Lemma maxainv_proper : maxainv K N -> N \proper K.
Proof.
by move/maxgroupp; case/andP; rewrite properE; move/normal_sub->; case/andP.
Qed.

Lemma maxainv_sub : maxainv K N -> N \subset K.
Proof. move=> h; apply: proper_sub; exact: maxainv_proper. Qed.

Lemma maxainv_ainvar : maxainv K N -> A \subset 'N(N | to).
Proof. by move/maxgroupp; case/and3P. Qed.

Lemma maxainvS : maxainv K N -> N \subset K.
Proof. by move=> pNN; rewrite proper_sub // maxainv_proper. Qed.

Lemma maxainv_exists : K :!=: 1 -> {N : {group rT} | maxainv K N}.
Proof.
move=> nt; apply: ex_maxgroup. exists [1 rT]%G.
rewrite /= normal1 subG1 nt /=.
apply/subsetP=> a Da; rewrite !inE Da /= sub1set !inE.
by rewrite /= -actmE // morph1 eqxx.
Qed.

End MaxAinvProps.


Lemma maxainvM : forall G H K : {group rT},
  H \subset D -> K \subset D -> maxainv G H -> maxainv G K ->
  H :<>: K -> H * K = G.
Proof.
move=> G N1 N2 sN1D sN2D pmN1 pmN2 neN12.
have cN12 : commute N1 N2.
  apply: normC; apply: (subset_trans (maxainv_sub pmN1)).
  by rewrite normal_norm ?maxainv_norm.
wlog nsN21 : G N1 N2 sN1D sN2D pmN1 pmN2 neN12 cN12/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite eqEsubset negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; apply: sym_not_eq.
have nP : N1 * N2 <| G by rewrite normalM ?maxainv_norm.
have sN2P : N2 \subset N1 * N2 by rewrite mulg_subr ?group1.
case/maxgroupP: (pmN1); case/andP=> nN1G pN1G mN1.
case/maxgroupP: (pmN2); case/andP=> nN2G pN2G mN2.
case/andP: pN1G=> nsGN1 ha1; case/andP: pN2G=> nsGN2 ha2.
case e : (G \subset N1 * N2).
  by apply/eqP; rewrite eqEsubset e mulG_subG !normal_sub.
have: N1 <*> N2 = N2 by apply: mN2; rewrite /= ?comm_joingE // nP e /= gactsM.
by rewrite comm_joingE // => h; move: nsN21; rewrite -h mulg_subl.
Qed.


Definition asimple (K : {set rT}) := maxainv K 1.

Lemma asimpleP : forall K : {group rT},
  reflect (K :!=: 1 /\ (forall H : {group rT},
    H <| K -> [acts A, on H | to] -> H :=: 1 \/ H :=: K)) 
  (asimple K).
Proof.
move=> K; apply: (iffP idP).
  case/maxgroupP; rewrite normal1 /=; case/andP=> nsK1 aK H1.
  rewrite eqEsubset negb_and nsK1 /=; split => // H nHK ha.
  case eHK : (H :==: K); first by right; apply/eqP.
  left; apply: H1; rewrite ?sub1G // nHK; move/negbT: eHK.
  by rewrite eqEsubset negb_and normal_sub //=; move->.
case=> ntK h; apply/maxgroupP; split.
  move: ntK; rewrite eqEsubset sub1G andbT normal1; move->.
  apply/subsetP=> a Da; rewrite !inE Da /= sub1set !inE.
  by rewrite /= -actmE // morph1 eqxx.
move=> H; case/andP=> nHK; case/andP=> nsKH ha _.
case: (h _ nHK ha)=> //; move/eqP; rewrite eqEsubset.
by rewrite (negbTE nsKH) andbF.
Qed.

Implicit Type K : {group rT}.
Implicit Type s : seq {group rT}.


Definition acomps K s :=
  ((last K s) == 1%G) && 
  path [rel x y : {group rT} | maxainv x y] K s.

Lemma acompsP : forall K s, reflect
  (last K s = 1%G /\  path [rel x y : {group rT} | maxainv x y] K s) (acomps K s).
Proof. by move=> K s; apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_acomps : forall K s, acomps K s -> (K :==: 1) = (s == [::]).
Proof.
move=> K s; case/andP=> ls cs; apply/eqP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxgroupP.
by rewrite G1 sub1G andbF.
Qed.


Lemma acomps_cons : forall K H s, acomps K (H :: s) -> acomps H s.
Proof.
by move=> K H s; case/andP => /= ls; case/andP=> _ p; rewrite /acomps ls.
Qed.

Lemma asimple_acompsP : forall K s,
  acomps K s -> reflect (s = [:: 1%G]) (asimple K).
Proof.
move=> K s cs; apply: (iffP idP); last first.
  by move=> se; move: cs; rewrite se /=; case/andP=> /=; rewrite andbT.
case: s cs.
  by rewrite /acomps /= andbT; move/eqP->; case/asimpleP; rewrite eqxx.
move=> H s cs sG; apply/eqP.
rewrite eqseq_cons -(trivg_acomps (acomps_cons cs)) andbC andbb.
case/acompsP: cs => /= ls; case/andP=> mH ps.
case/maxgroupP: sG; case/and3P => _ ntG _ ->; rewrite ?sub1G //.
rewrite (maxainv_norm mH); case/andP: (maxainv_proper mH)=> _ ->.
exact: (maxainv_ainvar mH).
Qed.

Lemma exists_acomps : forall K : {group rT}, exists s, acomps K s.
Proof.
move=> K; elim: {K} #|K| {1 3}K (leqnn #|K|) => [K | n Hi K cK].
  by rewrite leqNgt cardG_gt0.
case/orP: (orbN (asimple K)) => [sK | nsK].
  by exists [:: (1%G : {group rT})]; rewrite /acomps eqxx /= andbT.
case/orP: (orbN (K :==: 1))=> [tK | ntK].
  by exists (Nil _); rewrite /acomps /= andbT.
case: (maxainv_exists ntK)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cK) // proper_card // (maxainv_proper pmN).
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /acomps.
by rewrite last_cons lasts /= pmN.
Qed.


End StableCompositionSeries.


Section StrongJordanHolder.


Section AuxiliaryLemmas.

Variables (aT rT : finGroupType).
Variables (A : {group aT})(D : {group rT}).
Variable to : groupAction A D.

Lemma maxainv_asimple_quo : forall G H : {group rT},
   H \subset D -> maxainv to G H -> asimple (to / H) (G / H).
Proof.
move=> G H sHD; case/maxgroupP; case/and3P=> nHG pHG aH Hmax.
apply/asimpleP; split; first by rewrite -subG1 quotient_sub1 ?normal_norm.
move=> K' nK'Q aK'.
have : (K' \proper (G / H)) || (G / H == K').
  by rewrite properE eqEsubset andbC (normal_sub nK'Q) !andbT orbC orb_negb_r.
case/orP=> [ pHQ | eQH]; last by right; apply sym_eq; apply/eqP.
left; pose K := ((coset H) @*^-1 K')%G.
have eK'I : K' \subset (coset H) @* 'N(H).
  by rewrite (subset_trans (normal_sub nK'Q)) ?morphimS ?normal_norm.
have eKK' : K' :=: K / H by rewrite /(K / H) morphpreK //=.
suff eKH : K :=: H by rewrite -trivg_quotient eKK' eKH.
have sHK : H \subset K by rewrite -ker_coset kerE morphpreS // sub1set group1.
apply: Hmax => //; apply/and3P; split; last exact: qacts_cosetpre.
  by rewrite -(quotientGK nHG) cosetpre_normal.
by move: (proper_subn pHQ); rewrite sub_morphim_pre ?normal_norm.
Qed.


Lemma asimple_quo_maxainv : forall G H : {group rT},
  H \subset D -> G \subset D -> [acts A, on G | to] -> [acts A, on H | to] ->
  H <| G -> asimple (to / H) (G / H) ->
    maxainv to G H.
Proof.
move=> G H sHD sGD aG aH nHG; case/asimpleP=> ntQ maxQ; apply/maxgroupP; split.
  by rewrite nHG -quotient_sub1 ?normal_norm // subG1 ntQ.
move=> K; case/and3P=> nKG nsGK aK sHK.
pose K' := (K / H)%G.
have K'dQ : K' <| (G / H)%G by apply: morphim_normal.
have nKH : H <| K by rewrite (normalS _ _ nHG) // normal_sub.
have : K' :=: 1%G \/ K' :=: (G / H).
  apply: (maxQ K' K'dQ) => /=.
  apply/subsetP=> x Adx. rewrite inE Adx /= inE. apply/subsetP=> y.
  rewrite quotientE; case/morphimP=> z Nz Kz ->; rewrite /= !inE qactE //.
  have ntoyx :  to z x \in 'N(H) by  rewrite (acts_qact_dom_norm Adx).
  apply/morphimP; exists (to z x) => //.
  suff h: qact_dom to H \subset A.
    by rewrite astabs_act // (subsetP aK) //; apply: (subsetP h).
  by apply/subsetP=> t; rewrite qact_domE // inE; case/ andP.
case; last first.
  move/quotient_injG; rewrite !inE /=; move/(_ nKH nHG)=> c; move: nsGK.
  by rewrite c subxx.
rewrite /= -trivg_quotient; move=> tK'; apply:(congr1 (@gval _)); move: tK'.
by apply: (@quotient_injG _ H); rewrite ?inE /= ?normal_refl.
Qed.

Lemma asimpleI : forall N1 N2: {group rT}, 
  N2 \subset 'N(N1) -> N1 \subset D ->
  [acts A, on N1 | to] -> [acts A, on N2 | to] -> 
  asimple (to / N1) (N2 / N1) -> asimple (to / (N2 :&: N1)) (N2 / (N2 :&: N1)).
Proof.
move=> N1 N2 nN21 sN1D aN1 aN2; case/asimpleP=> ntQ1 max1.
case: (restrmP (coset_morphism N1) nN21) => f1 [f1e f1ker f1pre f1im].
have hf2' : N2 \subset 'N(N2 :&: N1) by apply: normsI => //; rewrite normG.
have hf2'' : 'ker (coset (N2 :&: N1)) \subset 'ker f1.
  by rewrite f1ker !ker_coset.
pose f2 := factm_morphism  hf2'' hf2'.
apply/asimpleP; split.
   rewrite /= setIC; apply/negP; move: (second_isog nN21); move/isog_eq1->.
   by apply/negP.
move=> H nHQ2 aH; pose K := f2 @* H.
have nKQ1 : K <| N2 / N1.
  rewrite (_ : N2 / N1 = f2 @* (N2 / (N2 :&: N1))) ?morphim_normal //.
  by rewrite morphim_factm f1im.
have sqA : qact_dom to N1 \subset A.
  by apply/subsetP=> t; rewrite qact_domE // inE; case/andP.
have nNN2 : (N2 :&: N1) <| N2.
  rewrite /normal subsetIl; apply: normsI => //; exact: normG.
have aKQ1 : [acts qact_dom to N1, on K | to / N1].
  pose H':= coset (N2 :&: N1)@*^-1 H.
  have eHH' : H :=: H' / (N2 :&: N1) by rewrite cosetpreK.
  have -> : K :=: f1 @* H' by rewrite /K eHH' morphim_factm.
  have sH'N2 : H' \subset N2.
    rewrite /H' eHH' quotientGK ?normal_cosetpre //=.
    by rewrite sub_cosetpre_quo ?normal_sub.
  have -> : f1 @* H' = coset N1 @* H' by rewrite f1im //=. 
  apply: qacts_coset => //; apply: qacts_cosetpre => //; last exact: gactsI.
  by apply: (subset_trans (subsetIr _ _)).
have injf2 : 'injm f2.
  by rewrite ker_factm f1ker /= ker_coset /= subG1 /= -quotientE trivg_quotient.
have iHK : H \isog K.
  apply/isogP; pose f3 := restrm_morphism (normal_sub nHQ2) f2.
  by exists f3; rewrite ?injm_restrm // morphim_restrm setIid.
case: (max1 _ nKQ1 aKQ1).
  by move/eqP; rewrite -(isog_eq1 iHK); move/eqP->; left.
move=> he /=; right; apply/eqP; rewrite eqEcard normal_sub //=.
move: (second_isog nN21); rewrite setIC; move/card_isog->; rewrite -he.
by move/card_isog: iHK=> <-; rewrite leqnn.
Qed.

End AuxiliaryLemmas.



Variables (aT rT : finGroupType).
Variables (A : {group aT})(D : {group rT}).
Variable to : groupAction A D.

(******************************************************************************)
(* The factors associated to two A-stable composition series of the same      *)
(* group are the same up to isomorphism and permutation                       *)
(******************************************************************************)

Lemma StrongJordanHolderUniqueness : 
  forall (G : {group rT}) (s1 s2 : seq {group rT}),
  G \subset D -> acomps to G s1 -> acomps to G s2 -> 
  perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
move=> G; elim: {G} #|G| {-2}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
move=> s1 s2 hsD cs1 cs2; case/orP: (orbN (G :==: 1)) => [tG | ntG].
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_acomps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_acomps cs2).
  by rewrite /= perm_eq_refl.
case/orP: (orbN (asimple to G))=> [sG | nsG].
  have -> : s1 = [:: 1%G ] by apply/(asimple_acompsP cs1).
  have -> : s2 = [:: 1%G ] by apply/(asimple_acompsP cs2).
  by rewrite /= perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have sN1D : N1 \subset D.
  by apply: subset_trans hsD; apply: maxainv_sub maxN_1.
have sN2D : N2 \subset D.
  by apply: subset_trans hsD; apply: maxainv_sub maxN_2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxainv_proper maxN_1).
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxainv_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /acomps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: (maxainv_norm maxN_1).
have nN2G : N2 <| G by apply: (maxainv_norm maxN_2).
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxainvM _ _ maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxainvM _ _ maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_acomps to N)=> sN; case/andP=> lsN csN.
have aN1 : [acts A, on N1 | to].
  by case/maxgroupP: maxN_1; case/and3P.
have aN2 : [acts A, on N2 | to].
  by case/maxgroupP: maxN_2; case/and3P.
have nNN1 : N <| N1.
  by apply: (normalS _ _ nNG); rewrite ?subsetIl ?normal_sub.
have nNN2 : N <| N2.
  by apply: (normalS _ _ nNG); rewrite ?subsetIr ?normal_sub.
have aN : [ acts A, on N1 :&: N2 | to].
  apply/subsetP=> x Ax; rewrite !inE Ax /=; apply/subsetP=> y Ny; rewrite inE.
  case/setIP: Ny=> N1y N2y. rewrite inE ?astabs_act  ?N1y ?N2y //.
    by move/subsetP: aN2; move/(_ x Ax).
  by move/subsetP: aN1; move/(_ x Ax).
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /acomps ?lst1 //= lsN csN andbT /=.
  apply: asimple_quo_maxainv=> //; first by apply: subIset; rewrite sN1D.
  apply: asimpleI => //.
    apply: subset_trans (normal_norm nN2G); exact: normal_sub.
  rewrite -quotientMidl (maxainvM _ _ maxN_2) //.
    by apply: maxainv_asimple_quo.
  by move=> e; apply: neN12.
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /acomps ?lst2 //= lsN csN andbT /=.
  apply: asimple_quo_maxainv=> //; first by apply: subIset; rewrite sN1D.
  have e : N1 :&: N2 :=: N2 :&: N1 by rewrite setIC.
  rewrite (group_inj (setIC N1 N2)); apply: asimpleI => //.
    apply: subset_trans (normal_norm nN1G); exact: normal_sub.
  rewrite -quotientMidl (maxainvM _ _ maxN_1) //.
  exact: maxainv_asimple_quo.
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
apply: perm_eq_trans i2; exact: perm_eq_refl.
Qed.

End StrongJordanHolder.






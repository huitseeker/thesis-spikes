(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop.
Require Import finset fingroup morphism automorphism quotient action.
Require Import commutator center.
(*****************************************************************************)
(*           H <|<| G   <=> H is subnormal in G, i.e., H <| ... <| G.        *)
(* invariant_factor A H G <=> A normalises both H and G, and H <| G.         *)
(*           A.-invariant <=> the (invariant_factor A) relation, in the      *)
(*                            in the context of the g_rel.-series notation.  *) 
(*    g_rel.-series H s <=> H :: s is a sequence of groups whose projection  *)
(*                          to sets satisfies relation g_rel pairwise; for   *)
(*                          example H <|<| G iff G = last H s for some s     *)
(*                          such that normal.-series H s.                    *)
(*   stable_factor A H G == H <| G and A centralises G / H                   *)
(*             A.-stable == the stable_factor relation, in the scope of the  *)
(*                          r.-series notation.                              *)
(*            G.-central == the central_factor relation, in the scope of the *)
(*                          r.-series notation.                              *)
(*       maximal M G == M is a maximal proper subgroup of G                  *)
(*    maximal_eq M G == (M == G) or (maximal M G)                            *)
(*   maxnormal M G N == M is a maximal subgroup of G normalized by N         *)
(*     minnormal M N == M is a minimal nontrivial subgroup normalized by N   *)
(*          simple G == G is a (nontrivial) simple group                     *)
(*                   := minnormal G G                                        *)
(*              G.-chief == the chief_factor relation, in the scope of the   *)
(*                          r.-series notation.                              *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section GroupDefs.

Variable gT : finGroupType.
Implicit Types A B U V : {set gT}.

Notation Local groupT := (group_of (Phant gT)).

Definition subnormal A B :=
  (A \subset B) && (iter #|B| (fun N => generated (class_support A N)) B == A).

Definition invariant_factor A B C :=
  [&& A \subset 'N(B), A \subset 'N(C) & B <| C].

Definition group_rel_of (r : rel {set gT}) := [rel H G : groupT | r H G].

Definition stable_factor A V U :=
  ([~: U, A] \subset V) && (V <| U). (* this orders allows and3P to be used *)

Definition central_factor A V U :=
  [&& [~: U, A] \subset V, V \subset U & U \subset A].

Definition maximal A B := [max A of G | G \proper B].

Definition maximal_eq A B := (A == B) || maximal A B.

Definition maxnormal A B U :=
  [max A of G | (G \proper B) && (U \subset 'N(G))].

Definition minnormal A B := [min A of G | (G :!=: 1) && (B \subset 'N(G))].

Definition simple A := minnormal A A.

Definition chief_factor A V U := maxnormal V U A && (U <| A).
End GroupDefs.

Prenex Implicits subnormal maximal simple.

Notation "H <|<| G" := (subnormal H G)
  (at level 70, no associativity) : group_scope.

Notation "A .-invariant" := (invariant_factor A)
  (at level 2, format "A .-invariant") : group_rel_scope.
Notation "A .-stable" := (stable_factor A)
  (at level 2, format "A .-stable") : group_rel_scope.
Notation "A .-central" := (central_factor A)
  (at level 2, format "A .-central") : group_rel_scope.
Notation "G .-chief" := (chief_factor G)
  (at level 2, format "G .-chief") : group_rel_scope.

Arguments Scope group_rel_of [_ group_rel_scope subgroup_scope subgroup_scope].

Notation "r .-series" := (path (rel_of_simpl_rel (group_rel_of r)))
  (at level 2, format "r .-series") : group_scope.

Section Subnormal.

Variable gT : finGroupType.
Notation sT := {set gT}.

Implicit Types A B C D : sT.
Implicit Type G H K : {group gT}.


Let setIgr H G := (G :&: H)%G.
Let sub_setIgr : forall G H, G \subset H -> G = setIgr H G.
Proof. by move=> G H; move/setIidPl; move/group_inj. Qed.

Let path_setIgr : forall H G s,
   normal.-series H s -> normal.-series (setIgr G H) (map (setIgr G) s).
Proof.
move=> H G s; elim: s H => //= K s IHs H; do 2![case/andP] => sHK nHK Ksn.
by rewrite /normal setSI ?normsIG ?IHs.
Qed.

Lemma subnormalP : forall H G,
  reflect (exists2 s, normal.-series H s & last H s = G) (H <|<| G).
Proof.
move=> H G; apply: (iffP andP) => [[sHG snHG] | [s Hsn <-{G}]].
  elim: {G}#|G| {-2}G sHG snHG => [|m IHm] G sHG.
    by exists [::]; last by apply/eqP; rewrite eq_sym.
  rewrite iterSr; case/IHm=> [|s Hsn defG].
    by rewrite sub_gen // class_supportEr (bigD1 1) //= conjsg1 subsetUl.
  exists (rcons s G); rewrite ?last_rcons // -cats1 path_cat Hsn defG /=.
  rewrite /normal gen_subG class_support_subG //=.
  by rewrite norms_gen ?class_support_normG.
set f := fun _ => <<_>>; have idf: iter _ f H == H.
  by elim=> //= m IHm; rewrite (eqP IHm) /f class_support_id genGid.
elim: {s}(size s) {-2}s (eqxx (size s)) Hsn => [[] //= | m IHm s].
case/lastP: s => // s G; rewrite size_rcons last_rcons -cats1 path_cat /=.
set K := last H s => def_m; case/and3P=> Hsn; case/andP=> sKG nKG _.
have:= sKG; rewrite subEproper; case/predU1P=> [<-|prKG]; first exact: IHm.
pose L := [group of f G].
have sHK: H \subset K by case/IHm: Hsn.
have sLK: L \subset K by rewrite gen_subG class_support_sub_norm.
rewrite -(subnK (proper_card (sub_proper_trans sLK prKG))) iter_add iterSr.
have defH: H = setIgr L H by rewrite -sub_setIgr ?sub_gen ?sub_class_support.
have: normal.-series H (map (setIgr L) s) by rewrite defH path_setIgr.
case/IHm=> [|_]; first by rewrite size_map.
by rewrite {1 2}defH last_map (subset_trans sHK) //= (setIidPr sLK); move/eqP->.
Qed.

Lemma subnormal_refl : forall G, G <|<| G.
Proof. by move=> G; apply/subnormalP; exists [::]. Qed.

Lemma subnormal_trans : forall K H G, H <|<| K -> K <|<| G -> H <|<| G.
Proof.
move=> K H G; case/subnormalP=> s1 Hs1 <-; case/subnormalP=> s2 Hs12 <-.
by apply/subnormalP; exists (s1 ++ s2); rewrite ?last_cat // path_cat Hs1.
Qed.

Lemma normal_subnormal : forall H G, H <| G -> H <|<| G.
Proof.
by move=> H G nsHG; apply/subnormalP; exists [:: G]; rewrite //= nsHG.
Qed.

Lemma setI_subnormal : forall G H K,
  K \subset G -> H <|<| G -> H :&: K <|<| K.
Proof.
move=> G H K sKG; case/subnormalP=> s Hs defG; apply/subnormalP.
exists (map (setIgr K) s); first exact: path_setIgr.
rewrite (last_map (setIgr K)) defG.
by apply: val_inj; rewrite /= (setIidPr sKG).
Qed.

Lemma subnormal_sub : forall G H, H <|<| G -> H \subset G.
Proof. by move=> G H; case/andP. Qed.

Lemma invariant_subnormal : forall A G H,
    A \subset 'N(G) -> A \subset 'N(H) -> H <|<| G ->
  exists2 s, (A.-invariant).-series H s & last H s = G.
Proof.
move=> A G H nGA nHA; case/andP; move: #|G| => m.
elim: m => [|m IHm] in G nGA * => sHG.
  by rewrite eq_sym; exists [::]; last exact/eqP.
rewrite iterSr; set K := <<_>>.
have nKA: A \subset 'N(K) by rewrite norms_gen ?norms_class_support.
have sHK: H \subset K by rewrite sub_gen ?sub_class_support.
case/IHm=> // s Hsn defK; exists (rcons s G); last by rewrite last_rcons.
rewrite path_rcons Hsn !andbA defK nGA nKA /= -/K.
by rewrite gen_subG class_support_subG ?norms_gen ?class_support_normG.
Qed.

Lemma subnormalEsupport : forall G H,
  H <|<| G -> H :=: G \/ <<class_support H G>> \proper G.
Proof.
move=> G H; case/andP=> sHG; set K := <<_>>; move/eqP <-.
have: K \subset G by rewrite gen_subG class_support_subG.
rewrite subEproper; case/predU1P=> [defK|]; [left | by right].
by elim: #|G| => //= _ ->.
Qed.

Lemma subnormalEr : forall G H, H <|<| G -> 
  H :=: G \/ (exists K : {group gT}, [/\ H <|<| K, K <| G & K \proper G]).
Proof.
move=> G H; case/subnormalP=> s Hs <-{G}.
elim/last_ind: s Hs => [|s G IHs]; first by left.
rewrite last_rcons -cats1 path_cat /= andbT; set K := last H s.
case/andP=> Hs nsKG; have:= normal_sub nsKG; rewrite subEproper.
case/predU1P=> [<- | prKG]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

Lemma subnormalEl : forall G H, H <|<| G ->
  H :=: G \/ (exists K : {group gT}, [/\ H <| K, K <|<| G & H \proper K]).
Proof.
move=> G H; case/subnormalP=> s Hs <-{G}.
elim: s H Hs => /= [|K s IHs] H; first by left.
case/andP=> nsHK Ks; have:= normal_sub nsHK; rewrite subEproper.
case/predU1P=> [-> | prHK]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

End Subnormal.

Implicit Arguments subnormalP [gT G H].
Prenex Implicits subnormalP.

Section MorphSubNormal.

Variable gT : finGroupType.
Implicit Type G H K : {group gT}.

Lemma morphim_subnormal : forall (rT : finGroupType) 
  G (f : {morphism G >-> rT}) H K, H <|<| K -> f @* H <|<| f @* K.
Proof.
move=> rT A f H K; case/subnormalP => s Hs <-{K}; apply/subnormalP.
elim: s H Hs => [|K s IHs] H /=; first by exists [::].
case/andP=> nsHK; case/IHs=> fs Hfs <-.
by exists ([group of f @* K] :: fs); rewrite /= ?morphim_normal.
Qed.

Lemma quotient_subnormal : forall H G K, G <|<| K -> G / H <|<| K / H.
Proof. by move=> H G K; exact: morphim_subnormal. Qed.

End MorphSubNormal.

Section MaxProps.

Variable gT : finGroupType.
Implicit Types G H M : {group gT}.

Lemma maximal_eqP : forall M G,
  reflect (M \subset G  /\
             forall H, M \subset H -> H \subset G -> H :=: M \/ H :=: G)
       (maximal_eq M G).
Proof.
move=> M G; rewrite subEproper /maximal_eq; case: eqP => [->|_]; first left.
  by split=> // H sGH sHG; right; apply/eqP; rewrite eqEsubset sHG.
apply: (iffP maxgroupP) => [] [sMG maxM]; split=> // H.
  by move/maxM=> maxMH; rewrite subEproper; case/predU1P; auto.
by rewrite properEneq; case/andP; move/eqP=> neHG sHG; case/maxM.
Qed.

Lemma maximal_exists : forall H G,
    H \subset G ->
  H :=: G \/ (exists2 M : {group gT}, maximal M G & H \subset M).
Proof.
move=> H G; rewrite subEproper; case/predU1P=> sHG; first by left.
suff [M *]: {M : {group gT} | maximal M G & H \subset M} by right; exists M.
exact: maxgroup_exists.
Qed.

Lemma mulg_normal_maximal : forall G M H,
  M <| G -> maximal M G -> H \subset G -> ~~ (H \subset M) -> (M * H = G)%g.
Proof.
move=> G M H; case/andP=> sMG nMG; case/maxgroupP=> _ maxM sHG not_sHM.
apply/eqP; rewrite eqEproper mul_subG // -norm_joinEr ?(subset_trans sHG) //.
by apply: contra not_sHM; move/maxM <-; rewrite ?joing_subl ?joing_subr.
Qed.

End MaxProps.

Section MinProps.

Variable gT : finGroupType.
Implicit Types G H M : {group gT}.


Lemma minnormal_exists : forall G H, H :!=: 1 -> G \subset 'N(H) ->
  {M : {group gT} | minnormal M G & M \subset H}.
Proof. by move=> G H ntH nHG; apply: mingroup_exists (H) _; rewrite ntH. Qed.

End MinProps.

Section MorphPreMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types Q R : {group rT}.

Lemma morphpre_maximal : forall Q R,
  Q \subset f @* D -> R \subset f @* D ->
  maximal (f @*^-1 Q) (f @*^-1 R) = maximal Q R.
Proof.
move=> Q R dQ dR.
apply/maxgroupP/maxgroupP; rewrite morphpre_proper //= => [] [sQR maxQ].
  split=> // M sMR sQM; have dM := subset_trans (proper_sub sMR) dR.
  rewrite -(morphpreK dQ) -(maxQ (f @*^-1 M)%G) ?morphpreK ?morphpreSK //.
  by rewrite morphpre_proper.
split=> // M sMR sQM; have dM: M \subset D.
  apply: subset_trans (proper_sub sMR) _; exact: subsetIl.
have defM: f @*^-1 (f @* M) = M.
  apply: morphimGK dM; apply: subset_trans sQM; exact: ker_sub_pre.
rewrite -defM; congr (f @*^-1 _); apply: maxQ.
  by rewrite -defM morphpre_proper ?morphimS in sMR.
by rewrite -(morphpreK dQ) morphimS.
Qed.

Lemma morphpre_maximal_eq : forall Q R,
  Q \subset f @* D -> R \subset f @* D ->
  maximal_eq (f @*^-1 Q) (f @*^-1 R) = maximal_eq Q R.
Proof.
move=> Q R dQ dR.
by rewrite /maximal_eq morphpre_maximal // !eqEsubset !morphpreSK.
Qed.

End MorphPreMax.

Section InjmMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variables G H K : {group gT}.

Hypothesis injf : 'injm f.

Lemma injm_maximal :
  G \subset D -> H \subset D -> maximal (f @* G) (f @* H) = maximal G H.
Proof.
move=> dG dH; rewrite -(morphpre_invm injf) -(morphpre_invm injf H).
by rewrite morphpre_maximal ?morphim_invm.
Qed.

Lemma injm_maximal_eq :
  G \subset D -> H \subset D -> maximal (f @* G) (f @* H) = maximal G H.
Proof.
by move=> dG dH; rewrite /maximal_eq injm_maximal // !eqEsubset !injmSK.
Qed.

End InjmMax.

Section QuoMax.

Variables (gT : finGroupType) (K G H : {group gT}).

Lemma cosetpre_maximal : forall Q R : {group coset_of K},
  maximal (coset K @*^-1 Q) (coset K @*^-1 R) = maximal Q R.
Proof. by move=> Q R; rewrite morphpre_maximal ?sub_im_coset. Qed.

Lemma cosetpre_maximal_eq : forall Q R : {group coset_of K},
  maximal_eq (coset K @*^-1 Q) (coset K @*^-1 R) = maximal_eq Q R.
Proof.
by move=> Q R; rewrite /maximal_eq !eqEsubset !cosetpreSK cosetpre_maximal.
Qed.

Lemma quotient_maximal :
  K <| G -> K <| H -> maximal (G / K) (H / K) = maximal G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal ?quotientGK. Qed.

Lemma quotient_maximal_eq :
  K <| G -> K <| H -> maximal_eq (G / K) (H / K) = maximal_eq G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal_eq ?quotientGK. Qed.

Lemma maximalJ : forall x, maximal (G :^ x) (H :^ x) = maximal G H.
Proof.
move=> x; rewrite -{1}(setTI G) -{1}(setTI H) -!morphim_conj.
by rewrite injm_maximal ?subsetT ?injm_conj.
Qed.

Lemma maximal_eqJ : forall x, maximal_eq (G :^ x) (H :^ x) = maximal_eq G H.
Proof. by move=> x; rewrite /maximal_eq !eqEsubset !conjSg maximalJ. Qed.

End QuoMax.

Section MaxNormalProps.

Variables (gT : finGroupType).

Implicit Types A B C : {set gT}.
Implicit Types G H K : {group gT}.

Lemma maxnormal_normal : forall A B, maxnormal A B B -> A <| B.
Proof.
move=> A B; case/maxsetP; case/and3P; move/gen_set_id=> /= -> pAB nAB _.
by rewrite /normal proper_sub.
Qed.

Lemma maxnormal_proper : forall A B C, maxnormal A B C -> A \proper B.
Proof.
move=> A B C; case/maxsetP; case/andP=> gA; case/andP=> pAB _ _.
exact: (sub_proper_trans (subset_gen A)).
Qed.

Lemma maxnormal_sub : forall A B C, maxnormal A B C -> A \subset B.
Proof.
move=> A B C hmax; rewrite proper_sub //; exact: (maxnormal_proper hmax).
Qed.

Lemma ex_maxnormal_ntrivg : forall G,
  G :!=: 1-> {N : {group gT} | maxnormal N G G}.
Proof.
move=> G ntG; apply: ex_maxgroup; exists [1 gT]%G; rewrite norm1 proper1G.
by rewrite subsetT ntG.
Qed.

Lemma maxnormalM : forall G H K,
  maxnormal H G G -> maxnormal K G G -> H :<>: K -> H * K = G.
Proof.
move=> G N1 N2 pmN1 pmN2 neN12.
have cN12 : commute N1 N2.
  apply: normC; apply: (subset_trans (maxnormal_sub pmN1)).
  by rewrite normal_norm ?maxnormal_normal.
wlog nsN21 : G N1 N2 pmN1 pmN2 neN12 cN12/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite eqEsubset negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; apply: sym_not_eq.
have nP : N1 * N2 <| G by rewrite normalM ?maxnormal_normal.
have sN2P : N2 \subset N1 * N2 by rewrite mulg_subr ?group1.
case/maxgroupP: (pmN2); case/andP=> nN2G pN2G mN2.
have contr : (N1 <*> N2) \proper G -> (N1 <*> N2) == N2.
  move => ne; apply/eqP=> /=; apply: mN2 => //=; rewrite ?ne comm_joingE //.
  by rewrite normal_norm.
suff h: ~~ (N1 * N2 \proper G).
  apply/eqP; rewrite eqEproper h.
  by rewrite mul_subG // ?(maxnormal_sub pmN1) ?(maxnormal_sub pmN2).
rewrite -comm_joingE //; apply: (contra contr).
rewrite comm_joingE // eqEsubset negb_and sN2P orbF; apply/negP=> h.
apply: (negP nsN21); apply: subset_trans h; apply: mulG_subl.
Qed.

End MaxNormalProps.

Section Simple.

Implicit Types gT rT : finGroupType.

Lemma simpleP : forall gT (G : {group gT}),
  reflect (G :!=: 1 /\ forall H : {group gT}, H <| G -> H :=: 1 \/ H :=: G)
          (simple G).
Proof.
move=> gT G; apply: (iffP mingroupP); rewrite normG andbT.
  case=> ntG simG; split=> // N; case/andP=> sNG nNG.
  by case: (eqsVneq N 1) => [|ntN]; [left | right; apply: simG; rewrite ?ntN].
case=> ntG simG; split=> // N; case/andP=> ntN nNG sNG.
by case: (simG N) ntN => // [|->]; [exact/andP | case/eqP].
Qed.

Lemma quotient_simple : forall gT (G H : {group gT}),
  H <| G -> simple (G / H) = maxnormal H G G.
Proof.
move=> gT G H nHG; apply/simpleP/maxgroupP=> [[ntG simG] | []].
  rewrite andbAC andbC -(quotient_sub1 (normal_norm nHG)) subG1 ntG.
  split=> // N; do 2![case/andP] => sNG ntN nNG sHN.
  case: (simG (N / H)%G) => [|| /= eqNG].
  - apply: quotient_normal; exact/andP.
  - move/trivgP=> trNH; apply/eqP; rewrite eqEsubset sHN andbT.
    by rewrite -quotient_sub1 // (subset_trans sNG) ?normal_norm.
  by case/negP: ntN; rewrite -(quotientSGK _ sHN) ?normal_norm // eqNG.
rewrite andbAC -subG1 (quotient_sub1 (normal_norm nHG)).
case/andP=> _ sGH simG; split=> // NH.
case/(inv_quotientN _) => //= N ->{NH} sHN nNG.
case sGN: (G \subset N); [right | left].
  by congr (_ / H); apply/eqP; rewrite eqEsubset sGN normal_sub.
by rewrite (simG N) ?trivg_quotient // andbAC sGN andbT.
Qed.

Lemma isog_simple : forall gT rT (G : {group gT}) (M : {group rT}),
  G \isog M -> simple G = simple M.
Proof.
move=> gT rT G M eqGM; wlog simM: gT rT G M eqGM / simple M.
  by move=> IH; apply/idP/idP=> sim; move/IH: (sim) ->; rewrite // isog_sym.
rewrite simM; case/simpleP: simM; case/isogP: eqGM => f injf <- ntM simM.
apply/simpleP; split=> [|N nNG].
  by apply: contra ntM; move/eqP=> /= M1; rewrite {3}M1 /= morphim1.
case: (andP nNG); move/(morphim_invm injf) => <- _.
have: f @* N <| f @* G by rewrite morphim_normal.
by case/simM=> /= ->; [left | right]; rewrite (morphim1, morphim_invm).
Qed.

Lemma simple_maxnormal : forall gT (G : {group gT}),
   simple G = maxnormal 1 G G.
Proof.
move=> gT G; rewrite -quotient_simple ?normal1 //.
by rewrite -(isog_simple (quotient1_isog G)).
Qed.

End Simple.

Section Chiefs.

Variable gT: finGroupType.

Lemma chief_factor_minnormal : forall G V U : {group gT},
  chief_factor G V U -> minnormal (U / V) (G / V).
Proof.
move=> G V U; case/and3P=> maxV sUG nUG.
case/maxgroupP: maxV; do 2![case/andP]=> sVU VltU nVG maxV.
have nVU := subset_trans sUG nVG.
apply/mingroupP; rewrite -subG1 quotient_sub1 ?VltU ?quotient_norms //.
split=> // Wbar ntWbar sWbarU; case/andP: ntWbar. 
have{sWbarU} [|W ->{Wbar} sVW] := inv_quotientS _ sWbarU; first exact/andP.
rewrite subEproper; case/predU1P=> [-> // | WltU ntWV].
have nVW := subset_trans (proper_sub WltU) nVU; have nWV := normsG sVW.
rewrite -quotient_normG ?quotientSGK // => [nWG|]; last exact/andP.
by rewrite (maxV W) ?trivg_quotient ?eqxx ?WltU in ntWV.
Qed.

Lemma acts_irrQ : forall G U V : {group gT},
    G \subset 'N(V) -> V <| U ->
  acts_irreducibly G (U / V) 'Q = minnormal (U / V) (G / V).
Proof.
move=> G U V nVG nsVU; apply/mingroupP/mingroupP; case; case/andP=> ->.
  rewrite astabsQ // subsetI nVG /= => nUG minUV.
  rewrite quotient_norms //; split=> // H; case/andP=> ntH nHG sHU.
  apply: minUV (sHU); rewrite ntH -(cosetpreK H) actsQ //.
  by apply: subset_trans (morphpre_norms _ nHG); rewrite -sub_quotient_pre.
rewrite sub_quotient_pre // => nUG minU; rewrite astabsQ //.
rewrite (subset_trans nUG); last first.
  by rewrite subsetI subsetIl /= -{2}(quotientGK nsVU) morphpre_norm.
split=> // H; case/andP=> ntH nHG sHU.
rewrite -{1}(cosetpreK H) astabsQ ?normal_cosetpre ?subsetI ?nVG //= in nHG.
apply: minU sHU; rewrite ntH; apply: subset_trans (quotientS _ nHG) _.
by rewrite -{2}(cosetpreK H) quotient_norm.
Qed.

Lemma chief_series_exists : forall H G : {group gT},
  H <| G -> {s | (G.-chief).-series 1%G s & last 1%G s = H}.
Proof.
move=> H G; elim: {H}_.+1 {-2}H (ltnSn #|H|) => // m IHm U leUm nsUG.
case: (eqVneq U 1%G) => [-> | ntU]; first by exists [::].
have [V maxV]: {V : {group gT} | maxnormal V U G}.
  by apply: ex_maxgroup; exists 1%G; rewrite proper1G ntU norms1.
have [ltVU nVG] := andP (maxgroupp maxV).
have [||s ch_s defV] := IHm V; first exact: leq_trans (proper_card ltVU) _.
  by rewrite /normal (subset_trans (proper_sub ltVU) (normal_sub nsUG)).
exists (rcons s U); last by rewrite last_rcons.
rewrite path_rcons defV /= ch_s /chief_factor; exact/and3P.
Qed.

End Chiefs.

Section Central.

Variable gT : finGroupType.
Variable G : {group gT}.
Implicit Type H K : {group gT}.

Lemma central_factor_central : forall H K,
  central_factor G H K -> (K / H) \subset 'Z(G / H).
Proof.
by move=> H K; case/and3P; move/quotient_cents2r=> *; rewrite subsetI quotientS.
Qed.


Lemma central_central_factor : forall H K,
  (K / H) \subset 'Z(G / H) -> H <| K -> H <| G -> central_factor G H K.
Proof.
move=> H K; rewrite subsetI; case/andP=> h1 h2 nHK nKG. 
rewrite /central_factor -quotient_cents2 ?normal_norm // h2 normal_sub //.
by move: h1; rewrite quotientSGK ?normal_norm // normal_sub.
Qed.


End Central.

(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype div.
Require Import bigop prime finset fingroup morphism automorphism quotient.
Require Import commutator gproduct gfunctor center gseries.

(******************************************************************************)
(*   This file defines nilpotent and solvable groups, and give some of their  *)
(* elementary properties; more will be added later (e.g., the nilpotence of   *)
(* p-groups in sylow.v, or the fact that minimal normal subgroups of solvable *)
(* groups are elementary abelian in maximal.v). This file defines:            *)
(*   nilpotent G == G is nilpotent, i.e., [~: H, G] is a proper subgroup of H *)
(*                  for all nontrivial H <| G.                                *)
(*    solvable G == G is solvable, i.e., H^`(1) is a proper subgroup of H for *)
(*                  all nontrivial subgroups H of G.                          *)
(*       'L_n(G) == the nth term of the lower central series, namely          *)
(*                  [~: G, ..., G] (n Gs) if n > 0, with 'L_0(G) = G.         *)
(*                  G is nilpotent iff 'L_n(G) = 1 for some n.                *)
(*       'Z_n(G) == the nth term of the upper central series, i.e.,           *)
(*                  with 'Z_0(G) = 1, 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)). *)
(*   nil_class G == the nilpotence class of G, i.e., the least n such that    *)
(*                  'L_n.+1(G) = 1 (or, equivalently, 'Z_n(G) = G), if G is   *)
(*                  nilpotent; we take nil_class G = #|G| when G is not       *)
(*                  nilpotent, so nil_class G < #|G| iff G is nilpotent.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section SeriesDefs.

Variables (n : nat) (gT : finGroupType) (A : {set gT}).

Definition lower_central_at_rec := iter n (fun B => [~: B, A]) A.

Definition upper_central_at_rec := iter n (fun B => coset B @*^-1 'Z(A / B)) 1.

End SeriesDefs.

(* By convention, the lower central series starts at 1 while the upper series *)
(* starts at 0 (sic).                                                         *)
Definition lower_central_at n := lower_central_at_rec n.-1.

(* Note: 'nosimpl' MUST be used outside of a section -- the end of section    *)
(* "cooking" destroys it.                                                     *)
Definition upper_central_at := nosimpl upper_central_at_rec.

Notation "''L_' n ( G )" := (lower_central_at n G)
  (at level 8, n at level 2, format "''L_' n ( G )") : group_scope.

Notation "''Z_' n ( G )" := (upper_central_at n G)
  (at level 8, n at level 2, format "''Z_' n ( G )") : group_scope.

Section PropertiesDefs.

Variables (gT : finGroupType) (A : {set gT}).

Definition nilpotent :=
  forallb G : {group gT}, (G \subset A :&: [~: G, A]) ==> (G :==: 1).

Definition nil_class := index 1 (mkseq (fun n => 'L_n.+1(A)) #|A|).

Definition solvable :=
  forallb G : {group gT}, (G \subset A :&: [~: G, G]) ==> (G :==: 1).

End PropertiesDefs.

Prenex Implicits nil_class nilpotent solvable.

Section NilpotentProps.

Variable gT: finGroupType.

Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma nilpotent1 : nilpotent [1 gT].
Proof. apply/forallP=> H; rewrite commG1 setIid -subG1; exact/implyP. Qed.

Lemma nilpotentS : forall A B, B \subset A -> nilpotent A -> nilpotent B.
Proof.
move=> A B sBA nilA; apply/forallP=> H; apply/implyP=> sHR.
have:= forallP nilA H; rewrite (subset_trans sHR) //.
by apply: subset_trans (setIS _ _) (setSI _ _); rewrite ?commgS.
Qed.

Lemma nil_comm_properl : forall G H A,
    nilpotent G -> H \subset G -> H :!=: 1 -> A \subset 'N_G(H) ->
  [~: H, A] \proper H.
Proof.
move=> G H A nilG sHG ntH; rewrite subsetI properE; case/andP=> sAG nHA.
rewrite (subset_trans (commgS H (subset_gen A))) ?commg_subl ?gen_subG //.
apply: contra ntH => sHR; have:= forallP nilG H; rewrite subsetI sHG.
by rewrite (subset_trans sHR) ?commgS.
Qed.

Lemma nil_comm_properr : forall G A H,
    nilpotent G -> H \subset G -> H :!=: 1 -> A \subset 'N_G(H) ->
  [~: A, H] \proper H.
Proof. by move=> G A H; rewrite commGC; exact: nil_comm_properl. Qed.
 
Lemma centrals_nil : forall (s : seq {group gT})(G : {group gT}),
  G.-central.-series 1%G s -> last 1%G s = G -> nilpotent G.
Proof.
move=> s G cs ls; apply/forall_inP=> H; rewrite subsetI; case/andP=> sHG sHR.
suff: forall n,  n <= size s -> H \subset nth G (1%G :: s) ((size s) - n).
  move/(_ (size s)) => /=; rewrite subnn -subG1 leqnn; exact.
elim=> [|n ihn ltns]; first by rewrite subn0 nth_last last_cons ls.
apply: subset_trans sHR _; apply: subset_trans (commSg _ (ihn (ltnW ltns))) _.
have e: (size s - n.+1 < size s) by rewrite -ltn_subS // leq_subr.
by rewrite ltn_subS //=; case/and3P: {e} (pathP G cs (size s - n.+1) e).
Qed.

End NilpotentProps.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma lcn0 : forall A, 'L_0(A) = A. Proof. by []. Qed.
Lemma lcn1 : forall A, 'L_1(A) = A. Proof. by []. Qed.
Lemma lcnSn : forall n A, 'L_n.+2(A) = [~: 'L_n.+1(A), A]. Proof. by []. Qed.
Lemma lcnSnS : forall n G, [~: 'L_n(G), G] \subset 'L_n.+1(G).
Proof. by case=> [|n] A; rewrite ?der1_subG // lcnSn. Qed.
Lemma lcnE : forall n A, 'L_n.+1(A) = lower_central_at_rec n A.
Proof. by []. Qed.
Lemma lcn2 : forall A, 'L_2(A) = A^`(1). Proof. by []. Qed.

Lemma lcn_group_set : forall n G, group_set 'L_n(G).
Proof. move=> n G; case: n; last elim=> *; exact: groupP. Qed.

Canonical Structure lower_central_at_group n G := Group (lcn_group_set n G).

Lemma lcn_char : forall n G, 'L_n(G) \char G.
Proof.
by case=> [|n] G; last elim: n => [|n IHn]; rewrite ?lcnSn ?charR ?char_refl.
Qed.

Lemma lcn_normal : forall n G, 'L_n(G) <|  G.
Proof. move=> n G; apply: char_normal; exact: lcn_char. Qed.

Lemma lcn_sub : forall n G, 'L_n(G) \subset G.
Proof. by move=> n G; case/andP: (lcn_normal n G). Qed.

Lemma lcn_norm : forall n G, G \subset 'N('L_n(G)).
Proof. by move=> n G; case/andP: (lcn_normal n G). Qed.

Lemma lcn_subS : forall n G, 'L_n.+1(G) \subset 'L_n(G).
Proof.
move=> [|n] G //; rewrite lcnSn commGC commg_subr.
by case/andP: (lcn_normal n.+1 G).
Qed.

Lemma lcn_normalS : forall n G, 'L_n.+1(G) <| 'L_n(G).
Proof.
by move=> G n; apply: normalS (lcn_normal _ _); rewrite (lcn_subS, lcn_sub).
Qed.

Lemma lcn_central : forall n G,
  'L_n(G) / 'L_n.+1(G) \subset 'Z(G / 'L_n.+1(G)).
Proof.
case=> [|n] G; first by rewrite trivg_quotient sub1G.
by rewrite subsetI quotientS ?lcn_sub ?quotient_cents2r.
Qed.

Lemma lcn_sub_leq : forall m n G, n <= m -> 'L_m(G) \subset 'L_n(G).
Proof.
move=> m n G; move/subnK <-; elim: {m}(m - n) => // m.
exact: subset_trans (lcn_subS _ _).
Qed.

Lemma lcnS : forall n A B, A \subset B -> 'L_n(A) \subset 'L_n(B).
Proof.
by case=> // n A B sAB; elim: n => // n IHn; rewrite !lcnSn genS ?imset2S.
Qed.

Lemma lcn_cprod : forall n A B G, A \* B = G -> 'L_n(A) \* 'L_n(B) = 'L_n(G).
Proof.
move=> [|n] // A B G; case/cprodP=> [[H K -> ->{A B}] defG cHK].
have sL := subset_trans (lcn_sub _ _); rewrite cprodE ?(centSS _ _ cHK) ?sL //.
symmetry; elim: n => // n; rewrite lcnSn => ->; rewrite commMG /=; last first.
  by apply: subset_trans (commg_normr _ _); rewrite sL // -defG mulG_subr.
rewrite -!(commGC G) -defG -{1}(centC cHK).
rewrite !commMG ?normsR ?lcn_norm ?cents_norm // 1?centsC //.
by rewrite -!(commGC 'L__(_)) -!lcnSn !(commG1P _) ?mul1g ?sL // centsC.
Qed.

Lemma der_cprod : forall n A B G, A \* B = G -> A^`(n) \* B^`(n) = G^`(n).
Proof.
by move=> n A B G defG; elim: n => {defG}// n; apply: (lcn_cprod 2).
Qed.

Lemma nilpotent_class : forall G, nilpotent G = (nil_class G < #|G|).
Proof.
move=> G; rewrite /nil_class; set s := mkseq _ _.
transitivity (1 \in s); last by rewrite -index_mem size_mkseq.
apply/idP/mapP=> {s}/= [nilG | [n _ Ln1]]; last first.
  apply/forallP=> H; rewrite subsetI; apply/implyP; case/andP=> sHG sHR.
  rewrite -subG1 {}Ln1; elim: n => // n IHn.
  by rewrite (subset_trans sHR) ?commSg.
pose m := #|G|.-1; exists m; first by rewrite mem_iota /= prednK.
rewrite ['L__(G)]card_le1_trivg //= -(subnn m).
elim: {-2}m => [|n]; [by rewrite subn0 prednK | rewrite lcnSn -predn_sub].
case: (eqsVneq 'L_n.+1(G) 1) => [-> | ntLn]; first by rewrite comm1G cards1.
case: (m - n) => [|m' /= IHn]; first by rewrite leqNgt cardG_gt1 ntLn.
rewrite -ltnS (leq_trans (proper_card _) IHn) //.
by rewrite (nil_comm_properl nilG) ?lcn_sub // subsetI subxx lcn_norm.
Qed.

Lemma lcn_nil_classP : forall n G,
  nilpotent G -> reflect ('L_n.+1(G) = 1) (nil_class G <= n).
Proof.
move=> n G; rewrite nilpotent_class /nil_class; set s := mkseq _ _.
set c := index 1 s => lt_c_G; case: leqP => [le_c_n | lt_n_c].
  have Lc1: nth 1 s c = 1 by rewrite nth_index // -index_mem size_mkseq.
  by left; apply/trivgP; rewrite -Lc1 nth_mkseq ?lcn_sub_leq.
right; apply/eqP; apply/negPf; rewrite -(before_find 1 lt_n_c) nth_mkseq //.
exact: ltn_trans lt_n_c lt_c_G.
Qed.

Lemma lcnP : forall G, reflect (exists n, 'L_n.+1(G) = 1) (nilpotent G).
Proof.
move=> G; apply: (iffP idP) => [nilG | [n Ln1]].
  by exists (nil_class G); exact/lcn_nil_classP.
apply/forallP=> H; apply/implyP; rewrite subsetI; case/andP=> sHG sHR.
rewrite -subG1 -{}Ln1; elim: n => // n IHn.
by rewrite (subset_trans sHR) ?commSg.
Qed.

Lemma abelian_nil : forall G, abelian G -> nilpotent G.
Proof. move=> G abG; apply/lcnP; exists 1%N; exact/commG1P. Qed.

Lemma nil_class0 : forall G, (nil_class G == 0) = (G :==: 1).
Proof.
move=> G; apply/idP/eqP=> [nilG | ->].
  by apply/(lcn_nil_classP 0); rewrite ?nilpotent_class (eqP nilG) ?cardG_gt0.
by rewrite -leqn0; apply/(lcn_nil_classP 0); rewrite ?nilpotent1.
Qed.

Lemma nil_class1 : forall G, (nil_class G <= 1) = abelian G.
Proof.
move=> G; case: (eqsVneq G 1) => [-> | ntG].
  by rewrite abelian1 leq_eqVlt ltnS leqn0 nil_class0 eqxx orbT.
apply/idP/idP=> cGG.
  apply/commG1P; apply/(lcn_nil_classP 1); rewrite // nilpotent_class.
  by rewrite (leq_ltn_trans cGG) // cardG_gt1.
by apply/(lcn_nil_classP 1); rewrite ?abelian_nil //; apply/commG1P.
Qed.

Lemma cprod_nil : forall A B G,
  A \* B = G -> nilpotent (G) = nilpotent A && nilpotent B.
Proof.
move=> A B G defG; case/cprodP: defG (defG) => [[H K -> ->{A B}] defG _] defGc.
apply/idP/andP=> [nilG | []].
  by rewrite !(nilpotentS _ nilG) // -defG (mulG_subr, mulG_subl).
case/lcnP=> m LmH1; case/lcnP=> n LnK1; apply/lcnP; exists (m + n.+1).
apply/trivgP; case/cprodP: (lcn_cprod (m.+1 + n.+1) defGc) => _ <- _.
by rewrite mulG_subG /= -{1}LmH1 -LnK1 !lcn_sub_leq ?leq_addl ?leq_addr.
Qed.

Lemma mulg_nil : forall G H,
  H \subset 'C(G) -> nilpotent (G * H) = nilpotent G && nilpotent H.
Proof.
by move=> G H cGH; rewrite -(cprod_nil (cprodEY cGH)) /= cent_joinEr.
Qed.

Lemma dprod_nil : forall A B G,
   A \x B = G -> nilpotent G = nilpotent A && nilpotent B.
Proof.
by move=> A B G; case/dprodP=> [[H K -> ->] <- cHK _]; rewrite mulg_nil.
Qed.

Lemma bigdprod_nil : forall I r (P : pred I) (A_ : I -> {set gT}) G,
  \big[dprod/1]_(i <- r | P i) A_ i = G
  -> (forall i, P i -> nilpotent (A_ i)) -> nilpotent G.
Proof.
move=> I r P A_ G defG nilA; rewrite -defG; move: G defG.
apply big_prop => [| A B IHA IHB G defG | i Pi]; rewrite ?nilpotent1 ?nilA //.
rewrite defG (dprod_nil defG).
by case/dprodP: defG => [[H K]]; move/IHA->; move/IHB.
Qed.

End LowerCentral.

Notation "''L_' n ( G )" := (lower_central_at_group n G) : subgroup_scope.

Lemma lcn_cont : forall n, GFunctor.continuous (lower_central_at n).
Proof.
case=> //; elim=> // n IHn g0T h0T H phi.
by rewrite !lcnSn morphimR ?lcn_sub // commSg ?IHn.
Qed.

Canonical Structure lcn_igFun n := [igFun by lcn_sub^~ n & lcn_cont n].
Canonical Structure lcn_gFun n := [gFun by lcn_cont n].
Canonical Structure lcn_mgFun n := [mgFun by fun _ G H => @lcnS _ n G H].

Section UpperCentralFunctor.

Variable n : nat.
Implicit Type gT : finGroupType.

Lemma ucn_pmap : exists hZ : GFunctor.pmap, @upper_central_at n = hZ.
Proof.
elim: n => [|n' [hZ defZ]]; first by exists trivGfun_pgFun.
by exists [pgFun of center %% hZ]; rewrite /= -defZ.
Qed.

(* Now extract all the intermediate facts of the last proof. *)

Lemma ucn_group_set : forall gT (G : {group gT}), group_set 'Z_n(G).
Proof. by case: ucn_pmap => hZ -> gT G; exact: groupP. Qed.

Canonical Structure upper_central_at_group gT G := Group (@ucn_group_set gT G).

Lemma ucn_sub : forall gT (G : {group gT}), 'Z_n(G) \subset G.
Proof. by case: ucn_pmap => hZ ->; exact: gFsub. Qed.

Lemma morphim_ucn : GFunctor.pcontinuous (upper_central_at n).
Proof. by case: ucn_pmap => hZ ->; exact: pmorphimF. Qed.

Canonical Structure ucn_igFun := [igFun by ucn_sub & morphim_ucn].
Canonical Structure ucn_gFun := [gFun by morphim_ucn].
Canonical Structure ucn_pgFun := [pgFun by morphim_ucn].

Variable (gT : finGroupType) (G : {group gT}).

Lemma ucn_char : 'Z_n(G) \char G. Proof. exact: gFchar. Qed.
Lemma ucn_norm : G \subset 'N('Z_n(G)). Proof. exact: gFnorm. Qed.
Lemma ucn_normal : 'Z_n(G) <| G. Proof. exact: gFnormal. Qed.

End UpperCentralFunctor.

Notation "''Z_' n ( G )" := (upper_central_at_group n G) : subgroup_scope.

Section UpperCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma ucn0 : forall A, 'Z_0(A) = 1.
Proof. by []. Qed.

Lemma ucnSn : forall n A, 'Z_n.+1(A) = coset 'Z_n(A) @*^-1 'Z(A / 'Z_n(A)).
Proof. by []. Qed.

Lemma ucnE : forall n A, 'Z_n(A) = upper_central_at_rec n A.
Proof. by []. Qed.

Lemma ucn_subS : forall n G, 'Z_n(G) \subset 'Z_n.+1(G).
Proof. by move=> n G; rewrite -{1}['Z_n(G)]ker_coset morphpreS ?sub1G. Qed.

Lemma ucn_sub_geq : forall m n G, n >= m -> 'Z_m(G) \subset 'Z_n(G).
Proof.
move=> m n G; move/subnK <-; elim: {n}(n - m) => // n IHn.
exact: subset_trans (ucn_subS _ _).
Qed.

Lemma ucn_central : forall n G, 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)).
Proof. by move=> n G; rewrite ucnSn cosetpreK. Qed.

Lemma ucn_normalS : forall n G, 'Z_n(G) <| 'Z_n.+1(G).
Proof.
by move=> n G; rewrite (normalS _ _ (ucn_normal n G)) ?ucn_subS ?ucn_sub.
Qed.

Lemma ucn_comm : forall n G, [~: 'Z_n.+1(G), G] \subset 'Z_n(G).
Proof.
move=> G n; rewrite -quotient_cents2 ?normal_norm ?ucn_normal ?ucn_normalS //.
by rewrite ucn_central subsetIr.
Qed.

Lemma ucn1 : forall G, 'Z_1(G) = 'Z(G).
Proof.
move=> G; apply: (quotient_inj (normal1 _) (normal1 _)).
by rewrite /= (ucn_central 0) -injmF ?norms1 ?coset1_injm.
Qed.

Lemma ucnSnR : forall n G,
  'Z_n.+1(G) = [set x \in G | [~: [set x], G] \subset 'Z_n(G)].
Proof.
move=> n G; apply/setP=> x; rewrite inE -(setIidPr (ucn_sub n.+1 G)) inE ucnSn.
case Gx: (x \in G) => //=; have nZG := ucn_norm n G.
rewrite -sub1set -sub_quotient_pre -?quotient_cents2 ?sub1set ?(subsetP nZG) //.
by rewrite subsetI quotientS ?sub1set.
Qed.

Lemma ucn_lcnP : forall n G, ('L_n.+1(G) == 1) = ('Z_n(G) == G).
Proof.
move=> n G; rewrite !eqEsubset sub1G ucn_sub /= andbT -(ucn0 G).
elim: {1 3}n 0 (addn0 n) => [j <- //|i IHi j].
rewrite addSnnS; move/IHi=> <- {IHi}; rewrite ucnSn lcnSn.
have nZG := normal_norm (ucn_normal j G).
have nZL := subset_trans (lcn_sub _ _) nZG.
by rewrite -sub_morphim_pre // subsetI morphimS ?lcn_sub // quotient_cents2.
Qed.

Lemma ucnP : forall G, reflect (exists n, 'Z_n(G) = G) (nilpotent G).
Proof.
move=> G; apply: (iffP (lcnP G)) => [] [n]; move/eqP=> clGn;
  by exists n; apply/eqP; rewrite ucn_lcnP in clGn *.
Qed.

Lemma ucn_nil_classP : forall n G,
  nilpotent G -> reflect ('Z_n(G) = G) (nil_class G <= n).
Proof.
move=> n G nilG; rewrite (sameP (lcn_nil_classP n nilG) eqP) ucn_lcnP.
exact: eqP.
Qed.

Lemma ucn_id : forall n G, 'Z_n('Z_n(G)) = 'Z_n(G).
Proof. by move=> n G; rewrite -{2}['Z_n(G)]gFid. Qed.

Lemma ucn_nilpotent : forall n G, nilpotent 'Z_n(G). 
Proof. by move=> n G; apply/ucnP; exists n; rewrite ucn_id. Qed.

Lemma nil_class_ucn : forall n G, nil_class 'Z_n(G) <= n.
Proof. by move=> n G; apply/ucn_nil_classP; rewrite ?ucn_nilpotent ?ucn_id. Qed.

End UpperCentral.

Section MorphNil.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type G : {group aT}.

Lemma morphim_lcn : forall n G, G \subset D -> f @* 'L_n(G) = 'L_n(f @* G).
Proof.
case=> // n G sHG; elim: n => // n IHn.
by rewrite !lcnSn -IHn morphimR // (subset_trans _ sHG) // lcn_sub.
Qed.

Lemma injm_ucn : forall n G,
  'injm f -> G \subset D -> f @* 'Z_n(G) = 'Z_n(f @* G).
Proof. move=> n G; exact: injmF. Qed.

Lemma morphim_nil : forall G, nilpotent G -> nilpotent (f @* G).
Proof.
move=> G; case/ucnP=> n ZnG; apply/ucnP; exists n.
by apply/eqP; rewrite eqEsubset ucn_sub /= -{1}ZnG morphim_ucn.
Qed.

Lemma injm_nil : forall G,
  'injm f -> G \subset D -> nilpotent (f @* G) = nilpotent G.
Proof.
move=> G injf sGD; apply/idP/idP; last exact: morphim_nil.
case/ucnP=> n; rewrite -injm_ucn //; move/injm_morphim_inj=> // defZ.
by apply/ucnP; exists n; rewrite defZ ?(subset_trans (ucn_sub n G)).
Qed.

Lemma nil_class_morphim : forall G,
  nilpotent G -> nil_class (f @* G) <= nil_class G.
Proof.
move=> G nilG; rewrite (sameP (ucn_nil_classP _ (morphim_nil nilG)) eqP) /=.
by rewrite eqEsubset ucn_sub -{1}(ucn_nil_classP _ nilG (leqnn _)) morphim_ucn.
Qed.

Lemma nil_class_injm : forall G,
  'injm f -> G \subset D -> nil_class (f @* G) = nil_class G.
Proof.
move=> G injf sGD; case nilG: (nilpotent G).
  apply/eqP; rewrite eqn_leq nil_class_morphim //.
  rewrite (sameP (lcn_nil_classP _ nilG) eqP) -subG1.
  rewrite -(injmSK injf) ?(subset_trans (lcn_sub _ _)) // morphim1.
  by rewrite morphim_lcn // (lcn_nil_classP _ _ (leqnn _)) //= injm_nil.
transitivity #|G|; apply/eqP; rewrite eqn_leq.
  rewrite -(card_injm injf sGD) (leq_trans (index_size _ _)) ?size_mkseq //.
  by rewrite leqNgt -nilpotent_class injm_nil ?nilG.
rewrite (leq_trans (index_size _ _)) ?size_mkseq // leqNgt -nilpotent_class.
by rewrite nilG.
Qed.

End MorphNil.

Section QuotientNil.

Variables gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma quotient_ucn_add : forall m n G,
  'Z_(m + n)(G) / 'Z_n(G) = 'Z_m(G / 'Z_n(G)).
Proof.
move=> m n G; elim: m => [|m IHm]; first exact: trivg_quotient.
apply/setP=> Zx; have [x Nx ->{Zx}] := cosetP Zx.
have [sZG nZG] := andP (ucn_normal n G).
rewrite (ucnSnR m) inE -!sub1set -morphim_set1 //= -quotientR ?sub1set // -IHm.
rewrite !quotientSGK ?(ucn_sub_geq, leq_addl, comm_subG _ nZG, sub1set) //=.
by rewrite addSn /= ucnSnR inE.
Qed.

Lemma isog_nil : forall (rT : finGroupType) G (L : {group rT}),
  G \isog L -> nilpotent G = nilpotent L.
Proof. by move=> rT G L; case/isogP=> f injf <-; rewrite injm_nil. Qed.

Lemma isog_nil_class : forall (rT : finGroupType) G (L : {group rT}),
  G \isog L -> nil_class G = nil_class L.
Proof. by move=> rT G L; case/isogP=> f injf <-; rewrite nil_class_injm. Qed.

Lemma quotient_nil : forall G H, nilpotent G -> nilpotent (G / H).
Proof. move=> G H; exact: morphim_nil. Qed.
  
Lemma quotient_center_nil : forall G, nilpotent (G / 'Z(G)) = nilpotent G.
Proof.
move=> G; rewrite -ucn1; apply/idP/idP; last exact: quotient_nil.
case/ucnP=> c nilGq; apply/ucnP; exists c.+1; have nsZ1G := ucn_normal 1 G.
apply: (quotient_inj _ nsZ1G); last by rewrite /= -(addn1 c) quotient_ucn_add.
by rewrite (normalS _ _ nsZ1G) ?ucn_sub ?ucn_sub_geq.
Qed.

Lemma nil_class_quotient_center : forall G,
  nilpotent (G) -> nil_class (G / 'Z(G)) = (nil_class G).-1.
Proof.
move=> G nilG; have nsZ1G := ucn_normal 1 G.
apply/eqP; rewrite -ucn1 eqn_leq; apply/andP; split.
  apply/ucn_nil_classP; rewrite ?quotient_nil //= -quotient_ucn_add ucn1.
  by rewrite (ucn_nil_classP _ _ _) ?addn1 ?leqSpred.
rewrite -subn1 leq_sub_add addnC; apply/ucn_nil_classP => //=.
apply: (quotient_inj _ nsZ1G) => /=.
  by apply: normalS (ucn_sub _ _) nsZ1G; rewrite /= addnS ucn_sub_geq.
by rewrite quotient_ucn_add; apply/ucn_nil_classP; rewrite //= quotient_nil.
Qed.

Lemma nilpotent_sub_norm : forall G H,
  nilpotent G -> H \subset G -> 'N_G(H) \subset H -> G :=: H.
Proof.
move=> G H nilG sHG sNH; apply/eqP; rewrite eqEsubset sHG andbT.
apply/negP=> nsGH.
have{nsGH} [i sZH []]: exists2 i, 'Z_i(G) \subset H & ~ 'Z_i.+1(G) \subset H.
  case/ucnP: nilG => n ZnG; rewrite -{}ZnG in nsGH.
  elim: n => [|i IHi] in nsGH *; first by rewrite sub1G in nsGH.
  by case sZH: ('Z_i(G) \subset H); [exists i | apply: IHi; rewrite sZH].
apply: subset_trans sNH; rewrite subsetI ucn_sub -commg_subr.
apply: subset_trans sZH; apply: subset_trans (ucn_comm i G); exact: commgS.
Qed.

Lemma nilpotent_proper_norm : forall G H,
  nilpotent G -> H \proper G -> H \proper 'N_G(H).
Proof.
move=> G H nilG; rewrite properEneq properE subsetI normG; case/andP=> neHG sHG.
by rewrite sHG; apply: contra neHG; move/(nilpotent_sub_norm nilG)->.
Qed.

Lemma nilpotent_subnormal : forall G H,
  nilpotent G -> H \subset G -> H <|<| G.
Proof.
move=> G H nilG; elim: {H}_.+1 {-2}H (ltnSn (#|G| - #|H|)) => // m IHm H.
rewrite ltnS => leGHm sHG; have:= sHG; rewrite subEproper.
case/predU1P=> [->|]; first exact: subnormal_refl.
move/(nilpotent_proper_norm nilG); set K := 'N_G(H) => prHK.
have snHK: H <|<| K by rewrite normal_subnormal ?normalSG.
have sKG: K \subset G by rewrite subsetIl.
apply: subnormal_trans snHK (IHm _ (leq_trans _ leGHm) sKG).
by rewrite ltn_sub2l ?proper_card ?(proper_sub_trans prHK).
Qed.

Lemma TI_center_nil : forall G H,
  nilpotent G -> H <| G -> H :&: 'Z(G) = 1 -> H :=: 1.
Proof.
move=> G H nilG; case/andP=> sHG nHG trHZ.
rewrite -{1}(setIidPl sHG); case/ucnP: nilG => n <-.
elim: n => [|n IHn]; apply/trivgP; rewrite ?subsetIr // -trHZ.
rewrite [H :&: 'Z(G)]setIA subsetI setIS ?ucn_sub //= (sameP commG1P trivgP).
rewrite -commg_subr commGC in nHG.
rewrite -IHn subsetI (subset_trans _ nHG) ?commSg ?subsetIl //=.
by rewrite (subset_trans _ (ucn_comm n G)) ?commSg ?subsetIr.
Qed.

Lemma meet_center_nil : forall G H,
  nilpotent G -> H <| G -> H :!=: 1 -> H :&: 'Z(G) != 1.
Proof. by move=> G H nilG nsHG; apply: contraNneq; move/TI_center_nil->. Qed.

Lemma center_nil_eq1 : forall G, nilpotent G -> ('Z(G) == 1) = (G :==: 1).
Proof.
move=> G nilG; apply/eqP/eqP=> [Z1 | ->]; last exact: center1.
by rewrite (TI_center_nil nilG) // (setIidPr (center_sub G)).
Qed.

End QuotientNil.

Section Solvable.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma nilpotent_sol : forall G, nilpotent G -> solvable G.
Proof.
move=> G nilG; apply/forallP=> H; rewrite subsetI.
apply/implyP; case/andP=> sHG sHH'; apply: (implyP (forallP nilG H)).
by rewrite subsetI sHG (subset_trans sHH') ?commgS.
Qed.

Lemma abelian_sol : forall G, abelian G -> solvable G.
Proof. move=> G; move/abelian_nil; exact: nilpotent_sol. Qed.

Lemma solvable1 : solvable [1 gT]. Proof. exact: abelian_sol (abelian1 gT). Qed.

Lemma solvableS : forall G H, H \subset G -> solvable G -> solvable H.
Proof.
move=> G H sHG solG; apply/forallP=> K; rewrite subsetI.
apply/implyP; case/andP=> sKH sKK'; apply: (implyP (forallP solG K)).
by rewrite subsetI (subset_trans sKH).
Qed.

Lemma sol_der1_proper : forall G H,
  solvable G -> H \subset G -> H :!=: 1 -> H^`(1) \proper H.
Proof.
move=> G H solG sHG ntH; rewrite properE comm_subG //; apply: implyP ntH.
by have:= forallP solG H; rewrite subsetI sHG implybNN. 
Qed.

Lemma derivedP : forall G, reflect (exists n, G^`(n) = 1) (solvable G).
Proof.
move=> G; apply: (iffP idP) => [solG | [n solGn]]; last first.
  apply/forallP=> H; rewrite subsetI; apply/implyP; case/andP=> sHG sH'H.
  rewrite -subG1 -{}solGn; elim: n => // n IHn.
  exact: subset_trans sH'H (commgSS _ _).
suffices IHn: forall n, #|G^`(n)| <= (#|G|.-1 - n).+1.
  by exists #|G|.-1; rewrite [G^`(_)]card_le1_trivg ?(leq_trans (IHn _)) ?subnn.
elim=> [|n IHn]; [by rewrite subn0 prednK | rewrite dergSn -predn_sub -ltnS].
case: (eqVneq G^`(n) 1) => [-> | ntGn]; first by rewrite commG1 cards1.
case: (_ - _) IHn => [|n']; first by rewrite leqNgt cardG_gt1 ntGn.
by apply: leq_trans (proper_card _); exact: sol_der1_proper (der_sub _ _) _.
Qed.

End Solvable.

Section MorphSol.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variable G : {group gT}.

Lemma morphim_sol : solvable G -> solvable (f @* G).
Proof.
move/(solvableS (subsetIr D G)); case/derivedP=> n Gn1; apply/derivedP.
by exists n; rewrite /= -morphimIdom -morphim_der ?subsetIl // Gn1 morphim1.
Qed.

Lemma injm_sol : 'injm f -> G \subset D -> solvable (f @* G) = solvable G.
Proof.
move=> injf sGD; apply/idP/idP; last exact: morphim_sol.
case/derivedP=> n Gn1; apply/derivedP; exists n; apply/trivgP.
rewrite -(injmSK injf) ?(subset_trans (der_sub _ _)) ?morphim_der //.
by rewrite Gn1 morphim1.
Qed.

End MorphSol.

Section QuotientSol.

Variables gT rT : finGroupType.
Implicit Types G H K : {group gT}.

Lemma isog_sol : forall G (L : {group rT}),
  G \isog L -> solvable G = solvable L.
Proof. by move=> G L; case/isogP=> f injf <-; rewrite injm_sol. Qed.

Lemma quotient_sol : forall G H, solvable G -> solvable (G / H).
Proof. move=> G H; exact: morphim_sol. Qed.

Lemma series_sol : forall G H,
  H <| G -> solvable G = solvable H && solvable (G / H).
Proof.
move=> G H; case/andP=> sHG nHG; apply/idP/andP=> [solG | [solH solGH]].
  by rewrite quotient_sol // (solvableS sHG).
apply/forallP=> K; rewrite subsetI; apply/implyP; case/andP=> sKG sK'K.
suffices sKH: K \subset H.
  by apply: (implyP (forallP solH K)); rewrite subsetI sKH.
have nHK := subset_trans sKG nHG.
rewrite -quotient_sub1 // subG1 (implyP (forallP solGH _)) //.
by rewrite subsetI -morphimR ?morphimS.
Qed.

End QuotientSol.

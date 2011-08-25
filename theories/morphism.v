(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finfun finset.
Require Import fingroup.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*                                                                            *)
(*   {morphism D >-> rT} ==                                                   *)
(*     the structure type of functions that are group morphisms mapping a     *)
(*     domain set D : {set aT} to a type rT; rT must have a finGroupType      *)
(*     structure, and D is usually a group (most of the theory expects this). *)
(*            mfun == the coercion projecting {morphism D >-> rT} to aT -> rT *)
(*                                                                            *)
(* Basic examples:                                                            *)
(*            idm D == the identity morphism with domain D, or more precisely *)
(*                     the identity function, but with a canonical            *)
(*                     {morphism G -> gT} structure.                          *)
(*          trivm D == the trivial morphism with domain D                     *)
(* If f has a {morphism D >-> rT} structure                                   *)
(*           'dom f == D                                                      *)
(*           f @* A == the image of A by f, where f is defined                *)
(*                  := f @: (D :&: A)                                         *)
(*        f @*^-1 R == the pre-image of R by f, where f is defined            *)
(*                  :=  D :&: f @^-1: R                                       *)
(*           'ker f == the kernel of f                                        *)
(*                  :=  f @^-1: 1                                             *)
(*         'ker_G f == the kernel of f restricted to G                        *)
(*                  :=  G :&: 'ker f (this is a pure notation)                *)
(*          'injm f <=> f injective on D                                      *)
(*                  <-> ker f \subset 1 (this is a pure notation)             *)
(*        invm injf == the inverse morphism of f, with domain f @* D, when f  *)
(*                     is injective (injf : 'injm f)                          *)
(*    restrm f sDom == the restriction of f to a subset A of D, given         *)
(*                     (sDom : A \subset D); restrm f sDom is transparently   *)
(*                     identical to f; the restrmP and domP lemmas provide    *)
(*                     opaque restrictions.                                   *)
(*     invm f infj  == the inverse morphism for an injective f, with domain   *)
(*                     f @* D, given (injf : 'injm f)                         *)
(*                                                                            *)
(*      G \isog H  <=> G and H are isomorphic as groups                       *)
(*       H \homg G <=> H is a homomorphic image of G                          *)
(*      isom G H f <=> f maps G isomorphically to H, provided D contains G    *)
(*                 <-> f @: G^# == H^#                                        *)
(*                                                                            *)
(* If, moreover, g : {morphism G >-> gT} with G : {group aT},                 *)
(*  factm sKer sDom == the (natural) factor morphism mapping f @* G to g @* G *)
(*                     given sDom : G \subset D, sKer : 'ker f \subset 'ker g *)
(*    ifactm injf g == the (natural) factor morphism mapping f @* G to g @* G *)
(*                     when f is injective (injf : 'injm f); here g must      *)
(*                     be an actual morphism structure, not its function      *)
(*                     projection.                                            *)
(*                                                                            *)
(* If g has a {morphism G >-> aT} structure for any G : {group gT}, then      *)
(*           f \o g has a canonical {morphism g @*^-1 D >-> rT} structure     *)
(*                                                                            *)
(* Finally, for an arbitrary function f : aT -> rT                            *)
(*     morphic D f <=> f preserves group multiplication in D, i.e.,           *)
(*                     f (x * y) = (f x) * (f y) for all x, y in D            *)
(*        morphm fM == a function identical to f, but with a canonical        *)
(*                     {morphism D >-> rT} structure, given fM : morphic D f  *)
(*      misom D C f <=> f maps D isomorphically to C                          *)
(*                  := morphic D f && isom D C f                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Reserved Notation "x \isog y" (at level 70).

Section MorphismStructure.

Variables aT rT : finGroupType.

Structure morphism (D : {set aT}) : Type := Morphism {
  mfun :> aT -> FinGroup.sort rT;
  _ : {in D &, {morph mfun : x y / x * y}}
}.

(* We give the most 'lightweight' possible specification to define morphisms:*)
(* local congruence with the group law of aT. We then provide the properties *)
(* for the 'textbook' notion of morphism, when the required structures are   *)
(* available (e.g. its domain is a group).                                   *)

Definition morphism_for D of phant rT := morphism D.

Definition clone_morphism D f :=
  let: Morphism _ fM := f
    return {type of @Morphism D for f} -> morphism_for D (Phant rT)
  in fun k => k fM.

Variables (D A : {set aT}) (R : {set rT}) (x : aT) (y : rT) (f : aT -> rT).

CoInductive morphim_spec : Prop := MorphimSpec z & z \in D & z \in A & y = f z.

Lemma morphimP : reflect morphim_spec (y \in f @: (D :&: A)).
Proof.
apply: (iffP imsetP) => [] [z]; first by case/setIP; exists z.
by exists z; first apply/setIP.
Qed.

Lemma morphpreP : reflect (x \in D /\ f x \in R) (x \in D :&: f @^-1: R).
Proof. rewrite !inE; exact: andP. Qed.

End MorphismStructure.

Notation "{ 'morphism' D >-> T }" := (morphism_for D (Phant T))
  (at level 0, format "{ 'morphism'  D  >->  T }") : group_scope.
Notation "[ 'morphism' D 'of' f ]" :=
     (@clone_morphism _ _ D _ (fun fM => @Morphism _ _ D f fM))
   (at level 0, format "[ 'morphism'  D  'of'  f ]") : form_scope.
Notation "[ 'morphism' 'of' f ]" := (clone_morphism (@Morphism _ _ _ f))
   (at level 0, format "[ 'morphism'  'of'  f ]") : form_scope.

Implicit Arguments morphimP [aT rT D A f y].
Implicit Arguments morphpreP [aT rT D R f x].
Prenex Implicits morphimP morphpreP.

(* domain, image, preimage, kernel, using phantom types to infer the domain *)

Section MorphismOps1.

Variables (aT rT : finGroupType) (D : {set aT}) (f : {morphism D >-> rT}).

Lemma morphM : {in D &, {morph f : x y / x * y}}.
Proof. by case f. Qed.

Notation morPhantom := (phantom (aT -> rT)).
Definition MorPhantom := Phantom (aT -> rT).

Definition dom of morPhantom f := D.

Definition morphim of morPhantom f := fun A => f @: (D :&: A).

Definition morphpre of morPhantom f := fun R : {set rT} => D :&: f @^-1: R.

Definition ker mph := morphpre mph 1.

End MorphismOps1.

Notation "''dom' f" := (dom (MorPhantom f))
  (at level 10, f at level 8, format "''dom'  f") : group_scope.

Notation "''ker' f" := (ker (MorPhantom f))
  (at level 10, f at level 8, format "''ker'  f") : group_scope.

Notation "''ker_' H f" := (H :&: 'ker f)
  (at level 10, H at level 2, f at level 8, format "''ker_' H  f")
  : group_scope.

Notation "f @* A" := (morphim (MorPhantom f) A)
  (at level 24, format "f  @*  A") : group_scope.

Notation "f @*^-1 R" := (morphpre (MorPhantom f) R)
  (at level 24, format "f  @*^-1  R") : group_scope.

Notation "''injm' f" := (pred_of_set ('ker f) \subset pred_of_set 1)
  (at level 10, f at level 8, format "''injm'  f") : group_scope.

Section MorphismTheory.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Types R S : {set rT}.
Implicit Types M : {group rT}.

(* Most properties of morphims hold only when the domain is a group. *)
Variables (D : {group aT}) (f : {morphism D >-> rT}).

Lemma morph1 : f 1 = 1.
Proof. by apply: (mulgI (f 1)); rewrite -morphM ?mulg1. Qed.

Lemma morphV : {in D, {morph f : x / x^-1}}.
Proof.
move=> x Dx; apply: (mulgI (f x)).
by rewrite -morphM ?groupV // !mulgV morph1.
Qed.

Lemma morphJ : {in D &, {morph f : x y / x ^ y}}.
Proof. by move=> * /=; rewrite !morphM ?morphV // ?groupM ?groupV. Qed.

Lemma morphX : forall n, {in D, {morph f : x / x ^+ n}}.
Proof.
by elim=> [|n IHn] x Dx; rewrite ?morph1 // !expgS morphM ?(groupX, IHn).
Qed.

Lemma morphR : {in D &, {morph f : x y / [~ x, y]}}.
Proof. by move=> * /=; rewrite morphM ?(groupV, groupJ) // morphJ ?morphV. Qed.

(* morphic image,preimage properties w.r.t. set-theoretic operations *)

Lemma morphimE : forall A, f @* A = f @: (D :&: A). Proof. by []. Qed.
Lemma morphpreE : forall R, f @*^-1 R = D :&: f @^-1: R. Proof. by []. Qed.
Lemma kerE : 'ker f = f @*^-1 1. Proof. by []. Qed.

Lemma morphimEsub : forall A, A \subset D -> f @* A = f @: A.
Proof. by move=> A sAD; rewrite /morphim (setIidPr sAD). Qed.

Lemma morphimEdom : f @* D = f @: D.
Proof. exact: morphimEsub. Qed.

Lemma morphimIdom : forall A, f @* (D :&: A) = f @* A.
Proof. by move=> A; rewrite /morphim setIA setIid. Qed.

Lemma morphpreIdom : forall R, D :&: f @*^-1 R = f @*^-1 R.
Proof. by move=> A; rewrite /morphim setIA setIid. Qed.

Lemma morphpreIim : forall R, f @*^-1 (f @* D :&: R) = f @*^-1 R.
Proof.
move=> R; apply/setP=> x; rewrite morphimEdom !inE.
by case Dx: (x \in D); rewrite // mem_imset.
Qed.

Lemma morphimIim : forall A, f @* D :&: f @* A = f @* A.
Proof. by move=> A; apply/setIidPr; rewrite imsetS // setIid subsetIl. Qed.

Lemma mem_morphim : forall A x, x \in D -> x \in A -> f x \in f @* A.
Proof. by move=> A x Dx Ax; apply/morphimP; exists x. Qed.

Lemma mem_morphpre : forall R x, x \in D -> f x \in R -> x \in f @*^-1 R.
Proof. by move=> R x Dx Rfx; exact/morphpreP. Qed.

Lemma morphimS : forall A B, A \subset B -> f @* A \subset f @* B.
Proof. by move=> A B sAB; rewrite imsetS ?setIS. Qed.

Lemma morphim_sub : forall A, f @* A \subset f @* D.
Proof. by move=> A; rewrite imsetS // setIid subsetIl. Qed.

Lemma leq_morphim : forall A, #|f @* A| <= #|A|.
Proof.
move=> A; apply: (leq_trans (leq_imset_card _ _)).
by rewrite subset_leq_card ?subsetIr.
Qed.

Lemma morphpreS : forall R S, R \subset S -> f @*^-1 R \subset f @*^-1 S.
Proof. by move=> R S sRS; rewrite setIS ?preimsetS. Qed.

Lemma morphim_setIpre : forall A R, f @* (A :&: f @*^-1 R) = f @* A :&: R.
Proof.
move=> A R; apply/setP=> fa; apply/morphimP/setIP=> [[a Da] | []].
  by rewrite !inE Da /=; case/andP=> Aa Rfa ->; rewrite mem_morphim.
by case/morphimP=> a Da Aa -> Rfa; exists a; rewrite // !inE Aa Da.
Qed.

Lemma morphim0 : f @* set0 = set0.
Proof. by rewrite morphimE setI0 imset0. Qed.

Lemma morphim_set1 : forall x, x \in D -> f @* [set x] = [set f x].
Proof.
move=> x; rewrite /morphim -sub1set; move/setIidPr->; exact: imset_set1.
Qed.

Lemma morphim1 : f @* 1 = 1.
Proof. by rewrite morphim_set1 ?morph1. Qed.

Lemma morphimV : forall A, f @* A^-1 = (f @* A)^-1.
Proof.
have subV: forall A, f @* A^-1 \subset (f @* A)^-1.
  move=> A; apply/subsetP=> y; case/morphimP=> x Dx; rewrite !inE => Ax' ->{y}.
  by rewrite -morphV // mem_imset // inE groupV Dx.
by move=> A; apply/eqP; rewrite eqEsubset subV -invSg invgK -{1}(invgK A) subV.
Qed.

Lemma morphpreV : forall R, f @*^-1 R^-1 = (f @*^-1 R)^-1.
Proof.
move=> R; apply/setP=> x; rewrite !inE groupV; case Dx: (x \in D) => //=.
by rewrite morphV.
Qed.

Lemma morphimMl : forall A B, A \subset D -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> A B sAD; rewrite /morphim setIC -group_modl // (setIidPr sAD).
apply/setP=> fxy; apply/idP/idP.
  case/imsetP=> xy; case/imset2P=> x y Ax; case/setIP=> Dy By -> -> {fxy xy}.
  by rewrite morphM // (subsetP sAD, mem_imset2) // mem_imset // inE By.
case/imset2P=> fx fy; case/imsetP=> x Ax -> {fx}.
case/morphimP=> y Dy By -> {fy} ->{fxy}.
by rewrite -morphM // (subsetP sAD, mem_imset) // mem_mulg // inE By.
Qed.

Lemma morphimMr : forall A B, B \subset D -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> A B sBD; apply: invg_inj.
by rewrite invMg -!morphimV invMg morphimMl // -invGid invSg.
Qed.

Lemma morphpreMl : forall R S,
  R \subset f @* D -> f @*^-1 (R * S) = f @*^-1 R * f @*^-1 S.
Proof.
move=> R S sRfD; apply/setP=> x; rewrite !inE.
apply/andP/imset2P=> [[Dx] | [y z]]; last first.
  rewrite !inE; case/andP=> Dy Rfy; case/andP=> Dz Rfz ->.
  by rewrite ?(groupM, morphM, mem_imset2).
case/imset2P=> fy fz Rfy Rfz def_fx.
case/morphimP: (subsetP sRfD fy Rfy) => y Dy _ def_fy.
exists y (y^-1 * x); last by rewrite mulKVg.
  by rewrite !inE Dy -def_fy.
by rewrite !inE groupM ?(morphM, morphV, groupV) // def_fx -def_fy mulKg.
Qed.

Lemma morphimJ : forall A x, x \in D -> f @* (A :^ x) = f @* A :^ f x.
Proof.
move=> A x Dx; rewrite !conjsgE morphimMl ?(morphimMr, sub1set, groupV) //.
by rewrite !(morphim_set1, groupV, morphV).
Qed.

Lemma morphpreJ : forall R x, x \in D -> f @*^-1 (R :^ f x) = f @*^-1 R :^ x.
Proof.
move=> R x Dx; apply/setP=> y; rewrite conjIg !inE conjGid // !mem_conjg inE.
by case Dy: (y \in D); rewrite // morphJ ?(morphV, groupV).
Qed.

Lemma morphimU : forall A B, f @* (A :|: B) = f @* A :|: f @* B.
Proof. by move=> A B; rewrite -imsetU -setIUr. Qed.

Lemma morphimI : forall A B, f @* (A :&: B) \subset f @* A :&: f @* B.
Proof. by move=> A B; rewrite subsetI // ?morphimS ?(subsetIl, subsetIr). Qed.

Lemma morphpre0 : f @*^-1 set0 = set0.
Proof. by rewrite morphpreE preimset0 setI0. Qed.

Lemma morphpreT : f @*^-1 setT = D.
Proof. by rewrite morphpreE preimsetT setIT. Qed.

Lemma morphpreU : forall R S, f @*^-1 (R :|: S) = f @*^-1 R :|: f @*^-1 S.
Proof. by move=> R S; rewrite -setIUr -preimsetU. Qed.

Lemma morphpreI : forall R S, f @*^-1 (R :&: S) = f @*^-1 R :&: f @*^-1 S.
Proof. by move=> R S; rewrite -setIIr -preimsetI. Qed.

Lemma morphpreD : forall R S, f @*^-1 (R :\: S) = f @*^-1 R :\: f @*^-1 S.
Proof. by move=> R S; apply/setP=> x; rewrite !inE; case: (x \in D). Qed.

(* kernel, domain properties *)

Lemma kerP : forall x, x \in D -> reflect (f x = 1) (x \in 'ker f).
Proof. move=> x Dx; rewrite 2!inE Dx; exact: set1P. Qed.

Lemma dom_ker : {subset 'ker f <= D}.
Proof. by move=> x; case/morphpreP. Qed.

Lemma mker : forall x, x \in 'ker f -> f x = 1.
Proof. by move=> x Kx; apply/kerP=> //; exact: dom_ker. Qed.

Lemma mkerl : forall x y, x \in 'ker f -> y \in D -> f (x * y) = f y.
Proof. by move=> x y Kx Dy; rewrite morphM // ?(dom_ker, mker Kx, mul1g). Qed.

Lemma mkerr : forall x y, x \in D -> y \in 'ker f -> f (x * y) = f x.
Proof. by move=> x y Dx Ky; rewrite morphM // ?(dom_ker, mker Ky, mulg1). Qed.

Lemma rcoset_kerP : forall x y,
  x \in D -> y \in D -> reflect (f x = f y) (x \in 'ker f :* y).
Proof.
move=> x y Dx Dy; rewrite mem_rcoset !inE groupM ?morphM ?groupV //=.
rewrite morphV // -eq_mulgV1; exact: eqP.
Qed.

Lemma ker_rcoset : forall x y,
  x \in D -> y \in D -> f x = f y -> exists2 z, z \in 'ker f & x = z * y.
Proof. move=> x y Dx Dy eqfxy; apply/rcosetP; exact/rcoset_kerP. Qed.

Lemma ker_norm : D \subset 'N('ker f).
Proof.
apply/subsetP=> x Dx; rewrite inE; apply/subsetP=> yx.
case/imsetP=> y Ky -> {yx}.
by rewrite !inE groupJ ?morphJ // ?dom_ker //= mker ?conj1g.
Qed.

Lemma ker_normal : 'ker f <| D.
Proof. by rewrite /(_ <| D) subsetIl ker_norm. Qed.

Lemma morphimGI : forall G A,
  'ker f \subset G -> f @* (G :&: A) = f @* G :&: f @* A.
Proof.
move=> G A sKG; apply/eqP; rewrite eqEsubset morphimI setIC.
apply/subsetP=> y; case/setIP; case/morphimP=> x Dx Ax ->{y}.
case/morphimP=> z Dz Gz; case/ker_rcoset=> {Dz}// y Ky def_x.
have{z Gz y Ky def_x} Gx: x \in G by rewrite def_x groupMl // (subsetP sKG).
by rewrite mem_imset ?inE // Dx Gx Ax.
Qed.

Lemma morphimIG : forall A G,
  'ker f \subset G -> f @* (A :&: G) = f @* A :&: f @* G.
Proof. by move=> A G sKG; rewrite setIC morphimGI // setIC. Qed.

Lemma morphimD : forall A B, f @* A :\: f @* B \subset f @* (A :\: B).
Proof.
move=> A B; rewrite subDset -morphimU morphimS //.
by rewrite setDE setUIr setUCr setIT subsetUr.
Qed.

Lemma morphimDG : forall A G,
  'ker f \subset G -> f @* (A :\: G) = f @* A :\: f @* G.
Proof.
move=> A G sKG; apply/eqP; rewrite eqEsubset morphimD andbT !setDE subsetI.
rewrite morphimS ?subsetIl // -[~: f @* G]setU0 -subDset setDE setCK.
by rewrite -morphimIG //= setIAC -setIA setICr setI0 morphim0.
Qed.

(* group structure preservation *)

Lemma morphpre_groupset : forall M, group_set (f @*^-1 M).
Proof.
move=> M; apply/group_setP; split=> [|x y]; rewrite !inE ?(morph1, group1) //.
by case/andP=> Dx Mfx; case/andP=> Dy Mfy; rewrite morphM ?groupM.
Qed.

Lemma morphim_groupset : forall G, group_set (f @* G).
Proof.
move=> G; apply/group_setP; split=> [|fx fy].
  by rewrite -morph1 mem_imset ?group1.
case/morphimP=> x Dx Gx ->; case/morphimP=> y Dy Gy ->.
by rewrite -morphM ?mem_imset ?inE ?groupM.
Qed.

Canonical Structure morphpre_group fPh M :=
  @group _ (morphpre fPh M) (morphpre_groupset M).
Canonical Structure morphim_group fPh G :=
  @group _ (morphim fPh G) (morphim_groupset G).
Canonical Structure ker_group fPh : {group aT} :=
  Eval hnf in [group of ker fPh].

Lemma morph_dom_groupset : group_set (f @: D).
Proof. by rewrite -morphimEdom groupP. Qed.

Canonical Structure morph_dom_group := group morph_dom_groupset.

Lemma morphpreMr : forall R S,
  S \subset f @* D -> f @*^-1 (R * S) = f @*^-1 R * f @*^-1 S.
Proof.
move=> R S sSfD; apply: invg_inj.
by rewrite invMg -!morphpreV invMg morphpreMl // -invSg invgK invGid.
Qed.

(* compatibility with inclusion *)

Lemma morphimK : forall A, A \subset D -> f @*^-1 (f @* A) = 'ker f * A.
Proof.
move=> A sAD; apply/setP=> x; rewrite !inE; apply/idP/idP.
  case/andP=> Dx; case/morphimP=> y Dy Ay eqxy.
  rewrite -(mulgKV y x) mem_mulg // !inE !(groupM, morphM, groupV) //.
  by rewrite morphV //= eqxy mulgV.
case/imset2P=> z y Kz Ay ->{x}.
have [Dy Dz]: y \in D /\ z \in D by rewrite (subsetP sAD) // dom_ker.
by rewrite groupM // morphM // mker // mul1g mem_imset // inE Dy.
Qed.

Lemma morphimGK : forall G,
 'ker f \subset G -> G \subset D -> f @*^-1 (f @* G) = G.
Proof. by move=> G sKG sGD; rewrite morphimK // mulSGid. Qed.

Lemma morphpre_set1 : forall x, x \in D -> f @*^-1 [set f x] = 'ker f :* x.
Proof. by move=> x Dx; rewrite -morphim_set1 // morphimK ?sub1set. Qed.

Lemma morphpreK : forall R, R \subset f @* D -> f @* (f @*^-1 R) = R.
Proof.
move=> R sRfD; apply/setP=> y; apply/morphimP/idP=> [[x _] | Ry].
  by rewrite !inE; case/andP=> _ Rfx ->.
case/morphimP: (subsetP sRfD y Ry) => x Dx _ defy.
by exists x; rewrite // !inE Dx -defy.
Qed.

Lemma morphim_ker : f @* 'ker f = 1.
Proof. by rewrite morphpreK ?sub1G. Qed.

Lemma ker_sub_pre : forall M, 'ker f \subset f @*^-1 M.
Proof. by move=> M; rewrite morphpreS ?sub1G. Qed.

Lemma ker_normal_pre : forall M, 'ker f <| f @*^-1 M.
Proof. by move=> M; rewrite /normal ker_sub_pre subIset ?ker_norm. Qed.

Lemma morphpreSK : forall R S,
  R \subset f @* D -> (f @*^-1 R \subset f @*^-1 S) = (R \subset S).
Proof.
move=> R S sRfD; apply/idP/idP=> [sf'RS|]; last exact: morphpreS.
suffices: R \subset f @* D :&: S by rewrite subsetI sRfD.
rewrite -(morphpreK sRfD) -[_ :&: S]morphpreK (morphimS, subsetIl) //.
by rewrite morphpreI morphimGK ?subsetIl // setIA setIid.
Qed.

Lemma sub_morphim_pre : forall A R,
  A \subset D -> (f @* A \subset R) = (A \subset f @*^-1 R).
Proof.
move=> A R sAD; rewrite -morphpreSK (morphimS, morphimK) //.
apply/idP/idP; first by apply: subset_trans; exact: mulG_subr.
by move/(mulgS ('ker f)); rewrite -morphpreMl ?(sub1G, mul1g).
Qed.

Lemma morphpre_proper : forall R S,
  R \subset f @* D -> S \subset f @* D ->
  (f @*^-1 R \proper f @*^-1 S) = (R \proper S).
Proof. by move=> Q R dQ dR; rewrite /proper !morphpreSK. Qed.

Lemma sub_morphpre_im : forall R G,
    'ker f \subset G -> G \subset D -> R \subset f @* D ->
  (f @*^-1 R \subset G) = (R \subset f @* G).
Proof. by symmetry; rewrite -morphpreSK ?morphimGK. Qed.

Lemma ker_trivg_morphim : forall A,
  (A \subset 'ker f) = (A \subset D) && (f @* A \subset [1]).
Proof.
move=> A; case sAD: (A \subset D); first by rewrite sub_morphim_pre.
by rewrite subsetI sAD.
Qed.

Lemma morphimSK : forall A B,
  A \subset D -> (f @* A \subset f @* B) = (A \subset 'ker f * B).
Proof.
move=> A B sAD; transitivity (A \subset 'ker f * (D :&: B)).
  by rewrite -morphimK ?subsetIl // -sub_morphim_pre // /morphim setIA setIid.
by rewrite setIC group_modl (subsetIl, subsetI) // andbC sAD.
Qed.

Lemma morphimSGK : forall A G,
  A \subset D -> 'ker f \subset G -> (f @* A \subset f @* G) = (A \subset G).
Proof. by move=> G K sGD skfK; rewrite morphimSK // mulSGid. Qed.

Lemma ltn_morphim : forall A, [1] \proper 'ker_A f -> #|f @* A| < #|A|.
Proof.
move=> A; case/properP; rewrite sub1set; case/setIP=> A1 _ [x].
case/setIP=> Ax kx; rewrite (cardsD1 1 A) A1 ltnS => x1.
rewrite -{1}(setD1K A1) morphimU morphim1 (setUidPr _) ?sub1set; last first.
  by rewrite -(mker kx) mem_morphim ?(dom_ker kx) // inE x1.
by rewrite (leq_trans (leq_imset_card _ _)) ?subset_leq_card ?subsetIr.
Qed.

(* injectivity of image and preimage *)

Lemma morphpre_inj :
  {in [pred R : {set rT} | R \subset f @* D] &, injective (fun R => f @*^-1 R)}.
Proof. exact: can_in_inj morphpreK. Qed.

Lemma morphim_injG :
  {in [pred G : {group aT} | ('ker f \subset G) && (G \subset D)] &,
   injective (fun G => f @* G)}.
Proof.
move=> G H; case/andP=> sKG sGD; case/andP=> sKH sHD eqfGH.
by apply: val_inj; rewrite /= -(morphimGK sKG sGD) eqfGH morphimGK.
Qed.

Lemma morphim_inj : forall G H,
    ('ker f \subset G) && (G \subset D) ->
    ('ker f \subset H) && (H \subset D) ->
  f @* G = f @* H -> G :=: H.
Proof. by move=> G H nsGf nsHf; move/morphim_injG->. Qed.

(* commutation with generated groups and cycles *)

Lemma morphim_gen : forall A, A \subset D -> f @* <<A>> = <<f @* A>>.
Proof.
move=> A sAD; apply/eqP.
rewrite eqEsubset andbC gen_subG morphimS; last exact: subset_gen.
by rewrite sub_morphim_pre gen_subG // -sub_morphim_pre // subset_gen.
Qed.

Lemma morphim_cycle : forall x, x \in D -> f @* <[x]> = <[f x]>.
Proof. by move=> x Dx; rewrite morphim_gen (sub1set, morphim_set1). Qed.

Lemma morphimY : forall A B,
  A \subset D -> B \subset D -> f @* (A <*> B) = f @* A <*> f @* B.
Proof. by move=> A B sAD sBD; rewrite morphim_gen ?morphimU // subUset sAD. Qed.

Lemma morphpre_gen : forall R,
  1 \in R -> R \subset f @* D -> f @*^-1 <<R>> = <<f @*^-1 R>>.
Proof.
move=> R R1 sRfD; apply/eqP.
rewrite eqEsubset andbC gen_subG morphpreS; last exact: subset_gen.
rewrite -{1}(morphpreK sRfD) -morphim_gen ?subsetIl // morphimGK //=.
  by rewrite sub_gen // setIS // preimsetS ?sub1set.
by rewrite gen_subG subsetIl.
Qed.

(* commutator, normaliser, normal, center properties*)

Lemma morphimR : forall A B,
  A \subset D -> B \subset D -> f @* [~: A, B] = [~: f @* A, f @* B].
Proof.
move=> A B; move/subsetP=> sAD; move/subsetP=> sBD.
rewrite morphim_gen; last first; last congr <<_>>.
  by apply/subsetP=> z; case/imset2P=> x y Ax By ->; rewrite groupR; auto.
apply/setP=> fz; apply/morphimP/imset2P=> [[z _] | [fx fy]].
  case/imset2P=> x y Ax By -> -> {z fz}.
  have Dx := sAD x Ax; have Dy := sBD y By.
  by exists (f x) (f y); rewrite ?(mem_imset, morphR) // ?(inE, Dx, Dy).
case/morphimP=> x Dx Ax ->{fx}; case/morphimP=> y Dy By ->{fy} -> {fz}.
by exists [~ x, y]; rewrite ?(inE, morphR, groupR, mem_imset2).
Qed.

Lemma morphim_norm : forall A, f @* 'N(A) \subset 'N(f @* A).
Proof.
move=> A; apply/subsetP=> fx; case/morphimP=> x Dx Nx -> {fx}.
by rewrite inE -morphimJ ?(normP Nx).
Qed.

Lemma morphim_norms : forall A B,
  A \subset 'N(B) -> f @* A \subset 'N(f @* B).
Proof.
move=> A B nBA; apply: subset_trans (morphim_norm B); exact: morphimS.
Qed.

Lemma morphim_subnorm : forall A B, f @* 'N_A(B) \subset 'N_(f @* A)(f @* B).
Proof.
move=> A B; exact: subset_trans (morphimI A _) (setIS _ (morphim_norm B)).
Qed.

Lemma morphim_normal : forall A B, A <| B -> f @* A <| f @* B.
Proof.
move=> A B; case/andP=> sAB nAB.
by rewrite /(_ <| _) morphimS // morphim_norms.
Qed.

Lemma morphim_cent1 : forall x, x \in D -> f @* 'C[x] \subset 'C[f x].
Proof. by move=> x Dx; rewrite -(morphim_set1 Dx) morphim_norm. Qed.

Lemma morphim_cent1s : forall A x,
  x \in D -> A \subset 'C[x] -> f @* A \subset 'C[f x].
Proof.
move=> A x Dx cAx; apply: subset_trans (morphim_cent1 Dx); exact: morphimS.
Qed.

Lemma morphim_subcent1 : forall A x, x \in D ->
   f @* 'C_A[x] \subset 'C_(f @* A)[f x].
Proof. by move=> A x Dx; rewrite -(morphim_set1 Dx) morphim_subnorm. Qed.

Lemma morphim_cent : forall A, f @* 'C(A) \subset 'C(f @* A).
Proof.
move=> A; apply/bigcapsP=> fx; case/morphimP=> x Dx Ax ->{fx}.
apply: subset_trans (morphim_cent1 Dx); apply: morphimS; exact: bigcap_inf.
Qed.

Lemma morphim_cents : forall A B,
  A \subset 'C(B) -> f @* A \subset 'C(f @* B).
Proof.
move=> A B cBA; apply: subset_trans (morphim_cent B); exact: morphimS.
Qed.

Lemma morphim_subcent : forall A B, f @* 'C_A(B) \subset 'C_(f @* A)(f @* B).
Proof.
move=> A B; exact: subset_trans (morphimI A _) (setIS _ (morphim_cent B)).
Qed.

Lemma morphim_abelian : forall A, abelian A -> abelian (f @* A).
Proof. move=> A; exact: morphim_cents. Qed.

Lemma morphpre_norm : forall R, f @*^-1 'N(R) \subset 'N(f @*^-1 R).
Proof.
move=> R; apply/subsetP=> x; rewrite !inE; case/andP=> Dx Nfx.
by rewrite -morphpreJ ?morphpreS.
Qed.

Lemma morphpre_norms : forall R S,
  R \subset 'N(S) -> f @*^-1 R \subset 'N(f @*^-1 S).
Proof.
move=> R S nSR; apply: subset_trans (morphpre_norm S); exact: morphpreS.
Qed.

Lemma morphpre_normal : forall R S,
  R \subset f @* D -> S \subset f @* D -> (f @*^-1 R <| f @*^-1 S) = (R <| S).
Proof.
move=> R S sRfD sSfD; apply/idP/andP=> [|[sRS nSR]].
  by move/morphim_normal; rewrite !morphpreK //; case/andP.
by rewrite /(_ <| _) (subset_trans _ (morphpre_norm _)) morphpreS.
Qed.

Lemma morphpre_subnorm : forall R S,
  f @*^-1 'N_R(S) \subset 'N_(f @*^-1 R)(f @*^-1 S).
Proof. by move=> R S; rewrite morphpreI setIS ?morphpre_norm. Qed.

Lemma morphim_normG : forall G,
  'ker f \subset G -> G \subset D -> f @* 'N(G) = 'N_(f @* D)(f @* G).
Proof.
move=> G sKG sGD; apply/eqP; rewrite eqEsubset -{1}morphimIdom morphim_subnorm.
rewrite -(morphpreK (subsetIl _ _)) morphimS //= morphpreI subIset // orbC.
by rewrite -{2}(morphimGK sKG sGD) morphpre_norm.
Qed.

Lemma morphim_subnormG : forall A G,
  'ker f \subset G -> G \subset D -> f @* 'N_A(G) = 'N_(f @* A)(f @* G).
Proof.
move=> A B sKB sBD; rewrite morphimIG ?normsG // morphim_normG //.
by rewrite setICA setIA morphimIim.
Qed.

Lemma morphpre_cent1 : forall x, x \in D -> 'C_D[x] \subset f @*^-1 'C[f x].
Proof.
move=> x Dx; rewrite -sub_morphim_pre ?subsetIl //.
by apply: subset_trans (morphim_cent1 Dx); rewrite morphimS ?subsetIr.
Qed.

Lemma morphpre_cent1s : forall R x,
  x \in D -> R \subset f @* D -> f @*^-1 R \subset 'C[x] -> R \subset 'C[f x].
Proof. by move=> R x Dx sRfD; move/(morphim_cent1s Dx); rewrite morphpreK. Qed.

Lemma morphpre_subcent1 : forall R x, x \in D ->
  'C_(f @*^-1 R)[x] \subset f @*^-1 'C_R[f x].
Proof.
move=> R x Dx; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: morphpre_cent1.
Qed.

Lemma morphpre_cent : forall A, 'C_D(A) \subset f @*^-1 'C(f @* A).
Proof.
move=> A; rewrite -sub_morphim_pre ?subsetIl //.
rewrite morphimGI ?(subsetIl, subIset) // orbC.
by rewrite (subset_trans (morphim_cent _)).
Qed.

Lemma morphpre_cents : forall A R,
  R \subset f @* D -> f @*^-1 R \subset 'C(A) -> R \subset 'C(f @* A).
Proof. by move=> A R sRfD; move/morphim_cents; rewrite morphpreK. Qed.

Lemma morphpre_subcent : forall R A,
  'C_(f @*^-1 R)(A) \subset f @*^-1 'C_R(f @* A).
Proof.
move=> R A; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: morphpre_cent.
Qed.

(* local injectivity properties *)

Lemma injmP : reflect {in D &, injective f} ('injm f).
Proof.
apply: (iffP subsetP) => [injf x y Dx Dy | injf x /= Kx].
  by case/ker_rcoset=> // z; move/injf; move/set1P->; rewrite mul1g.
have Dx := dom_ker Kx; apply/set1P; apply: injf => //.
by apply/rcoset_kerP; rewrite // mulg1.
Qed.

Lemma card_im_injm : (#|f @* D| == #|D|) = 'injm f.
Proof. by rewrite morphimEdom (sameP imset_injP injmP). Qed.

Section Injective.

Hypothesis injf : 'injm f.

Lemma ker_injm : 'ker f = 1.
Proof. exact/trivgP. Qed.

Lemma injmK : forall A, A \subset D -> f @*^-1 (f @* A) = A.
Proof. by move=> A sAD; rewrite morphimK // ker_injm // mul1g. Qed.

Lemma injm_morphim_inj : forall A B,
  A \subset D -> B \subset D -> f @* A = f @* B -> A = B.
Proof. by move=> A B sAD sBD eqAB; rewrite -(injmK sAD) eqAB injmK. Qed.

Lemma card_injm : forall A, A \subset D -> #|f @* A| = #|A|.
Proof.
move=> A sAD; rewrite morphimEsub // card_in_imset //.
exact: (sub_in2 (subsetP sAD) (injmP injf)).
Qed.

Lemma order_injm : forall x, x \in D -> #[f x] = #[x].
Proof.
by move=> x Dx; rewrite orderE -morphim_cycle // card_injm ?cycle_subG.
Qed.

Lemma injm1 : forall x, x \in D -> f x = 1 -> x = 1.
Proof. by move=> x Dx; move/(kerP Dx); rewrite ker_injm; move/set1P. Qed.

Lemma morph_injm_eq1 : forall x, x \in D -> (f x == 1) = (x == 1).
Proof. by move=> x Dx; rewrite -morph1 (inj_in_eq (injmP injf)) ?group1. Qed.

Lemma morphim_injm_eq1 : forall A, A \subset D -> (f @* A == 1) = (A == 1).
Proof.
move=> A sAD; rewrite -morphim1.
by apply/eqP/eqP=> [|-> //]; apply: injm_morphim_inj; last exact: sub1G.
Qed.

Lemma injmSK : forall A B,
  A \subset D -> (f @* A \subset f @* B) = (A \subset B).
Proof. by move=> A B sAD; rewrite morphimSK // ker_injm mul1g. Qed.

Lemma sub_morphpre_injm : forall R A,
    A \subset D -> R \subset f @* D ->
  (f @*^-1 R \subset A) = (R \subset f @* A).
Proof. by move=> R A sAD sRfD; rewrite -morphpreSK ?injmK. Qed.

Lemma injmI : forall A B, f @* (A :&: B) = f @* A :&: f @* B.
Proof.
move=> A B; have sfI: f @* A :&: f @* B \subset f @* D.
  by apply/setIidPr; rewrite setIA morphimIim.
rewrite -(morphpreK sfI) morphpreI -(morphimIdom A) -(morphimIdom B).
by rewrite !injmK ?subsetIl // setICA -setIA !morphimIdom.
Qed.

Lemma injm_norm : forall A, A \subset D -> f @* 'N(A) = 'N_(f @* D)(f @* A).
Proof.
move=> A sAD; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subnorm.
rewrite -sub_morphpre_injm ?subsetIl // morphpreI injmK // setIS //.
by rewrite -{2}(injmK sAD) morphpre_norm.
Qed.

Lemma injm_subnorm : forall A B,
  B \subset D -> f @* 'N_A(B) = 'N_(f @* A)(f @* B).
Proof.
by move=> A B sBD; rewrite injmI injm_norm // setICA setIA morphimIim.
Qed.

Lemma injm_cent1 : forall x, x \in D -> f @* 'C[x] = 'C_(f @* D)[f x].
Proof. by move=> x Dx; rewrite injm_norm ?morphim_set1 ?sub1set. Qed.

Lemma injm_subcent1 : forall A x, x \in D -> f @* 'C_A[x] = 'C_(f @* A)[f x].
Proof. by move=> A x Dx; rewrite injm_subnorm ?morphim_set1 ?sub1set. Qed.

Lemma injm_cent : forall A, A \subset D -> f @* 'C(A) = 'C_(f @* D)(f @* A).
Proof.
move=> A sAD; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subcent.
apply/subsetP=> fx; case/setIP; case/morphimP=> x Dx _ ->{fx} cAfx.
rewrite mem_morphim // inE Dx -sub1set centsC cent_set1 -injmSK //.
by rewrite injm_cent1 // subsetI morphimS // -cent_set1 centsC sub1set.
Qed.

Lemma injm_subcent : forall A B,
  B \subset D -> f @* 'C_A(B) = 'C_(f @* A)(f @* B).
Proof.
by move=> A B sBD; rewrite injmI injm_cent // setICA setIA morphimIim.
Qed.

Lemma injm_abelian : forall A, A \subset D -> abelian (f @* A) = abelian A.
Proof.
move=> A sAD; rewrite /abelian !(sameP setIidPl eqP) -injm_subcent //.
by rewrite !eqEsubset !injmSK // subIset ?sAD.
Qed.

End Injective.

Lemma eq_morphim : forall g : {morphism D >-> rT},
  {in D, f =1 g} -> forall A, f @* A = g @* A.
Proof.
by move=> g efg A; apply: eq_in_imset; apply: sub_in1 efg => x; case/setIP.
Qed.

Lemma eq_in_morphim : forall B A (g : {morphism B >-> rT}),
  D :&: A = B :&: A -> {in A, f =1 g} -> f @* A = g @* A.
Proof.
move=> B A g eqDBA eqAfg; rewrite /morphim /= eqDBA.
by apply: eq_in_imset => x; case/setIP=> _; exact: eqAfg.
Qed.

End MorphismTheory.

Notation "''ker' f" := (ker_group (MorPhantom f)) : subgroup_scope.
Notation "''ker_' G f" := (G :&: 'ker f)%G : subgroup_scope.
Notation "f @* G" := (morphim_group (MorPhantom f) G) : subgroup_scope.
Notation "f @*^-1 M" := (morphpre_group (MorPhantom f) M) : subgroup_scope.
Notation "f @: D" := (morph_dom_group f D) : subgroup_scope.

Section IdentityMorphism.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Type G : {group gT}.

Definition idm of {set gT} := fun x : gT => x : FinGroup.sort gT.

Lemma idm_morphM : forall A, {in A & , {morph idm A : x y / x * y}}.
Proof. by []. Qed.

Canonical Structure idm_morphism A := Morphism (@idm_morphM A).

Lemma injm_idm : forall G, 'injm (idm G).
Proof. by move=> G; apply/injmP=> x y _ _. Qed.

Lemma ker_idm : forall G, 'ker (idm G) = 1.
Proof. by move=> G; apply/trivgP; exact: injm_idm. Qed.

Lemma morphim_idm : forall A B, B \subset A -> idm A @* B = B.
Proof.
move=> A B; rewrite /morphim /= /idm; move/setIidPr->.
by apply/setP=> x; apply/imsetP/idP=> [[y By ->]|Bx]; last exists x.
Qed.

Lemma morphpre_idm : forall A B, idm A @*^-1 B = A :&: B.
Proof. by move=> A B; apply/setP=> x; rewrite !inE. Qed.

Lemma im_idm : forall A, idm A @* A = A.
Proof. move=> A; exact: morphim_idm. Qed.

End IdentityMorphism.

Prenex Implicits idm.

Section RestrictedMorphism.

Variables aT rT : finGroupType.
Variables A D : {set aT}.
Implicit Type B : {set aT}.
Implicit Type R : {set rT}.

Definition restrm of A \subset D := @id (aT -> FinGroup.sort rT).

Section Props.

Hypothesis sAD : A \subset D.
Variable f : {morphism D >-> rT}.
Local Notation fA := (restrm sAD (mfun f)).

Canonical Structure restrm_morphism :=
  @Morphism aT rT A fA (sub_in2 (subsetP sAD) (morphM f)).

Lemma morphim_restrm : forall B, fA @* B = f @* (A :&: B).
Proof. by move=> B; rewrite {2}/morphim setIA (setIidPr sAD). Qed.

Lemma im_restrm : fA @* A = f @* A.
Proof. by rewrite morphim_restrm setIid. Qed.

Lemma morphpre_restrm : forall R, fA @*^-1 R = A :&: f @*^-1 R.
Proof. by move=> R; rewrite setIA (setIidPl sAD). Qed.

Lemma ker_restrm : 'ker fA = 'ker_A f.
Proof. exact: morphpre_restrm. Qed.

Lemma injm_restrm : 'injm f -> 'injm fA.
Proof. by apply: subset_trans; rewrite ker_restrm subsetIr. Qed.

End Props.

Lemma restrmP : forall f : {morphism D >-> rT}, A \subset 'dom f ->
  {g : {morphism A >-> rT} | [/\ g = f :> (aT -> rT), 'ker g = 'ker_A f,
                                 forall R, g @*^-1 R = A :&: f @*^-1 R
                               & forall B, B \subset A -> g @* B = f @* B]}.
Proof.
move=> f sAD; exists (restrm_morphism sAD f).
split=> // [|R|B sBA]; first 1 [exact: ker_restrm | exact: morphpre_restrm].
by rewrite morphim_restrm (setIidPr sBA).
Qed.

Lemma domP : forall f : {morphism D >-> rT}, 'dom f = A ->
  {g : {morphism A >-> rT} | [/\ g = f :> (aT -> rT), 'ker g = 'ker f,
                                 forall R, g @*^-1 R = f @*^-1 R
                               & forall B, g @* B = f @* B]}.
Proof. by move=> f <-; exists f. Qed.

End RestrictedMorphism.

Prenex Implicits restrm.
Implicit Arguments restrmP [aT rT D A].
Implicit Arguments domP [aT rT D A].

Section TrivMorphism.

Variables aT rT : finGroupType.

Definition trivm of {set aT} & aT := 1 : FinGroup.sort rT.

Lemma trivm_morphM : forall A : {set aT},
  {in A & , {morph trivm A : x y / x * y}}.
Proof. by move=> A x y /=; rewrite mulg1. Qed.

Canonical Structure triv_morph A := Morphism (@trivm_morphM A).

Lemma morphim_trivm : forall (G H : {group aT}), trivm G @* H = 1.
Proof.
move=> G H; apply/setP=> /= y; rewrite inE.
apply/idP/eqP=> [|->]; first by case/morphimP.
by apply/morphimP; exists (1 : aT); rewrite /= ?group1.
Qed.

Lemma ker_trivm : forall G : {group aT}, 'ker (trivm G) = G.
Proof. by move=> G; apply/setIidPl; apply/subsetP=> x _; rewrite !inE /=. Qed.

End TrivMorphism.

Prenex Implicits trivm.

(* Canonical Structure of morphism for the composition of 2 morphisms. *)

Section MorphismComposition.

Variables gT hT rT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).

Variable f : {morphism G >-> hT}.
Variable g : {morphism H >-> rT}.

Notation Local gof := (mfun g \o mfun f).

Lemma comp_morphM : {in f @*^-1 H &, {morph gof: x y / x * y}}.
Proof.
by move=> x y; rewrite /= !inE; do 2!case/andP=> ? ?; rewrite !morphM.
Qed.

Canonical Structure comp_morphism := Morphism comp_morphM.

Lemma ker_comp : 'ker gof = f @*^-1 'ker g.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma injm_comp : 'injm f -> 'injm g -> 'injm gof.
Proof. by move=> injf; rewrite ker_comp; case/trivgP=> ->. Qed.

Lemma morphim_comp : forall A : {set gT}, gof @* A = g @* (f @* A).
Proof.
move=> A; apply/setP=> z; apply/morphimP/morphimP=> [[x]|[y Hy fAy ->{z}]].
  rewrite !inE; case/andP=> Gx Hfx; exists (f x) => //.
  by apply/morphimP; exists x.
by case/morphimP: fAy Hy => x Gx Ax ->{y} Hfx; exists x; rewrite ?inE ?Gx.
Qed.

Lemma morphpre_comp : forall C : {set rT},
  gof @*^-1 C = f @*^-1 (g @*^-1 C).
Proof. by move=> C; apply/setP=> z; rewrite !inE andbA. Qed.

End MorphismComposition.

(* Canonical structure of morphism for the factor morphism *)

Section FactorMorphism.

Variables aT qT rT : finGroupType.

Variables G H : {group aT}.
Variable f : {morphism G >-> rT}.
Variable q : {morphism H >-> qT}.

Definition factm of 'ker q \subset 'ker f  & G \subset H :=
  fun x => f (repr (q @*^-1 [set x])).

Hypothesis sKqKf : 'ker q \subset 'ker f.
Hypothesis sGH : G \subset H.

Notation ff := (factm sKqKf sGH).

Lemma factmE : forall x, x \in G -> ff (q x) = f x.
Proof.
rewrite /ff => x Gx; have Hx := subsetP sGH x Gx.
have: x \in q @*^-1 [set q x] by rewrite !inE Hx /=.
move/mem_repr; case/morphpreP; move: (repr _) => y Hy; move/set1P.
by case/ker_rcoset=> // z Kz ->; rewrite mkerl ?(subsetP sKqKf).
Qed.

Lemma factm_morphM : {in q @* G &, {morph ff : x y / x * y}}.
Proof.
move=> xq yq; case/morphimP=> x Hx Gx ->{xq}.
by case/morphimP=> y Hy Gy ->{yq}; rewrite -morphM ?factmE ?groupM // morphM.
Qed.

Canonical Structure factm_morphism := Morphism factm_morphM.

Lemma morphim_factm : forall A : {set aT}, ff @* (q @* A) = f @* A.
Proof.
move=> A; rewrite -morphim_comp /= {1}/morphim /= morphimGK //; last first.
  by rewrite (subset_trans sKqKf) ?subsetIl.
apply/setP=> y; apply/morphimP/morphimP;
  by case=> x Gx Ax ->{y}; exists x; rewrite //= factmE.
Qed.

Lemma morphpre_factm : forall C : {set rT}, ff @*^-1 C =  q @* (f @*^-1 C).
Proof.
move=> C; apply/setP=> y; rewrite !inE /=.
apply/andP/morphimP=> [[]|[x Hx]]; last first.
  by case/morphpreP=> Gx Cfx ->; rewrite factmE ?mem_imset ?inE ?Hx.
case/morphimP=> x Hx Gx ->; rewrite factmE //.
by exists x; rewrite // !inE Gx.
Qed.

Lemma ker_factm : 'ker ff = q @* 'ker f.
Proof. exact: morphpre_factm. Qed.

Lemma injm_factm : 'injm f -> 'injm ff.
Proof. by rewrite ker_factm; case/trivgP=> ->; rewrite morphim1. Qed.

Lemma injm_factmP : reflect ('ker f = 'ker q) ('injm ff).
Proof.
rewrite ker_factm -morphimIdom sub_morphim_pre ?subsetIl //.
rewrite setIA (setIidPr sGH) (sameP setIidPr eqP) (setIidPl _) // eq_sym.
exact: eqP.
Qed.

Lemma ker_factm_loc : forall K : {group aT}, 'ker_(q @* K) ff = q @* 'ker_K f.
Proof. by move=> K; rewrite ker_factm -morphimIG. Qed.

End FactorMorphism.

Prenex Implicits factm.

Section InverseMorphism.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types C D : {set rT}.
Variables (G : {group aT}) (f : {morphism G >-> rT}).
Hypothesis injf : 'injm f.

Lemma invm_subker : 'ker f \subset 'ker (idm G).
Proof. by rewrite ker_idm. Qed.

Definition invm := factm invm_subker (subxx _).

Canonical Structure invm_morphism := Eval hnf in [morphism of invm].

Lemma invmE : {in G, cancel f invm}.
Proof. exact: factmE. Qed.

Lemma invmK : {in f @* G, cancel invm f}.
Proof. by move=> fx; case/morphimP=> x _ Gx ->; rewrite invmE. Qed.

Lemma morphpre_invm : forall A, invm @*^-1 A = f @* A.
Proof. by move=> A; rewrite morphpre_factm morphpre_idm morphimIdom. Qed.

Lemma morphim_invm : forall A, A \subset G -> invm @* (f @* A) = A.
Proof. by move=> A sAG; rewrite morphim_factm morphim_idm. Qed.

Lemma morphim_invmE : forall C, invm @* C = f @*^-1 C.
Proof.
move=> C; rewrite -morphpreIdom -(morphim_invm (subsetIl _ _)).
by rewrite morphimIdom -morphpreIim morphpreK (subsetIl, morphimIdom).
Qed.

Lemma injm_proper : forall A B,
  A \subset G -> B \subset G -> (f @* A \proper f @* B) = (A \proper B).
Proof.
move=> A B dA dB; rewrite -morphpre_invm -(morphpre_invm B).
by rewrite morphpre_proper ?morphim_invm.
Qed.

Lemma injm_invm : 'injm invm.
Proof. by move/can_in_inj: invmK; move/injmP. Qed.

Lemma ker_invm : 'ker invm = 1.
Proof. by move/trivgP: injm_invm. Qed.

Lemma im_invm : invm @* (f @* G) = G.
Proof. exact: morphim_invm. Qed.

End InverseMorphism.

Prenex Implicits invm.

Section InjFactm.

Variables (gT aT rT : finGroupType) (D G : {group gT}).
Variables (g : {morphism G >-> rT}) (f : {morphism D >-> aT}) (injf : 'injm f).

Definition ifactm :=
  tag (domP [morphism of g \o invm injf] (morphpre_invm injf G)).

Lemma ifactmE : {in D, forall x, ifactm (f x) = g x}.
Proof.
rewrite /ifactm => x Dx; case: domP => f' /= [def_f' _ _ _].
by rewrite {f'}def_f' //= invmE.
Qed.

Lemma morphim_ifactm : forall A : {set gT},
  A \subset D -> ifactm @* (f @* A) = g @* A.
Proof.
rewrite /ifactm => A sAD; case: domP => _ /= [_ _ _ ->].
by rewrite morphim_comp morphim_invm.
Qed.

Lemma im_ifactm : G \subset D -> ifactm @* (f @* G) = g @* G.
Proof. exact: morphim_ifactm. Qed.

Lemma morphpre_ifactm : forall C, ifactm @*^-1 C = f @* (g @*^-1 C).
Proof.
rewrite /ifactm => C; case: domP => _ /= [_ _ -> _].
by rewrite morphpre_comp morphpre_invm.
Qed.

Lemma ker_ifactm : 'ker ifactm = f @* 'ker g.
Proof. exact: morphpre_ifactm. Qed.

Lemma injm_ifactm : 'injm g -> 'injm ifactm.
Proof. by rewrite ker_ifactm; move/trivgP->; rewrite morphim1. Qed.

End InjFactm.

(* Reflected (boolean) form of morphism and isomorphism properties *)

Section ReflectProp.

Variables aT rT : finGroupType.

Section Defs.

Variables (A : {set aT}) (B : {set rT}).

(* morphic is the morphM property of morphisms seen through morphicP *)
Definition morphic (f : aT -> rT) :=
  forallb u, (u \in [predX A & A]) ==> (f (u.1 * u.2) == f u.1 * f u.2).

Definition isom f := f @: A^# == B^#.

Definition misom f := morphic f && isom f.

Definition isog := existsb f : {ffun aT -> rT}, misom f.

Section MorphicProps.

Variable f : aT -> rT.

Lemma morphicP : reflect {in A &, {morph f : x y / x * y}} (morphic f).
Proof.
apply: (iffP forallP) => [fM x y Ax Ay | fM [x y] /=].
  by apply/eqP; have:= fM (x, y); rewrite inE /= Ax Ay.
by apply/implyP; case/andP=> Ax Ay; rewrite fM.
Qed.

Definition morphm of morphic f := f : aT -> FinGroup.sort rT.

Lemma morphmE : forall fM, morphm fM = f. Proof. by []. Qed.

Canonical Structure morphm_morphism fM :=
  @Morphism _ _ A (morphm fM) (morphicP fM).

End MorphicProps.

Lemma misomP : forall f, reflect {fM : morphic f & isom (morphm fM)} (misom f).
Proof. by move=> f; apply: (iffP andP) => [] [fM fiso] //; exists fM. Qed.

Lemma misom_isog : forall f, misom f -> isog.
Proof.
move=> f; case/andP=> fM iso_f; apply/existsP; exists (finfun f).
apply/andP; split; last by rewrite /misom /isom !(eq_imset _ (ffunE f)).
apply/forallP=> u; rewrite !ffunE; exact: forallP fM u.
Qed.

Lemma isom_isog : forall (D : {group aT}) (f : {morphism D >-> rT}),
  A \subset D -> isom f -> isog.
Proof.
move=> D f sAD isof; apply: (@misom_isog f); rewrite /misom isof andbT.
apply/morphicP; exact: (sub_in2 (subsetP sAD) (morphM f)).
Qed.

End Defs.

Implicit Arguments isom_isog [A B D].

Infix "\isog" := isog.

(* The real reflection properties only hold for true groups and morphisms. *)

Section Main.

Variables (G : {group aT}) (H : {group rT}).
Notation fMT := {morphism G >-> rT}.

Lemma isomP : forall f : fMT, reflect ('injm f /\ f @* G = H) (isom G H f).
Proof.
move=> f; apply: (iffP eqP) => [eqfGH | [injf <-]]; last first.
  by rewrite setDE -morphimEsub ?subsetIl // -setDE morphimDG // morphim1.
split.
  apply/subsetP=> x; rewrite !inE /=; case/andP=> Gx fx1; apply/idPn=> nx1.
  by move/setP: eqfGH; move/(_ (f x)); rewrite mem_imset ?inE (nx1, fx1).
rewrite morphimEdom -{2}(setD1K (group1 G)) imsetU eqfGH.
by rewrite imset_set1 morph1 setD1K.
Qed.

Lemma isom_card : forall f : fMT, isom G H f -> #|G| = #|H|.
Proof.
move=> f; case/isomP; move/injmP=> injf <-.
by rewrite morphimEdom card_in_imset.
Qed.

Lemma isogP : reflect (exists2 f : fMT, 'injm f & f @* G = H) (G \isog H).
Proof.
apply: (iffP idP) => [| [f *]]; last by apply: (isom_isog f); last exact/isomP.
by case/existsP=> f; case/misomP=> fM; case/isomP; exists (morphm_morphism fM).
Qed.

End Main.

Variables (G : {group aT}) (f : {morphism G >-> rT}).

Lemma morphim_isom : forall (H : {group aT}) (K : {group rT}),
  H \subset G -> isom H K f -> f @* H = K.
Proof.
by move=> H K; case/(restrmP f)=> g [gf _ _ <- //]; rewrite -gf; case/isomP.
Qed.

Lemma sub_isom : forall (A : {set aT}) (C : {set rT}),
  A \subset G -> f @* A = C -> 'injm f -> isom A C f.
Proof.
move=> A C sAG; case: (restrmP f sAG) => g [_ _ _ img] <-{C} injf.
rewrite /isom -morphimEsub ?morphimDG ?morphim1 //.
by rewrite subDset setUC subsetU ?sAG.
Qed.

Lemma sub_isog : forall (A : {set aT}),
  A \subset G -> 'injm f -> isog A (f @* A).
Proof. move=> A sAG injf; apply: (isom_isog f sAG); exact: sub_isom. Qed.

End ReflectProp.

Implicit Arguments morphicP [aT rT A f].
Implicit Arguments misomP [aT rT A B f].
Implicit Arguments isom_isog [aT rT A B D].
Implicit Arguments isomP [aT rT G H f].
Implicit Arguments isogP [aT rT G H].
Prenex Implicits morphic morphicP morphm isom isog isomP misomP isogP.
Notation "x \isog y":= (isog x y).

Section Isomorphisms.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_refl : G \isog G.
Proof.
by apply/isogP; exists [morphism of idm G]; rewrite /= ?injm_idm ?morphim_idm.
Qed.

Lemma card_isog : G \isog H -> #|G| = #|H|.
Proof. case/isogP=> f injf <-; apply: isom_card (f) _; exact/isomP. Qed.

Lemma isog_abelian :  G \isog H -> abelian G = abelian H.
Proof. by case/isogP=> f injf <-; rewrite injm_abelian. Qed.

Lemma trivial_isog : G :=: 1 -> H :=: 1 -> G \isog H.
Proof.
move=> -> ->; apply/isogP.
exists [morphism of @trivm gT hT 1]; rewrite /= ?morphim1 //.
rewrite ker_trivm; exact: subxx.
Qed.

Lemma isog_eq1 : G \isog H -> (G :==: 1) = (H :==: 1).
Proof. by move=> isoGH; rewrite !trivg_card1 card_isog. Qed.

Lemma isog_symr : G \isog H -> H \isog G.
Proof.
case/isogP=> f injf <-; apply/isogP.
by exists [morphism of invm injf]; rewrite /= ?injm_invm // im_invm.
Qed.

Lemma isog_trans : G \isog H -> H \isog K -> G \isog K.
Proof.
case/isogP=> f injf <-; case/isogP=> g injg <-.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
rewrite -morphim_comp -{1 8}defG.
by apply/isogP; exists [morphism of g \o f]; rewrite ?injm_comp.
Qed.

End Isomorphisms.

Section IsoBoolEquiv.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_sym : (G \isog H) = (H \isog G).
Proof. apply/idP/idP; exact: isog_symr. Qed.

Lemma isog_transl : G \isog H -> (G \isog K) = (H \isog K).
Proof.
by move=> iso; apply/idP/idP; apply: isog_trans; rewrite // -isog_sym.
Qed.

Lemma isog_transr : G \isog H -> (K \isog G) = (K \isog H).
Proof.
by move=> iso; apply/idP/idP; move/isog_trans; apply; rewrite // -isog_sym.
Qed.

End IsoBoolEquiv.

Section Homg.

Implicit Types rT gT aT : finGroupType.

Definition homg rT aT (C : {set rT}) (D : {set aT}) :=
  existsb f : {ffun aT -> rT}, (morphic D f && (f @: D == C)).

Lemma homgP : forall rT aT (C : {set rT}) (D : {set aT}), 
  reflect (exists f : {morphism D >-> rT}, f @* D = C) (homg C D).
Proof.
move=> rT aT H G; apply: (iffP existsP) => [[f] | [f <-]].
  case/andP=> fM; move/eqP=> <-; exists (morphm_morphism fM).
  by rewrite /morphim /= setIid.
exists (finfun f); apply/andP; split.
  by apply/morphicP=> x y Dx Dy; rewrite !ffunE morphM.
by apply/eqP; rewrite /morphim setIid; apply: eq_imset => x; rewrite ffunE.
Qed.

Lemma morphim_homg : forall aT rT (A D : {set aT}) (f : {morphism D >-> rT}),
  A \subset D -> homg (f @* A) A.
Proof.
move=> aT rT A D f sAD; apply/homgP; exists (restrm_morphism sAD f).
by rewrite morphim_restrm setIid.
Qed.

Lemma leq_homg : forall rT aT (C : {set rT}) (G : {group aT}),
  homg C G -> #|C| <= #|G|.
Proof. move=> rT aT C G; case/homgP=> f <-; exact: leq_morphim. Qed.

Lemma homg_refl : forall aT (A : {set aT}), homg A A.
Proof.
by move=> aT A; apply/homgP; exists (idm_morphism A); rewrite im_idm.
Qed.

Lemma homg_trans : forall aT (B : {set aT}),
                   forall rT (C : {set rT}) gT (G : {group gT}),
  homg C B -> homg B G -> homg C G.
Proof.
move=> aT B rT C gT G homCB homBG.
case/homgP: homBG homCB => fG <-; case/homgP=> fK <-.
by rewrite -morphim_comp morphim_homg // -sub_morphim_pre.
Qed.

Lemma isogEcard : forall rT aT (G : {group rT}) (H : {group aT}),
  (G \isog H) = (homg G H) && (#|H| <= #|G|).
Proof.
move=> rT aT G H; rewrite isog_sym; apply/isogP/andP=> [[f injf <-] | []].
  by rewrite leq_eqVlt eq_sym card_im_injm injf morphim_homg.
case/homgP=> f <-; rewrite leq_eqVlt eq_sym card_im_injm.
by rewrite ltnNge leq_morphim orbF; exists f.
Qed.

Lemma isog_hom : forall rT aT (G : {group rT}) (H : {group aT}),
  G \isog H -> homg G H.
Proof. by move=> rT aT G H; rewrite isogEcard; case/andP. Qed.

Lemma isogEhom : forall rT aT (G : {group rT}) (H : {group aT}),
  (G \isog H) = homg G H && homg H G.
Proof.
move=> rT aT G H; apply/idP/andP=> [isoGH | [homGH homHG]].
  by rewrite !isog_hom // isog_sym.
by rewrite isogEcard homGH leq_homg.
Qed.

Lemma eq_homgl : forall gT aT rT,
                 forall (G : {group gT}) (H : {group aT}) (K : {group rT}),
  G \isog H -> homg G K = homg H K.
Proof.
move=> gT aT rT G H K; rewrite isogEhom; case/andP=> homGH homHG.
apply/idP/idP; exact: homg_trans.
Qed.

Lemma eq_homgr : forall gT rT aT,
                 forall (G : {group gT}) (H : {group rT}) (K : {group aT}),
  G \isog H -> homg K G = homg K H.
Proof.
move=> gT rT aT G H K; rewrite isogEhom; case/andP=> homGH homHG.
apply/idP/idP=> homK; exact: homg_trans homK _.
Qed.

End Homg.

Notation "G \homg H" := (homg G H)
  (at level 70, no associativity) : group_scope.

Implicit Arguments homgP [rT aT C D].

(* Isomorphism between a group and its subtype. *)

Section SubMorphism.

Variables (gT : finGroupType) (G : {group gT}).

Canonical Structure sgval_morphism := Morphism (@sgvalM _ G).
Canonical Structure subg_morphism := Morphism (@subgM _ G).

Lemma injm_sgval : 'injm sgval.
Proof. apply/injmP; apply: in2W; exact: subg_inj. Qed.

Lemma injm_subg : 'injm (subg G).
Proof. apply/injmP; exact: can_in_inj (@subgK _ _). Qed.
Hint Resolve injm_sgval injm_subg.

Lemma ker_sgval : 'ker sgval = 1. Proof. exact/trivgP. Qed.
Lemma ker_subg : 'ker (subg G) = 1. Proof. exact/trivgP. Qed.

Lemma im_subg : subg G @* G = [subg G].
Proof.
apply/eqP; rewrite -subTset morphimEdom.
by apply/subsetP=> u _; rewrite -(sgvalK u) mem_imset ?subgP.
Qed.

Lemma sgval_sub : forall A, sgval @* A \subset G.
Proof. move=> A; apply/subsetP=> x; case/imsetP=> u _ ->; exact: subgP. Qed.

Lemma sgvalmK : forall A, subg G @* (sgval @* A) = A.
Proof.
move=> A; apply/eqP; rewrite eqEcard !card_injm ?subsetT ?sgval_sub //.
rewrite leqnn andbT -morphim_comp; apply/subsetP=> u /=.
by case/morphimP=> v _ Av ->; rewrite /= sgvalK.
Qed.

Lemma subgmK : forall A : {set gT}, A \subset G -> sgval @* (subg G @* A) = A.
Proof.
move=> A sAG; apply/eqP; rewrite eqEcard !card_injm ?subsetT //.
rewrite leqnn andbT -morphim_comp morphimE /= morphpreT.
by apply/subsetP=> u; case/morphimP=> v Gv Av -> /=; rewrite subgK.
Qed.

Lemma im_sgval : sgval @* [subg G] = G.
Proof. by rewrite -{2}im_subg subgmK. Qed.

Lemma isom_subg : isom G [subg G] (subg G).
Proof. by apply/isomP; rewrite im_subg. Qed.

Lemma isom_sgval : isom [subg G] G sgval.
Proof. by apply/isomP; rewrite im_sgval. Qed.

Lemma isog_subg : isog G [subg G].
Proof. exact: isom_isog isom_subg. Qed.

End SubMorphism.


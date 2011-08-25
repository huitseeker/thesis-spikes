(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun ssralg matrix zmodp tuple vector.

(*****************************************************************************)
(*  * Finite dimensional algebras                                            *)
(*     algFType K       == type for finite dimension algebra structure.      *)
(*     algFMixin K      == builds the mixins containing the definition       *)
(*                         of an algebra over K.                             *)
(*     AlgFType T M     == packs the mixin M to build an algebra of type     *)
(*                         algFType K. The field K will be infered from the  *)
(*                         mixin M. The underlying type T should have a      *)
(*                         algType canonical structure.                      *)
(*      ... inherite definition and proofs from algType + vector.            *)
(*      (A * B)%VS      == the smallest vector space that contains           *)
(*                           {a * b | a \in A & b \in B}                     *)
(*      {algebra A}     == an algebra over A                                 *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Reserved Notation "{ 'algebra' T }" (at level 0, format "{ 'algebra'  T }").

Import GRing.Theory.

(* Finite dimensional algebra *)
Module AlgFType.

Section ClassDef.
Variable R : ringType.
Implicit Type phR : phant R.

Structure class_of (A : Type) : Type := Class {
  base1 : GRing.Algebra.class_of R A;
   mixin : VectorType.mixin_of (GRing.Lmodule.Pack _ base1 A)
}.
Local Coercion base1 : class_of >-> GRing.Algebra.class_of.
Local Coercion mixin : class_of >-> VectorType.mixin_of.
Definition base2 A (c : class_of A) := @VectorType.Class _ _ c c.
Local Coercion base2 : class_of >-> VectorType.class_of.

Structure type phR: Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):=
  let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.

Definition pack phR A A0 (m0 : VectorType.mixin_of (@GRing.Lmodule.Pack R _ A A0 A)) :=
  fun bT b & phant_id (@GRing.Algebra.class _ phR bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class A b m) A.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition zmodType phR cT := GRing.Zmodule.Pack (@class phR cT) cT.
Definition lmodType phR cT := GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition ringType phR cT := GRing.Ring.Pack (@class phR cT) cT.
Definition lalgType phR cT := GRing.Lalgebra.Pack phR (@class phR cT) cT.
Definition algType phR cT := GRing.Algebra.Pack phR (@class phR cT) cT.
Definition vectType phR  cT := VectorType.Pack phR (@class phR cT) cT.

Definition vector_ringType phR  cT :=
  @VectorType.Pack R phR  (GRing.Ring.sort (@ringType phR cT)) 
    (class cT) (GRing.Ring.sort (ringType cT)).

End ClassDef.

Module Exports.

Coercion base1 : class_of >-> GRing.Algebra.class_of.
Coercion mixin : class_of >-> VectorType.mixin_of.
Coercion base2 : class_of >-> VectorType.class_of.
Coercion eqType : type >->  Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion lmodType : type>->  GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Coercion vectType : type >-> VectorType.type.
Canonical Structure vectType.
Canonical Structure vector_ringType.
Bind Scope ring_scope with sort.
Notation algFType R := (@type _ (Phant R)).
Notation AlgFType R m :=
   (@pack _ (Phant R) _ _ m _ _ id _ id).

End Exports.

End AlgFType.
Import AlgFType.Exports.



Section algFTypeTheory.

Variable R: comRingType. 

Definition matrixAlgFType n := AlgFType R (matrixVectMixin R n.+1 n.+1).

End algFTypeTheory.

Canonical Structure matrixAlgFType.

Section AlgebraDef.
Variable (K : fieldType) (A : algFType K).
Implicit Type u v : A.
Implicit Type vs : {vspace A}.

Definition amull u: 'End(A) := lapp_of_fun ( *%R u).
Local Notation "\*l a" := (amull a) (at level 10): vspace_scope.

Lemma amull_linear_p : forall u, linear ( *%R u).
Proof. by move=> u k v w; rewrite mulr_addr scaler_mulr. Qed.
Canonical Structure amull_linear u := Linear (amull_linear_p u).

Definition amulr u: 'End(A) := lapp_of_fun ( *%R^~ u).
Local Notation "\*r a" := (amulr a) (at level 10): vspace_scope.

Lemma amulr_linear_p : forall u, linear ( *%R^~ u).
Proof. by move=> u k v w; rewrite mulr_addl scaler_mull. Qed.
Canonical Structure amulr_linear u := Linear (amulr_linear_p u).

Lemma size_prodv : forall vs1 vs2: {vspace A},
  size (allpairs ( *%R) (vbasis vs1) (vbasis vs2)) == (\dim vs1 * \dim vs2)%N.
Proof. by move=> *; rewrite size_allpairs !size_tuple. Qed.

Definition prodv vs1 vs2: {vspace A} := span (Tuple (size_prodv vs1 vs2)).

Local Notation "A * B" := (prodv A B) : vspace_scope.

Lemma memv_prod : forall vs1 vs2 a b, a \in vs1 -> b \in vs2 -> a * b \in (vs1 * vs2)%VS.
Proof.
move=> vs1 vs2 a b Hvs1 Hvs2.
rewrite (coord_basis Hvs1) (coord_basis Hvs2).
rewrite -mulr_suml; apply: memv_suml => i _.  
rewrite -mulr_sumr; apply: memv_suml => j _.
rewrite -scaler_mull -scaler_mulr scalerA memvZl //.
apply: memv_span; apply/allpairsP; exists ((vbasis vs1)`_i,(vbasis vs2)`_j).
by rewrite !mem_nth // size_tuple.
Qed.

Lemma prodvP : forall vs1 vs2 vs3,
  reflect (forall a b, a \in vs1 -> b \in vs2 -> a * b \in vs3)
          (vs1 * vs2 <= vs3)%VS.
Proof.
move=> vs1 vs2 vs3; apply: (iffP idP).
  move=> Hs a b Ha Hb; apply: subv_trans Hs; exact: memv_prod.
move=> Ha; apply/subvP=> v.
move/coord_span->; apply: memv_suml => i _.
apply: memvZl=> /=.
set u := allpairs _ _ _.
have: i < size u by rewrite (eqP (size_prodv _ _)).
move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
by apply Ha; apply: memv_basis.
Qed.

Lemma prodv_inj : forall (x y : A), (x * y)%:VS = (x%:VS * y%:VS)%VS.
Proof.
move => x y.
apply: subv_anti.
apply/andP; split.
 by apply: memv_prod; rewrite memv_inj.
apply/prodvP => a b.
case/injvP => ca ->.
case/injvP => cb ->.
by rewrite -scaler_mulr -scaler_mull !memvZ memv_inj !orbT.
Qed.

Lemma dimv1: \dim (1%:VS: {vspace A}) = 1%N.
Proof. by rewrite dim_injv GRing.nonzero1r. Qed.

Lemma dim_prodv : forall vs1 vs2,
 \dim (vs1 * vs2) <= \dim vs1 * \dim vs2.
Proof.
move => vs1 vs2.
by rewrite (leq_trans (dim_span _)) // size_allpairs !size_tuple.
Qed.

Lemma vnonzero1r:  (1%:VS) != ((0: A)%:VS) :> {vspace A}.
Proof. by apply/eqP=> HH; move/eqP: dimv1; rewrite HH dimv0=> HH1. Qed.

Lemma vbasis1: exists k, k != 0 /\ 
                  vbasis (1%:VS: {vspace A}) = [:: k *: 1] :> seq _.
Proof.
rewrite /vbasis dim_injv GRing.nonzero1r /=.
case/injvP: (@memv_pick _ A (1%:VS))=> k Hk.
exists k; split; last by rewrite Hk.
apply/eqP=> H; case/negP: vnonzero1r.
by move/eqP: Hk; rewrite H scale0r vpick0.
Qed.

Lemma prod0v: left_zero (0%:VS) prodv.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/prodvP=> a b; case/injvP=> k1 -> Hb.
by rewrite scaler0 mul0r mem0v.
Qed.

Lemma prodv0: right_zero (0%:VS) prodv.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/prodvP=> a b Ha; case/injvP=> k1 ->.
by rewrite scaler0 mulr0 mem0v.
Qed.

Lemma prod1v: left_id (1%:VS) prodv.
Proof.
case: vbasis1=> k [Hk He] /=.
move=> vs; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b; case/injvP=> k1 -> Hb.
  by rewrite -scaler_mull mul1r memvZl.
apply/subvP=> v Hv.
rewrite (coord_basis Hv); apply: memv_suml => i _ /=.
rewrite memvZ -[_`_i]mul1r memv_prod ?(orbT, memv_inj) //.
by apply: memv_basis; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma prodv1: right_id (1%:VS) prodv.
Proof.
case: vbasis1=> k [Hk He] /=.
move=> vs; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b Ha; case/injvP=> k1 ->.
  by rewrite -scaler_mulr mulr1 memvZl.
apply/subvP=> v Hv; rewrite (coord_basis Hv).
apply: memv_suml => i _ /=.
rewrite memvZ -[_`_i]mulr1 memv_prod ?(orbT, memv_inj) //.
by apply: memv_basis; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma prodvA: associative prodv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP.
split; apply/prodvP=> a b Ha Hb.
  rewrite (coord_basis Ha) -mulr_suml.
  apply: memv_suml => i _ /=.
  move/coord_span: Hb->; rewrite -mulr_sumr.  
  apply: memv_suml => j _ /=.
  rewrite -scaler_mull -scaler_mulr scalerA memvZl //.
  set u := allpairs _ _ _.
  have: j < size u by rewrite (eqP (size_prodv _ _)).
  move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
  by rewrite mulrA !memv_prod // ?memv_basis // mem_nth // size_tuple.
move/coord_span: Ha->; rewrite (coord_basis Hb).
rewrite -mulr_suml; apply: memv_suml => i _ /=.  
rewrite -mulr_sumr; apply: memv_suml => j _ /=.
rewrite -scaler_mull -scaler_mulr scalerA memvZl //.
set u := allpairs _ _ _; have: i < size u by rewrite (eqP (size_prodv _ _)).
move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
by rewrite -mulrA !memv_prod // ?memv_basis // mem_nth // size_tuple.
Qed.

Lemma prodv_monol : forall vs vs1 vs2, (vs1 <= vs2 -> vs1 * vs <= vs2 * vs)%VS.
Proof.
move=> vs vs1 vs2 Hvs; apply/prodvP=> a b Ha Hb; apply: memv_prod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma prodv_monor : forall vs vs1 vs2, (vs1 <= vs2 -> vs * vs1 <= vs * vs2)%VS.
Proof.
move=> vs vs1 vs2 Hvs; apply/prodvP=> a b Ha Hb; apply: memv_prod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma prodv_addl: left_distributive prodv addv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b;case/memv_addP=> v1 [v2 [Hv1 Hv2 ->]] Hb.
  by rewrite mulr_addl; apply: memv_add; apply: memv_prod.
apply/subvP=> v;  case/memv_addP=> v1 [v2 [Hv1 Hv2 ->]].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: prodv_monol; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: prodv_monol; exact: addvSr.
Qed.

Lemma prodv_addr: right_distributive prodv addv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b Ha;case/memv_addP=> v1 [v2 [Hv1 Hv2 ->]].
  by rewrite mulr_addr; apply: memv_add; apply: memv_prod.
apply/subvP=> v;  case/memv_addP=> v1 [v2 [Hv1 Hv2 ->]].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: prodv_monor; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: prodv_monor; exact: addvSr.
Qed.

(* Building the predicate that checks is a vspace has a unit *)
Let size_feq : forall vs T (f1 f2: _ -> T) (b := vbasis vs),
 size (val [ffun i : 'I_(\dim vs) => f1 b`_i] ++
       val [ffun i: 'I_(\dim vs)  => f2 b`_i]) == (\dim vs + \dim vs)%N.
Proof.
by move=> vs T f1 f2; rewrite /= size_cat // !size_tuple card_ord.
Qed.
Let feq vs T (f1 f2: _ -> T) := Tuple (size_feq vs f1 f2).

Let feq_lshift : forall vs T (f1 f2 : _ -> T) (i : 'I_(\dim vs)),
   let b := vbasis vs in 
  tnth (feq vs f1 f2) (lshift _ i) = f1 b`_i.
Proof.
move=> vs T f1 f2 i b.
rewrite /tnth /= !fgraph_map nth_cat /=.
rewrite size_map -cardT card_ord  (ltn_ord i).
by rewrite map_ffun_enum // nth_fgraph_ord ffunE -tnth_nth.
Qed.

Let feq_rshift : forall vs T (f1 f2: _ -> T) i,
   let b := vbasis vs in 
  tnth (feq vs f1 f2) (rshift _ i) = f2 b`_i.
Proof.
move=> vs T f1 f2 i b.
rewrite /tnth /= !fgraph_map nth_cat /=.
rewrite size_map -cardT card_ord ltnNge leq_addr /= addKn.
by rewrite map_ffun_enum // nth_fgraph_ord ffunE -tnth_nth.
Qed.

Definition has_aunit vs := 
  (\dim vs != 0)%N && 
  vsolve_eq (feq vs ( *%R) (fun x => *%R^~ x)) (feq vs id id) vs.

Lemma has_aunitP : forall vs,
  reflect
   (exists u, 
     [/\ u \in vs, u != 0 & forall x, x \in vs -> u * x = x /\ x = x * u])
   (has_aunit vs).
Proof.
pose f := fun x: A => *%R^~ x.
move=> vs; apply: (iffP andP).
  case=> Hd; case/vsolve_eqP=> /=.
    move=> i.
    rewrite -[i]splitK /unsplit; case: split=> o.
    rewrite (feq_lshift ( *%R) f); exact: linearP.
    by rewrite (feq_rshift ( *%R) f); exact: (linearP (amulr_linear _)).
  move=> u [H1u H2u]; exists u; rewrite H1u.
  suff Hu: forall x : A, x \in vs -> u * x = x /\ x = x * u.
    split=> //; apply/eqP=> Hu0.
    case: (Hu _ (memv_pick vs)); rewrite Hu0 mul0r.
    move/(@sym_equal _ _ _); move/eqP; rewrite vpick0 -dimv_eq0.
    by move=> Hnd; case/negP: Hd.
  move=> x; move/coord_basis->.
  rewrite linear_sum -mulr_suml; split; apply eq_bigr=> i /= _.
    rewrite linearZ /=.
    move: (H2u (rshift _ i)).
    by rewrite (feq_rshift ( *%R) f) (feq_rshift id id) /f => ->.
  rewrite -scaler_mull /=.
  move: (H2u (lshift _ i)).
  by rewrite (feq_lshift ( *%R) f) (feq_lshift id id) /f => ->.
case=> u [H1u H2u H3u]; split.
  apply/negP; rewrite dimv_eq0=> Hd.
  by case/negP: H2u; rewrite -memv0 -(eqP Hd).
apply/vsolve_eqP.
  move=> i.
  rewrite -[i]splitK /unsplit; case: split=> o.
    rewrite (feq_lshift ( *%R) f); exact: linearP.
  by rewrite (feq_rshift ( *%R) f); exact: (linearP (amulr_linear _)).
exists u; split=> // i.
rewrite -[i]splitK /unsplit; case: split=> o.
  rewrite (feq_lshift ( *%R) f) (feq_lshift id id).
  case (H3u (vbasis vs)`_o)=> //=.
  by apply: memv_basis; apply: mem_nth; rewrite size_tuple.
rewrite (feq_rshift ( *%R) f) (feq_rshift id id).
case (H3u (vbasis vs)`_o)=> //=.
by apply: memv_basis; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma has_aunit1 : forall vs, 1 \in vs -> has_aunit vs.
Proof.
move=> vs Hvs; apply/has_aunitP.
exists 1; split=> //; first exact: nonzero1r.
by move=> *; rewrite !(mulr1, mul1r).
Qed.
  
Structure aspace : Type := ASpace {
    a2vs :> {vspace A};
    _ : ((has_aunit a2vs) && (a2vs * a2vs <= a2vs))%VS 
}.

Definition aspace_of of phant A := aspace.
Local Notation "{ 'algebra' T }" := (aspace_of (Phant T)) : type_scope.

Canonical Structure aspace_subType :=
  Eval hnf in [subType for a2vs by aspace_rect].
Canonical Structure aspace_eqMixin := [eqMixin of aspace by <:].
Canonical Structure aspace_eqType := Eval hnf in EqType aspace aspace_eqMixin.
Definition aspace_choiceMixin := [choiceMixin of aspace by <:].
Canonical Structure aspace_choiceType :=
  Eval hnf in ChoiceType aspace aspace_choiceMixin.

Canonical Structure aspace_of_subType := Eval hnf in [subType of {algebra A}].
Canonical Structure aspace_of_eqType := Eval hnf in [eqType of {algebra A}].
Canonical Structure aspace_for_choiceType :=  Eval hnf in [choiceType of {algebra A}].

(* Canonical Structure apredType :=  *)
(*   mkPredType (fun (al: {algebra A}) (a: A) => (a%:VS <= al)%VS). *)

Implicit Type gs: {algebra A}.

Lemma aunit_eproof : forall gs, 
  let b := vbasis gs in
  exists u, 
    (u \in gs) &&
    forallb i : 'I_(\dim gs), (b`_i * u == b`_i) && (u * b`_i == b`_i).
Proof.
move=> gs b.
have: has_aunit gs by case: {b}gs=> vs /=; case/andP.
pose f := fun x: A => *%R^~ x.
case/andP=> _; case/vsolve_eqP=> /=; last first.
  move=> u [H1x H2x]; exists u; rewrite H1x.
  apply/forallP=> i.
  move: (H2x (lshift _ i)) (H2x (rshift _ i)).
  rewrite (feq_lshift ( *%R) f) (feq_lshift id id)=> ->.
  rewrite (feq_rshift ( *%R) f) (feq_rshift id id) /f => ->.
  by rewrite eqxx.
move=> i.
rewrite -[i]splitK /unsplit; case: split=> o.
  rewrite (feq_lshift ( *%R) f); exact: linearP.
rewrite (feq_rshift ( *%R) f); exact: (linearP (amulr_linear _)).
Qed.

Definition aunit gs := xchoose (aunit_eproof gs).

Lemma memv_unit : forall gs, aunit gs \in gs.
Proof.
by move=> gs; case/andP: (xchooseP (aunit_eproof gs)).
Qed.

Lemma aunitl : forall gs, forall x, x \in gs -> (aunit gs) * x = x.
Proof.
move=> gs x Hx; case/andP: (xchooseP (aunit_eproof gs))=> H1a H2a.
move/coord_basis: Hx->.
rewrite linear_sum; apply eq_bigr=> i /= _.
rewrite linearZ /=; congr (_ *: _).
move/forallP: H2a.
by move/(_ i); case/andP=> _; move/eqP->.
Qed.

Lemma aunitr : forall gs, forall x, x \in gs -> x * (aunit gs) = x.
Proof.
move=> gs x Hx; case/andP: (xchooseP (aunit_eproof gs))=> H1a H2a.
move/coord_basis: Hx->.
rewrite -mulr_suml; apply eq_bigr=> i /= _.
rewrite -scaler_mull.
by move/forallP: H2a;move/(_ i); case/andP; move/eqP->.
Qed.

Lemma aunit1 : forall gs, (aunit gs == 1) = (1 \in gs).
Proof.
move=> gs; apply/eqP/idP=> H; first by rewrite -H memv_unit.
by move: (aunitr H); rewrite mul1r.
Qed.

Lemma anonzero1r : forall gs, aunit gs != 0.
Proof.
move=> gs; apply/eqP=> Eu0.
move: (aunitr (memv_pick gs)); rewrite Eu0 mulr0.
move/(@sym_equal _ _ _); move/eqP; rewrite vpick0 -dimv_eq0.
by apply/negP; case gs=> vs /=; case/andP; case/andP.
Qed.

Lemma aspace1_def: ((has_aunit (1%:VS)) && (1%:VS * 1%:VS <= 1%:VS))%VS.
Proof. 
rewrite prod1v subv_refl andbT.
apply/has_aunitP; exists 1; split; first by exact: memv_inj.
  exact: nonzero1r.
by move=> x; rewrite mul1r mulr1.
Qed.

Canonical Structure aspace1 : {algebra A} := (ASpace aspace1_def).

Lemma aspacef_def:
   ((has_aunit (fullv A)) && ((fullv A) * (fullv A) <= (fullv A)))%VS.
Proof. 
rewrite subvf andbT.
apply/has_aunitP; exists 1; split; first by exact: memvf.
  by exact: nonzero1r.
by move=> x; rewrite mul1r mulr1.
Qed.

Canonical Structure aspacef : {algebra A} := (ASpace aspacef_def).

Lemma asubv : forall gs, (gs * gs <= gs)%VS.
Proof. by case=> vs /=; case/andP. Qed.

Lemma memv_mul : forall gs x y,
  x \in gs -> y \in gs -> x * y \in gs.
Proof. by move => gs x y Hx Hy; move/prodvP: (asubv gs); apply. Qed.

Lemma aspace_cap_def : forall gs1 gs2, 
  aunit gs1 = aunit gs2 ->
  let gs := (gs1 :&: gs2)%VS in ((has_aunit gs) && (gs * gs <= gs))%VS.
Proof.
move=> gs1 gs2 Ha; apply/andP; split.
  apply/has_aunitP; exists (aunit gs1); split.
  - by rewrite memv_cap memv_unit Ha memv_unit.
  - by exact: anonzero1r.
  move=> x; rewrite  memv_cap; case/andP=> Hg _.
  by rewrite !(aunitl,aunitr). 
rewrite subv_cap; apply/andP; split.
  apply: (subv_trans (prodv_monol _ (capvSl _ _))).
  apply: (subv_trans (prodv_monor _ (capvSl _ _))).
  exact: asubv.
apply: (subv_trans (prodv_monol _ (capvSr _ _))).
apply: (subv_trans (prodv_monor _ (capvSr _ _))).
exact: asubv.
Qed.

Definition aspace_cap gs1 gs2 (u: aunit gs1 = aunit gs2): {algebra A} := 
  ASpace (aspace_cap_def u).

End AlgebraDef.

Notation "{ 'algebra' T }" := (aspace_of (Phant T)) : type_scope.
Notation "A * B" := (prodv A B) : vspace_scope.

Section SubAlgFType.

(* Turn a {algebra A} into a algType                                         *)
Variable (K : fieldType) (A: algFType K)  (als: {algebra A}).

Inductive suba_of : predArgType := Suba x & x \in als.
Definition sa_val u := let: Suba x _ := u in x.
Canonical Structure suba_subType :=
  Eval hnf in [subType for sa_val by suba_of_rect].
Definition suba_eqMixin := Eval hnf in [eqMixin of suba_of by <:].
Canonical Structure suba_eqType := Eval hnf in EqType suba_of suba_eqMixin.
Definition suba_choiceMixin := [choiceMixin of suba_of by <:].
Canonical Structure suba_choiceType :=
  Eval hnf in ChoiceType suba_of suba_choiceMixin.

Lemma subaP : forall u, sa_val u \in als.
Proof. exact: valP. Qed.
Lemma suba_inj : injective sa_val.
Proof. exact: val_inj. Qed.
Lemma congr_suba : forall u v, u = v -> sa_val u = sa_val v.
Proof. exact: congr1. Qed.

Definition suba_zero := Suba (mem0v als).
Definition suba_opp u := Suba (memvNr (subaP u)).
Definition suba_add u v := Suba (memvD (subaP u) (subaP v)).

Lemma suba_addA : associative suba_add.
Proof. by move=> u v w; apply: val_inj; exact: addrA. Qed.
Lemma suba_addC : commutative suba_add.
Proof. by move=> u v; apply: val_inj; exact: addrC. Qed.
Lemma suba_add0 : left_id suba_zero suba_add.
Proof. move=> u; apply: val_inj; exact: add0r. Qed.
Lemma suba_addN : left_inverse suba_zero suba_opp suba_add.
Proof. move=> u; apply: val_inj; exact: addNr. Qed.

Definition suba_zmodMixin := 
  GRing.Zmodule.Mixin suba_addA suba_addC suba_add0 suba_addN.
Canonical Structure suba_zmodType :=
  Eval hnf in ZmodType suba_of suba_zmodMixin.

Definition suba_scale k (u: suba_of) := Suba (memvZl k (valP u)).

Lemma suba_scaleA : forall k1 k2 u, 
  suba_scale k1 (suba_scale k2 u) = suba_scale (k1 * k2) u.
Proof. by move=> *; apply: val_inj; exact: scalerA. Qed.
Lemma suba_scale1 : left_id 1 suba_scale.
Proof. by move=> *; apply: val_inj; exact: scale1r. Qed.
Lemma suba_scale_addr : forall k, {morph (suba_scale k) : x y / x + y}.
Proof. by move=> k u v; apply: val_inj; exact: scaler_addr. Qed.
Lemma suba_scale_addl : forall u, {morph (suba_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> u k1 k2; apply: val_inj; exact: scaler_addl. Qed.

Definition suba_lmodMixin := 
  GRing.Lmodule.Mixin suba_scaleA suba_scale1 suba_scale_addr suba_scale_addl.
Canonical Structure suba_lmodType :=
  Eval hnf in LmodType K suba_of suba_lmodMixin.

Definition suba_v2rv (u: suba_of) :=
  \row_(j < \dim als) (coord (vbasis als) (sa_val u) j).

Lemma suba_v2rv_linear_proof: linear suba_v2rv.
Proof.
move=> k u1 v1; apply: val_inj.
congr mx_val; apply/matrixP=> i j /=.
by rewrite !mxE linearP !ffunE.
Qed.
Canonical Structure suba_v2rv_linear := Linear suba_v2rv_linear_proof.

Lemma suba_v2rv_bij: bijective suba_v2rv.
Proof.
pose v (r: 'rV_(\dim als)) :=
  \sum_(i < \dim als) (r 0 i *: (vbasis als)`_i).
have memv_vr: forall r, v r \in als.
  move=> r; apply: memv_suml=> i _; apply: memvZl.
  by apply: memv_basis; apply: mem_nth; rewrite size_tuple.
exists (fun r => Suba (memv_vr r)).
  move=> v1; apply: val_inj; rewrite /suba_v2rv /v.
  have F1: sa_val v1 \in als by case v1.
  by rewrite /= {2}(coord_basis F1); apply: eq_big=> // i _; rewrite mxE.
move=> v1; apply/rowP=> i.
rewrite /subvect_v2rv /v /=  mxE coord_sumE.
rewrite (bigD1 i) //= linearZ ffunE /=.
   rewrite (free_coordt _ _ (free_is_basis (is_basis_vbasis _)))
         eqxx [_ *: _]mulr1 big1 ?addr0 //.
move=> k.
rewrite linearZ ffunE (free_coordt _ _ (free_is_basis (is_basis_vbasis _))).
by move/(negPf)=> ->; rewrite [_ *: _]mulr0.
Qed.


Definition suba_VectMixin := VectMixin suba_v2rv_linear_proof suba_v2rv_bij.
Canonical Structure suba_vectType := VectType K suba_VectMixin.

Definition suba_one := Suba (memv_unit als).
Definition suba_mul u v := 
  Suba (subv_trans (memv_prod (subaP u) (subaP v)) (asubv _)).

Lemma suba_mulA : associative suba_mul.
Proof. by move=> u v w; apply: val_inj; exact: mulrA. Qed.
Lemma suba_mu1l : left_id suba_one suba_mul.
Proof. by move=> u; apply: val_inj; apply: aunitl; case: u. Qed.
Lemma suba_mul1 : right_id suba_one suba_mul.
Proof. by move=> u; apply: val_inj; apply: aunitr; case: u. Qed.
Lemma suba_mul_addl : left_distributive suba_mul suba_add.
Proof. move=> u v w; apply: val_inj; exact: mulr_addl. Qed.
Lemma suba_mul_addr : right_distributive suba_mul suba_add.
Proof. move=> u v w; apply: val_inj; exact: mulr_addr. Qed.
Lemma suba_nonzero1: suba_one != 0.
Proof. apply/val_eqP; apply/eqP; exact: anonzero1r. Qed.

Definition suba_ringMixin :=
  RingMixin suba_mulA suba_mu1l suba_mul1 suba_mul_addl 
            suba_mul_addr suba_nonzero1.

Canonical Structure suba_ringType :=
  Eval hnf in RingType suba_of suba_ringMixin.

Lemma suba_scale_mull: forall k (x y:suba_of),  k *: (x * y) = (k *: x) * y.
Proof. move=> u v w; apply: val_inj; exact: scaler_mull. Qed.

Canonical Structure suba_lalgType :=
  Eval hnf in  LalgType K suba_of suba_scale_mull.

Lemma suba_scale_mulr: forall k (x y: suba_of), k *: (x * y) = x * (k *: y).
Proof. move=> u v w; apply: val_inj; exact: scaler_mulr. Qed.

Canonical Structure suba_algType :=
  Eval hnf in  AlgType K suba_of suba_scale_mulr.

Canonical Structure suba_algFType := AlgFType K suba_VectMixin.

End SubAlgFType.

Module LApp.

Section LinearAppStruct.

(* Endomorphisms over V have an algebra structure as soon as dim V != 0 *)
Variable (R : comRingType) (V: vectType R).
Hypothesis dim_nz: (vdim V != 0)%N.

Canonical Structure algType := LApp.algType dim_nz.

Canonical Structure algFType :=
   Eval hnf in AlgFType R (linearMixin V V).
 
End LinearAppStruct.

End LApp.

Export AlgFType.Exports.

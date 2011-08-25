(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import ssralg finset fingroup morphism perm action.

(*****************************************************************************)
(* This file clones the entire ssralg hierachy for finite types; this allows *)
(* type inference to function properly on expressions that mix combinatorial *)
(* and algebraic operators (e.g., [set x + y | x, y <- A]).                  *)
(*   finZmodType, finRingType, finComRingType, finUnitRingType,              *)
(*   finComUnitRingType, finIdomType, finFieldType finLmodType,              *)
(*   finLalgType finAlgType finUnitAlgType                                   *)
(*      == the finite counterparts of zmodType, etc.                         *)
(* Note that a finFieldType is canonically decidable. All these structures   *)
(* can be derived using [xxxType of T] forms, e.g., if R has both canonical  *)
(* finType and ringType structures, then                                     *)
(*     Canonical Structure R_finRingType := Eval hnf in [finRingType of R].  *)
(* declares the derived finRingType structure for R. As the implementation   *)
(* of the derivation is somewhat involved, the Eval hnf normalization is     *)
(* strongly recommended.                                                     *)
(*   This file also provides direct tie-ins with finite group theory:        *)
(*  [baseFinGroupType of R for +%R] == the (canonical) additive group        *)
(*      [finGroupType of R for +%R]    structures for R                      *)
(*                         {unit R} == the type of units of R, which has a   *)
(*                                     canonical group structure.            *)
(*                           'U%act == the action by right multiplication of *)
(*                                     {unit R} on R, via FinRing.unit_act.  *)
(*                                     (This is also a group action.)        *)
(*****************************************************************************)

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FinRing.

Local Notation mixin_of T b := (Finite.mixin_of (EqType T b)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later 
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_choice : forall T, base_of T -> Choice.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, mixin_of T (to_choice b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T :=
  fun bT b & phant_id (base_class bT) b =>
  fun fT m & phant_id (Finite.class fT) (Finite.Class m) =>
  Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_choice base_sort].
Local Notation fin_ c := (@Finite.Class _ c c).
Local Notation do_pack pack T := (pack T _ _ id _ _ id).
Import GRing.Theory.

Definition groupMixin V := FinGroup.Mixin (@addrA V) (@add0r V) (@addNr V).
Local Notation base_group T vT fT :=
  (@FinGroup.PackBase T (groupMixin vT) (Finite.class fT)).
Local Notation fin_group B V := (@FinGroup.Pack B (@addNr V)).

Module Zmodule.

Section ClassDef.

Record class_of M :=
  Class { base : GRing.Zmodule.class_of M; mixin : mixin_of M base }.
Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Zmodule.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.

Definition join_finType := @Finite.Pack zmodType (fin_ class) cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Canonical Structure join_finType.
Notation finZmodType := type.
Notation "[ 'finZmodType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finZmodType'  'of'  T ]") : form_scope.
Coercion baseFinGroupType : type >-> FinGroup.base_type.
Canonical Structure baseFinGroupType.
Coercion finGroupType : type >-> FinGroup.type.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
Notation "[ 'baseFinGroupType' 'of' R 'for' +%R ]" :=
    (BaseFinGroupType R (groupMixin _))
  (at level 0, format "[ 'baseFinGroupType'  'of'  R  'for'  +%R ]")
    : form_scope.
Notation "[ 'finGroupType' 'of' R 'for' +%R ]" :=
    (@FinGroup.clone R _ (finGroupType _) id _ id)
  (at level 0, format "[ 'finGroupType'  'of'  R  'for'  +%R ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Section AdditiveGroup.

Variable U : finZmodType.
Implicit Types x y : U.

Lemma zmod1gE : 1%g = 0 :> U.                    Proof. by []. Qed.
Lemma zmodVgE : forall x, x^-1%g = - x.          Proof. by []. Qed.
Lemma zmodMgE : forall x y, (x * y)%g = x + y.   Proof. by []. Qed.
Lemma zmodXgE : forall n x, (x ^+ n)%g = x *+ n. Proof. by []. Qed.
Lemma zmod_mulgC : forall x y, commute x y.      Proof. exact: GRing.addrC. Qed.
Lemma zmod_abelian : forall A : {set U}, abelian A.
Proof. move=> A; apply/centsP=> x _ y _; exact: zmod_mulgC. Qed.

End AdditiveGroup.

Module Ring.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Ring.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Ring.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Ring.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition join_finType := @Finite.Pack ringType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack ringType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Ring.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Notation finRingType := type.
Notation "[ 'finRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finRingType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

Section Unit.

Variable R : finRingType.

Definition is_inv (x y : R) := (x * y == 1) && (y * x == 1).
Definition unit : pred R := fun x => existsb y, is_inv x y.
Definition inv x := odflt x (pick (is_inv x)).

Lemma mulVr : {in unit, left_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP=> _; move/eqP.
Qed.

Lemma mulrV : {in unit, right_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP; move/eqP.
Qed.

Lemma intro_unit : forall x y, y * x = 1 /\ x * y = 1 -> unit x.
Proof.
by move=> x y [yx1 xy1]; apply/existsP; exists y; rewrite /is_inv xy1 yx1 !eqxx.
Qed.

Lemma invr_out : {in predC unit, inv =1 id}.
Proof.
rewrite /inv => x nUx; case: pickP => // y invxy.
by case/existsP: nUx; exists y.
Qed.

Definition UnitMixin := GRing.UnitRing.Mixin mulVr mulrV intro_unit invr_out.

End Unit.

End Ring.
Import Ring.Exports.

Module ComRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.ComRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition join_finType := @Finite.Pack comRingType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack comRingType class cT.
Definition join_finRingType := @Ring.Pack comRingType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Notation finComRingType := FinRing.ComRing.type.
Notation "[ 'finComRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComRingType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.UnitRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.UnitRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.

Definition join_finType := @Finite.Pack unitRingType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack unitRingType class cT.
Definition join_finRingType := @Ring.Pack unitRingType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Notation finUnitRingType := FinRing.UnitRing.type.
Notation "[ 'finUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finUnitRingType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Section UnitsGroup.

Variable R : finUnitRingType.

Inductive unit_of (phR : phant R) := Unit (x : R) of GRing.unit x.
Bind Scope group_scope with unit_of.

Let phR := Phant R.
Local Notation uT := (unit_of phR).
Definition uval (u : uT) := let: Unit x _ := u in x.

Canonical Structure unit_subType := [subType for uval by @unit_of_rect phR].
Definition unit_eqMixin := Eval hnf in [eqMixin of uT by <:].
Canonical Structure unit_eqType := Eval hnf in EqType uT unit_eqMixin.
Definition unit_choiceMixin := [choiceMixin of uT by <:].
Canonical Structure unit_choiceType :=
  Eval hnf in ChoiceType uT unit_choiceMixin.
Definition unit_countMixin := [countMixin of uT by <:].
Canonical Structure unit_countType := Eval hnf in CountType uT unit_countMixin.
Canonical Structure unit_subCountType := Eval hnf in [subCountType of uT].
Definition unit_finMixin := [finMixin of uT by <:].
Canonical Structure unit_finType := Eval hnf in FinType uT unit_finMixin.
Canonical Structure unit_subFinType := Eval hnf in [subFinType of uT].

Definition unit1 := Unit phR (@GRing.unitr1 _).
Lemma unit_inv_proof : forall u : uT, GRing.unit (val u)^-1.
Proof. by move=> u; rewrite GRing.unitr_inv ?(valP u). Qed.
Definition unit_inv u := Unit phR (unit_inv_proof u).
Lemma unit_mul_proof : forall u v : uT, GRing.unit (val u * val v).
Proof. by move=> u v; rewrite (GRing.unitr_mulr _ (valP u)) ?(valP v). Qed.
Definition unit_mul u v := Unit phR (unit_mul_proof u v).
Lemma unit_muluA : associative unit_mul.
Proof. move=> u v w; apply: val_inj; exact: GRing.mulrA. Qed.
Lemma unit_mul1u : left_id unit1 unit_mul.
Proof. move=> u; apply: val_inj; exact: GRing.mul1r. Qed.
Lemma unit_mulVu : left_inverse unit1 unit_inv unit_mul.
Proof. move=> u; apply: val_inj; exact: GRing.mulVr (valP u). Qed.

Definition unit_GroupMixin := FinGroup.Mixin unit_muluA unit_mul1u unit_mulVu.
Canonical Structure unit_baseFinGroupType :=
  Eval hnf in BaseFinGroupType uT unit_GroupMixin.
Canonical Structure unit_finGroupType := Eval hnf in FinGroupType unit_mulVu.

Definition unit_act x (u : uT) := x * val u.
Lemma unit_actE : forall x u, unit_act x u = x * val u. Proof. by []. Qed.

Canonical Structure unit_action :=
  @TotalAction _ _ unit_act (@GRing.mulr1 _) (fun _ _ _ => GRing.mulrA _ _ _).
Lemma unit_is_groupAction : @is_groupAction _ R setT setT unit_action.
Proof.
move=> u _ /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= [_ u]GRing.mulr_addl.
Qed.
Canonical Structure unit_groupAction := GroupAction unit_is_groupAction.

End UnitsGroup.

Module Import UnitsGroupExports.
Bind Scope group_scope with unit_of.
Canonical Structure unit_subType.
Canonical Structure unit_eqType.
Canonical Structure unit_choiceType.
Canonical Structure unit_countType.
Canonical Structure unit_subCountType.
Canonical Structure unit_finType.
Canonical Structure unit_subFinType.
Canonical Structure unit_baseFinGroupType.
Canonical Structure unit_finGroupType.
Canonical Structure unit_action.
Canonical Structure unit_groupAction.
End UnitsGroupExports.

Module ComUnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComUnitRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := ComRing.Class (mixin c).
Definition base3 R (c : class_of R) := @UnitRing.Class R (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition finComRingType := ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition finUnitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.

Definition join_finType := @Finite.Pack comUnitRingType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack comUnitRingType class cT.
Definition join_finRingType := @Ring.Pack comUnitRingType class cT.
Definition join_finComRingType := @ComRing.Pack comUnitRingType class cT.
Definition join_finUnitRingType := @UnitRing.Pack comUnitRingType class cT.
Definition ujoin_finComRingType := @ComRing.Pack unitRingType class cT.
Definition cjoin_finUnitRingType := @UnitRing.Pack comRingType class cT.
Definition fcjoin_finUnitRingType := @UnitRing.Pack finComRingType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure ujoin_finComRingType.
Canonical Structure cjoin_finUnitRingType.
Canonical Structure fcjoin_finUnitRingType.
Notation finComUnitRingType := FinRing.ComUnitRing.type.
Notation "[ 'finComUnitRingType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finComUnitRingType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.IntegralDomain.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := ComUnitRing.Class (mixin c).
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition finComRingType := ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition finUnitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition finComUnitRingType := ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.

Definition join_finType := @Finite.Pack idomainType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack idomainType class cT.
Definition join_finRingType := @Ring.Pack idomainType class cT.
Definition join_finUnitRingType := @UnitRing.Pack idomainType class cT.
Definition join_finComRingType := @ComRing.Pack idomainType class cT.
Definition join_finComUnitRingType := @ComUnitRing.Pack idomainType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion base2 : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical Structure finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure join_finComUnitRingType.
Notation finIdomainType := FinRing.IntegralDomain.type.
Notation "[ 'finIdomainType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finIdomainType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition pack := gen_pack Pack Class GRing.Field.class.
Variable cT : type.
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition finComRingType := ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition finUnitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition finComUnitRingType := ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition finIdomainType := IntegralDomain.Pack class cT.
Definition fieldType := GRing.Field.Pack class cT.

Definition join_finType := @Finite.Pack fieldType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack fieldType class cT.
Definition join_finRingType := @Ring.Pack fieldType class cT.
Definition join_finUnitRingType := @UnitRing.Pack fieldType class cT.
Definition join_finComRingType := @ComRing.Pack fieldType class cT.
Definition join_finComUnitRingType := @ComUnitRing.Pack fieldType class cT.
Definition join_finIdomainType := @IntegralDomain.Pack fieldType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical Structure finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion finIdomainType : type >-> IntegralDomain.type.
Canonical Structure finIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical Structure fieldType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure join_finComUnitRingType.
Canonical Structure join_finIdomainType.
Notation finFieldType := FinRing.Field.type.
Notation "[ 'finFieldType' 'of' T ]" := (do_pack pack T)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End Field.
Import Field.Exports.

Section DecideField.

Variable F : Field.type.

Fixpoint sat e f :=
  match f with
  | GRing.Bool b => b
  | t1 == t2 => (GRing.eval e t1 == GRing.eval e t2)%bool
  | GRing.Unit t => GRing.unit (GRing.eval e t)
  | f1 /\ f2 => sat e f1 && sat e f2
  | f1 \/ f2 => sat e f1 || sat e f2
  | f1 ==> f2 => (sat e f1 ==> sat e f2)%bool
  | ~ f1 => ~~ sat e f1
  | ('exists 'X_k, f1) => (existsb x : F, sat (set_nth 0%R e k x) f1)
  | ('forall 'X_k, f1) => (forallb x : F, sat (set_nth 0%R e k x) f1)
  end%T.

Lemma decidable : GRing.DecidableField.axiom sat.
Proof.
move=> e f; elim: f e;
  try by move=> f1 IH1 f2 IH2 e /=; case IH1; case IH2; constructor; tauto.
- by move=> b e; exact: idP.
- by move=> t1 t2 e; exact: eqP.
- by move=> t e; exact: idP.
- by move=> f IH e /=; case: IH; constructor.
- by move=> i f IH e; apply: (iffP existsP) => [] [x fx]; exists x; exact/IH.
by move=> i f IH e; apply: (iffP forallP) => f_ x; exact/IH.
Qed.

Definition DecidableFieldMixin := DecFieldMixin decidable.

End DecideField.

Module DecField.

Section Joins.

Variable cT : Field.type.
Let class := Field.class cT.

Definition type := Eval hnf in DecFieldType cT (DecidableFieldMixin cT).
Definition finType := @Finite.Pack type (fin_ class) type.
Definition finZmodType := @Zmodule.Pack type class type.
Definition finRingType := @Ring.Pack type class type.
Definition finUnitRingType := @UnitRing.Pack type class type.
Definition finComRingType := @ComRing.Pack type class type.
Definition finComUnitRingType := @ComUnitRing.Pack type class type.
Definition finIdomainType := @IntegralDomain.Pack type class type.
Definition baseFinGroupType := base_group type finZmodType finZmodType.
Definition finGroupType := fin_group baseFinGroupType cT.

End Joins.

Module Exports.
Coercion type : Field.type >-> GRing.DecidableField.type.
Canonical Structure type.
Canonical Structure finType.
Canonical Structure finZmodType.
Canonical Structure finRingType.
Canonical Structure finUnitRingType.
Canonical Structure finComRingType.
Canonical Structure finComUnitRingType.
Canonical Structure finIdomainType.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
End Exports.

End DecField.

Module Lmodule.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Lmodule.class_of R M ; mixin : mixin_of M base }.
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition pack := gen_pack (Pack phR) Class (@GRing.Lmodule.class R phR).

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition lmodType := GRing.Lmodule.Pack phR class cT.
Definition join_finType := @Finite.Pack lmodType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack lmodType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Notation finLmodType R := (FinRing.Lmodule.type (Phant R)).
Notation "[ 'finLmodType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLmodType'  R  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Module Lalgebra.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Lalgebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Ring.Class (mixin c).
Definition base3 M (c : class_of M) := @Lmodule.Class _ _ (base c) (mixin c).
Local Coercion base : class_of >-> GRing.Lalgebra.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.
Local Coercion base3 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.Lalgebra.class R phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition lmodType := GRing.Lmodule.Pack phR class cT.
Definition finLmodType := Lmodule.Pack phR class cT.
Definition lalgType := GRing.Lalgebra.Pack phR class cT.

Definition join_finType := @Finite.Pack lalgType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack lalgType class cT.
Definition join_finLmodType := @Lmodule.Pack R phR lalgType class cT.
Definition join_finRingType := @Ring.Pack lalgType class cT.
Definition rjoin_finLmodType := @Lmodule.Pack R phR ringType class cT.
Definition ljoin_finRingType := @Ring.Pack lmodType class cT.
Definition fljoin_finRingType := @Ring.Pack finLmodType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Lalgebra.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion base3 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure rjoin_finLmodType.
Canonical Structure ljoin_finRingType.
Canonical Structure fljoin_finRingType.
Notation finLalgType R := (FinRing.Lalgebra.type (Phant R)).
Notation "[ 'finLalgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finLalgType'  R  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

Module Algebra.

Section ClassDef.

Variable R : ringType.

Record class_of M :=
  Class { base : GRing.Algebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Lalgebra.Class (mixin c).
Local Coercion base : class_of >-> GRing.Algebra.class_of.
Local Coercion base2 : class_of >->Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.Algebra.class R phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition countType := Countable.Pack (fin_ class) cT.
Definition finType := Finite.Pack (fin_ class) cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition finZmodType := Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition finRingType := Ring.Pack class cT.
Definition lmodType := GRing.Lmodule.Pack phR class cT.
Definition finLmodType := Lmodule.Pack phR class cT.
Definition lalgType := GRing.Lalgebra.Pack phR class cT.
Definition finLalgType := Lalgebra.Pack phR class cT.
Definition algType := GRing.Algebra.Pack phR class cT.

Definition join_finType := @Finite.Pack algType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack algType class cT.
Definition join_finRingType := @Ring.Pack algType class cT.
Definition join_finLmodType := @Lmodule.Pack R phR algType class cT.
Definition join_finLalgType := @Lalgebra.Pack R phR algType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Algebra.class_of.
Coercion base2 : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical Structure finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finLalgType.
Notation finAlgType R := (type (Phant R)).
Notation "[ 'finAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T)
  (at level 0, format "[ 'finAlgType'  R  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End Algebra.
Import Algebra.Exports.

Module UnitAlgebra.
 
Section ClassDef.

Variable R : unitRingType.
 
Record class_of M := 
  Class { base : GRing.UnitAlgebra.class_of R M ; mixin : mixin_of M base }. 
Definition base2 M (c : class_of M) := Algebra.Class (mixin c).
Definition base3 M (c : class_of M) := @UnitRing.Class _ (base c) (mixin c).

Local Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Local Coercion base2 : class_of >-> Algebra.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (cT : type phR).
Definition pack := gen_pack (Pack phR) Class (@GRing.UnitAlgebra.class R phR). 
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c. 

Definition eqType := Equality.Pack class cT. 
Definition choiceType := Choice.Pack class cT. 
Definition countType := Countable.Pack (fin_ class) cT. 
Definition finType := Finite.Pack (fin_ class) cT. 
Definition zmodType := GRing.Zmodule.Pack class cT. 
Definition finZmodType := Zmodule.Pack class cT. 
Definition ringType := GRing.Ring.Pack class cT. 
Definition finRingType := Ring.Pack class cT. 
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition finUnitRingType := UnitRing.Pack class cT. 
Definition lmodType := GRing.Lmodule.Pack phR class cT. 
Definition finLmodType := Lmodule.Pack phR class cT. 
Definition lalgType := GRing.Lalgebra.Pack phR class cT. 
Definition finLalgType := Lalgebra.Pack phR class cT. 
Definition algType := GRing.Algebra.Pack phR class cT. 
Definition finAlgType := Algebra.Pack phR class cT. 
Definition unitAlgType := GRing.UnitAlgebra.Pack phR class cT.

Definition join_finType := @Finite.Pack unitAlgType (fin_ class) cT.
Definition join_finZmodType := @Zmodule.Pack unitAlgType class cT.
Definition join_finRingType := @Ring.Pack unitAlgType class cT.
Definition join_finUnitRingType := @UnitRing.Pack unitAlgType class cT.
Definition join_finLmodType := @Lmodule.Pack R phR unitAlgType class cT.
Definition join_finLalgType := @Lalgebra.Pack R phR unitAlgType class cT.
Definition join_finAlgType := @Algebra.Pack R phR unitAlgType class cT.
Definition  ljoin_finUnitRingType := @UnitRing.Pack lmodType class cT.
Definition fljoin_finUnitRingType := @UnitRing.Pack finLmodType class cT.
Definition  njoin_finUnitRingType := @UnitRing.Pack lalgType class cT.
Definition fnjoin_finUnitRingType := @UnitRing.Pack finLalgType class cT.
Definition  ajoin_finUnitRingType := @UnitRing.Pack algType class cT.
Definition fajoin_finUnitRingType := @UnitRing.Pack finAlgType class cT.
Definition ujoin_finLmodType := @Lmodule.Pack R phR unitRingType class cT.
Definition ujoin_finLalgType := @Lalgebra.Pack R phR unitRingType class cT.
Definition ujoin_finAlgType := @Algebra.Pack R phR unitRingType class cT.

Definition baseFinGroupType := base_group cT zmodType finType.
Definition finGroupType := fin_group baseFinGroupType zmodType.
Definition join_baseFinGroupType := base_group zmodType zmodType finType.
Definition join_finGroupType := fin_group join_baseFinGroupType zmodType.

End ClassDef. 

Module Exports.
Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Coercion base2 : class_of >-> Algebra.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical Structure finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Coercion finAlgType : type >-> Algebra.type.
Canonical Structure finAlgType.
Coercion unitAlgType : type >-> GRing.UnitAlgebra.type.
Canonical Structure unitAlgType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finLalgType.
Canonical Structure join_finAlgType.
Canonical Structure ljoin_finUnitRingType.
Canonical Structure fljoin_finUnitRingType.
Canonical Structure njoin_finUnitRingType.
Canonical Structure fnjoin_finUnitRingType.
Canonical Structure ajoin_finUnitRingType.
Canonical Structure fajoin_finUnitRingType.
Canonical Structure ujoin_finLmodType.
Canonical Structure ujoin_finLalgType.
Canonical Structure ujoin_finAlgType.
Notation finUnitAlgType R := (type (Phant R)).
Notation "[ 'finUnitAlgType' R 'of' T ]" := (do_pack (@pack _ (Phant R)) T) 
  (at level 0, format "[ 'finUnitAlgType'  R  'of'  T ]") : form_scope.
Canonical Structure baseFinGroupType.
Canonical Structure finGroupType.
Canonical Structure join_baseFinGroupType.
Canonical Structure join_finGroupType.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Module Theory.

Definition zmod1gE := zmod1gE.
Definition zmodVgE := zmodVgE.
Definition zmodMgE := zmodMgE.
Definition zmodXgE := zmodXgE.
Definition zmod_mulgC := zmod_mulgC.
Definition zmod_abelian := zmod_abelian.
Definition unit_actE := unit_actE.

End Theory.

End FinRing.

Import FinRing.
Export Zmodule.Exports Ring.Exports ComRing.Exports.
Export UnitRing.Exports UnitsGroupExports ComUnitRing.Exports.
Export IntegralDomain.Exports Field.Exports DecField.Exports.    
Export Lmodule.Exports Lalgebra.Exports Algebra.Exports UnitAlgebra.Exports.

Notation "{ 'unit' R }" := (unit_of (Phant R))
  (at level 0, format "{ 'unit'  R }") : type_scope.
Notation "''U'" := (unit_action _) (at level 0) : action_scope.
Notation "''U'" := (unit_groupAction _) (at level 0) : groupAction_scope.


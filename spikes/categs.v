(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Add LoadPath "../theories/" as Ssreflect.
Require Import ssreflect ssrfun seq ssrbool ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Category.

(*all property definitions preexist in ssrfun *)

Record mixin_of (oT: Type) := Mixin {
  composition : (oT -> oT) -> (oT -> oT) -> (oT -> oT);
  _ : associative composition;
  identity : oT -> oT;
  _ : left_id identity composition;
  _ : right_id identity composition
}.


Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {
  sort;
  _ : class_of sort;
  _ : Type
}.

Local Coercion sort :
  type >-> Sortclass.

Variables (T:Type) (cT:type).
Definition class :=
  let: Pack _ c _ as cT' := cT
  return class_of cT' in c.
Definition pack c := @Pack T c T.
Definition clone :=
  fun c & cT -> T & phant_id (pack c) cT
  => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation catType := type.
Notation CatMixin := Mixin.
Notation CatType T m := (@Pack T m T).
Notation "[ 'catType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'catType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'catType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'catType'  'of'  T ]") : form_scope.
End Exports.

End Category.
Export Category.Exports.

Definition composition (cT:catType) := Category.composition (Category.class cT).
Definition identity (cT:catType) := Category.identity (Category.class cT).
Definition ob (cT:catType) := Category.sort (cT).

(* Naturally, this is just a toy example : with this architecture, we
could not even define the dual category, since we have only one instance
per type. If we wanted to do this seriously, we would adopt the trick of
defining categories on a specific arrow type, and require objects as their
identity arrows (used in Haskell's Data.Category). Or we would use
overlapping instances à la quote. Thankfully, this isn't really the
point. *)

(* the object = object maps between categories C and D*)

Implicit Types (sT tT : Type) (cT dT : catType).

Definition object_map sT tT := sT -> tT.
Definition arrow_map sT tT := (sT -> sT) -> (tT  -> tT).

(* We omit contravariance in this simple example, it can be defined a
   posteriori with a functor defined on C^{op} ... provided we have a
   category definition that lets you represent duality.
   *)

Definition covariant_map sT dT (Fo: object_map sT dT) (Fa: arrow_map sT dT) :=
  forall (f : sT -> sT) (x:sT), Fo (f (x)) = Fa(f) (Fo(x)).

Definition func_id cT dT (Fa : arrow_map cT dT) : Prop :=
  Fa(@identity cT) = (@identity dT).
Definition func_comp cT dT (Fa:arrow_map cT dT) :=
  forall (f g : cT -> cT), Fa (composition g f) = (composition (Fa g) (Fa f)).

Module Functor.

Section ClassDef.

Variables (cT dT: catType).

Record mixin_of (oM : object_map cT dT) := Mixin {
  aM : arrow_map cT dT;
  _ : covariant_map oM aM;
  _ : func_id aM;
  _ : func_comp aM
}.

Notation class_of := mixin_of.

(* The phantom forces the inference on source and target type*)

Structure map (phcd: phant (cT -> dT)) := Pack {
  apply : cT -> dT;
  _ : class_of apply;
  _ : cT -> dT
}.

Local Coercion apply :
  map >-> Funclass.

Variables (phCD : phant (cT-> dT)) (f g : cT -> dT) (cF : map phCD).
Definition class :=
  let: Pack _ c _ as cF' := cF
  return class_of cF' in c.
Definition clone fA of
  phant_id g (apply cF) & phant_id fA class := @Pack phCD f fA f.
Definition pack (fZ : mixin_of f) :=
 @Pack (Phant (cT -> dT)) f fZ f.

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Notation Functor fCD := (@pack _ _ _ fCD).
Notation "{ 'functor' fCD }" := (map (Phant fCD))
  (at level 0, format "{ 'functor'  fCD }").
Notation "[ 'functor' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'functor'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'functor' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'functor'  'of'  f ]") : form_scope.
End Exports.

End Functor.
Export Functor.Exports.

(* The functor coerces to its object map*)
Definition armap (cT dT:catType) :=
  [ fun F => Functor.aM (@Functor.class _ _ (Phant (cT -> dT)) F) ].

Implicit Arguments armap [cT dT].

Lemma fcovariance cT dT : forall (F:{functor cT -> dT}), covariant_map F (armap F).
Proof. by case=> F; case. Qed.

Lemma fidentity cT dT : forall (F:{functor cT -> dT}), func_id (armap F).
Proof. by case=> F; case. Qed.

Lemma fcomposition cT dT : forall (F:{functor cT -> dT}), func_comp (armap F).
Proof. by case => F; case. Qed.

Section IdentityFunctor.

Variable cT : catType.

Definition idmap := @id cT.

Lemma id_covariance : @covariant_map _ cT (idmap) id.
Proof. by []. Qed.

Lemma id_fidentity : @func_id cT cT id.
Proof. by []. Qed.

Lemma id_fcomposition : @func_comp cT cT id.
Proof. by []. Qed.

Canonical Structure identityFunctor := Functor
  (Functor.Mixin id_covariance id_fidentity id_fcomposition).

End IdentityFunctor.

Section CompFunctor.

Variables cT dT eT : catType.
Variables (F : {functor cT -> dT}) (G : {functor dT -> eT}).

Local Notation gof := (Functor.apply G \o Functor.apply F).
Local Notation arr_gof := (armap G \o armap F).

Lemma comp_covariance : covariant_map gof arr_gof.
Proof. by move=> f x /=; rewrite 2!fcovariance. Qed.

Lemma comp_fidentity : func_id arr_gof.
Proof. by rewrite /func_id /comp 2!fidentity. Qed.

Lemma comp_fcomposition : func_comp arr_gof.
Proof. by move=> f g; rewrite /comp 2!fcomposition. Qed.

Canonical Structure comp_functor := Functor
  (Functor.Mixin comp_covariance comp_fidentity comp_fcomposition).

End CompFunctor.

Module NatTrans.

(* the object = Mappings from objects in C to arrows in D *)

Section ClassDef.

Variables (cT dT : catType).
Variables (F G : {functor cT -> dT}).

Record mixin_of (phi : cT -> (dT -> dT)) := Mixin {
  _ : forall (f : cT -> cT) (x:cT),
    composition (phi (f x)) ((armap F) f) = composition ((armap G) f) (phi x)
}.

Notation class_of := mixin_of.

(* notations force the inference on both functors*)

Structure map  := Pack {
  apply : cT -> (dT -> dT);
  _ : class_of apply;
  _ : cT -> (dT -> dT)
}.

Local Coercion apply :
  map >-> Funclass.

Variables (phi nu : cT -> dT -> dT) (nFG : map).
Definition class :=
  let: Pack _ c _ as nFG' := nFG return class_of nFG' in c.
Definition clone fA of
  phant_id nu (apply nFG) & phant_id fA class := @Pack phi fA phi.
Definition pack (fZ : mixin_of phi) := @Pack phi fZ phi.

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Notation NaturalTransformation FGmixin :=
  (@pack _ _ _ _ FGmixin).
Notation "{ 'nattrans' fF ~> fG }" :=
  (map [functor of fF] [functor of fG])
  (at level 0, format "{ 'nattrans' fF ~> fG }").
Notation "[ 'natural' 'transformation' 'of' f 'as' g ]" :=
  (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'natural' 'transformation'  'of'  f  'as'  g ]")
  : form_scope.
Notation "[ 'natural' 'transformation' 'of' f ]" :=
  (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'natural' 'transformation'  'of'  f ]") : form_scope.

End Exports.

End NatTrans.
Export NatTrans.Exports.

(* Finally, adjunctions *)

Module Adjunction.

(* the object = one of the functors, since the definition is symmetric *)

Section ClassDef.

Variables (cT dT:catType).

Record mixin_of (F : {functor cT -> dT}) (G: {functor dT -> cT}) :=
  Mixin {
    unit : {nattrans (@idmap cT) ~> (G\o F)};
    counit : {nattrans (F\o G) ~> (@idmap dT)};
    _ : forall Y : dT,
      ((armap G \o counit) Y) \o ((unit \o G) Y) = (@idmap cT);
    _ : forall X : cT,
      ((counit \o F) X) \o ((armap F \o unit) X) = (@idmap dT)
  }.

Record class_of f (G: {functor dT -> cT}) := Class {
  base : Functor.mixin_of f;
  mixin : mixin_of (Functor base) G
}.

Structure map (phCD : phant (cT -> dT)) := Pack {
  apply : cT -> dT;
  unapply : {functor dT -> cT};
  _ : class_of apply unapply;
  _ : cT -> dT
}.

Local Coercion apply :
  map >-> Funclass.

Variables (phCD : phant (cT -> dT)) (f : cT -> dT) (G : {functor dT -> cT}).
Variables  (cF : map phCD).
Definition class :=
  let: Pack _ _ c _ as cF' := cF return (class_of cF' (unapply cF')) in c.
Definition clone fL of phant_id f (apply cF) & phant_id fL class :=
  @Pack phCD f G fL f.

Definition pack F G (m : mixin_of F G) :=
  fun b & phant_id (Functor.class F) b =>
    fun m0 & phant_id m0 m => Pack phCD (@Class f G b m0) f.

Definition functor := Functor (base class).

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Coercion base : class_of >-> Functor.mixin_of.
Coercion mixin : class_of >-> mixin_of.
Coercion functor : map >-> Functor.map.

Notation Adjunction m := (@pack _ _ _ _ _ _ m  _ id _ id).
Notation "{ 'adjunction' fCD }" := (@map _ _ (Phant fCD))
  (at level 0, format "{ 'adjunction'  fCD }").
Notation "[ 'adjunction' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'adjunction'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'adjunction' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'adjunction'  'of'  f ]") : form_scope.
End Exports.

End Adjunction.
Export Adjunction.Exports.

Section Test.
Variables (cT dT : catType).

Variable x : {adjunction (cT -> dT)}.

Variable f : cT -> dT.
Variable fm : Functor.mixin_of f.
Definition F := Functor fm.

Variable G : {functor cT -> dT}.
(* Variable m: Adjunction.mixin_of F G.

   Refused statically !
   F : {functor cT -> dT}
   G : {functor cT -> dT}


   The term "G" has type "{functor cT -> dT}" while it is expected to have type
   "{functor dT -> cT}".
*)
Variable U : {functor dT -> cT}.
Variable m : Adjunction.mixin_of F U.
Variable m': Adjunction.mixin_of G U.

Check (Adjunction m).

End Test.
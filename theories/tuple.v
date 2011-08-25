(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*****************************************************************************)
(* Tuples, i.e., lists with a fixed (known) length. We define:               *)
(*   n.-tuple T   : the type of n-tuples of elements of type T.              *)
(*   [tuple of s] : the tuple whose underlying sequence (value) is s, which  *)
(*                  must have a known size; specifically, Coq must be able   *)
(*                  to infer a tuple whose Canonical Projection is s, e.g.,  *)
(*     [tuple]            is the empty tuple, and                            *)
(*     [tuple x1; ..; xn] the explicit n.-tuple <x1; ..; xn>.                *)
(* As n.-tuple T coerces to seq t, all operations for seq (size, nth, ...)   *)
(* can be applied to t : n.-tuple T; we provide a few specialized instances  *)
(* when this avoids the need for a default value.                            *)
(*   tsize t      : the size of t (the n in n.-tuple T)                      *)
(*   tnth t i     : the i'th component of t, where i : 'I_n.                 *)
(*   [tnth t i]   : the i'th component of t, where i : nat.                  *)
(*   thead t      : the first element of t, when n is canonically positive.  *)
(* Most seq constructors (behead, cat, belast, take, drop, rot, map, ...)    *)
(* can be used to build tuples via the [tuple of s] construct.               *)
(*   Tuples are actually a subType of seq, and inherit all combinatorial     *)
(* structures, including the finType structure.                              *)
(*   Some useful lemmas and definitions:                                     *)
(*     tuple0 : [tuple] is the only 0.-tuple                                 *)
(*     tupleP : elimination view for n.+1.-tuple                             *)
(*     ord_tuple n : the n.-tuple of all i : 'I_n                            *)
(*****************************************************************************)

Section Def.

Variables (n : nat) (T : Type).

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

Canonical Structure tuple_subType :=
  Eval hnf in [subType for tval by tuple_of_rect].

Implicit Type t : tuple_of.

Definition tsize of tuple_of := n.

Lemma size_tuple : forall t, size t = n.
Proof. move=> f; exact: (eqP (valP f)). Qed.

Lemma tnth_default : forall t (i : 'I_n), T.
Proof. by case=> [[|//]]; move/eqP <-; case. Qed.

Definition tnth t i := nth (tnth_default t i) t i.

Lemma tnth_nth : forall x t i, tnth t i = nth x t i.
Proof. by move=> x t i; apply: set_nth_default; rewrite size_tuple. Qed.

Lemma map_tnth_enum : forall t, map (tnth t) (enum 'I_n) = t.
Proof.
move=> t; case def_t: {-}(val t) => [|x0 t'].
  by rewrite [enum _]size0nil // -cardE card_ord -(size_tuple t) def_t.
apply: (@eq_from_nth _ x0) => [|i]; rewrite size_map.
  by rewrite -cardE size_tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -cardE card_ord in lt_i_e.
by rewrite (nth_map (Ordinal lt_i_n)) // (tnth_nth x0) nth_enum_ord.
Qed.

Lemma eq_from_tnth : forall t1 t2, tnth t1 =1 tnth t2 -> t1 = t2.
Proof.
by move=> *; apply: val_inj; rewrite /= -!map_tnth_enum; exact: eq_map.
Qed.

Definition tuple t mkT : tuple_of :=
  mkT (let: Tuple _ tP := t return size t == n in tP).

Lemma tupleE : forall t, tuple (fun sP => @Tuple t sP) = t.
Proof. by case. Qed.

End Def.

Notation "n .-tuple" := (tuple_of n)
  (at level 2, format "n .-tuple") : type_scope.

Notation "{ 'tuple' n 'of' T }" := (n.-tuple T : predArgType)
  (at level 0, only parsing) : form_scope.

Notation "[ 'tuple' 'of' s ]" := (tuple (fun sP => @Tuple _ _ s sP))
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.

Notation "[ 'tnth' t i ]" := (tnth t (@Ordinal (tsize t) i (erefl true)))
  (at level 0, t, i at level 8, format "[ 'tnth'  t  i ]") : form_scope.

Canonical Structure nil_tuple T :=
   Tuple (erefl _ : @size T [::] == 0).
Canonical Structure cons_tuple n T x (t : n.-tuple T) :=
   Tuple (valP t : size (x :: t) == n.+1).

Notation "[ 'tuple' x1 ; .. ; xn ]" := [tuple of x1 :: .. [:: xn] ..]
  (at level 0, format "[ 'tuple' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Notation "[ 'tuple' ]" := [tuple of [::]]
  (at level 0, format "[ 'tuple' ]") : form_scope.

Section SeqTuple.

Variables (n : nat) (T rT : Type).
Notation tT := (n.-tuple T).

Lemma nseq_tupleP : forall x : T, size (nseq n x) == n.
Proof. by move=> x; rewrite size_nseq. Qed.
Canonical Structure nseq_tuple x := Tuple (nseq_tupleP x).

Lemma iota_tupleP : forall m, size (iota m n) == n.
Proof. by move=> m; rewrite size_iota. Qed.
Canonical Structure iota_tuple m := Tuple (iota_tupleP m).

Lemma behead_tupleP : forall t : tT, size (behead t) == n.-1.
Proof. by move=> t; rewrite size_behead size_tuple. Qed.
Canonical Structure behead_tuple t := Tuple (behead_tupleP t).

Lemma belast_tupleP : forall x (t : tT), size (belast x t) == n.
Proof. by move=> x t; rewrite size_belast size_tuple. Qed.
Canonical Structure belast_tuple x t := Tuple (belast_tupleP x t).

Lemma cat_tupleP : forall n1 n2 (t1 : n1.-tuple T) (t2 : n2.-tuple T),
  size (t1 ++ t2) == n1 + n2.
Proof. by move=> n1 n2 t1 t2; rewrite size_cat !size_tuple. Qed.
Canonical Structure cat_tuple n1 n2 t1 t2 := Tuple (@cat_tupleP n1 n2 t1 t2).

Lemma take_tupleP : forall m (t : tT), size (take m t) == minn m n.
Proof. by move=> m t; rewrite size_take size_tuple eqxx. Qed.
Canonical Structure take_tuple m t := Tuple (take_tupleP m t).

Lemma drop_tupleP : forall m (t : tT), size (drop m t) == n - m.
Proof. by move=> m t; rewrite size_drop size_tuple. Qed.
Canonical Structure drop_tuple m t := Tuple (drop_tupleP m t).

Lemma rev_tupleP : forall t : tT, size (rev t) == n.
Proof. by move=> t; rewrite size_rev size_tuple. Qed.
Canonical Structure rev_tuple t := Tuple (rev_tupleP t).

Lemma rot_tupleP : forall m (t : tT), size (rot m t) == n.
Proof. by move=> m t; rewrite size_rot size_tuple. Qed.
Canonical Structure rot_tuple m t := Tuple (rot_tupleP m t).

Lemma rotr_tupleP : forall m (t : tT), size (rotr m t) == n.
Proof. by move=> m t; rewrite size_rotr size_tuple. Qed.
Canonical Structure rotr_tuple m t := Tuple (rotr_tupleP m t).

Lemma map_tupleP : forall f (t : tT), @size rT (map f t) == n.
Proof. by move=> f t; rewrite size_map size_tuple. Qed.
Canonical Structure map_tuple f t := Tuple (map_tupleP f t).

Lemma scanl_tupleP : forall f x (t : tT), @size rT (scanl f x t) == n.
Proof. by move=> f x t; rewrite size_scanl size_tuple. Qed.
Canonical Structure scanl_tuple f x t := Tuple (scanl_tupleP f x t).

Lemma pairmap_tupleP : forall f x (t : tT), @size rT (pairmap f x t) == n.
Proof. by move=> f x t; rewrite size_pairmap size_tuple. Qed.
Canonical Structure pairmap_tuple f x t := Tuple (pairmap_tupleP f x t).

Lemma zip_tupleP :forall (T1 T2: Type) (t1 : n.-tuple T1) (t2 : n.-tuple T2),
 size (zip t1 t2) == n.
Proof. by move=> *; rewrite size1_zip !size_tuple. Qed.
Canonical Structure zip_tuple T1 T2 (t1 : n.-tuple T1) (t2 : n.-tuple T2) := 
  Tuple (zip_tupleP t1 t2).

Definition thead n (t : n.+1.-tuple T) := tnth t ord0.

Lemma tnth0 : forall x n (t : n.-tuple T), tnth [tuple of x :: t] ord0 = x.
Proof. by []. Qed.

Lemma theadE : forall x n (t : n.-tuple T), thead [tuple of x :: t] = x.
Proof. by []. Qed.

Lemma tuple0 : @all_equal_to (0.-tuple T) [tuple].
Proof. by move=> t; apply: val_inj; case: t => [[]]. Qed.

CoInductive tuple1_spec : n.+1.-tuple T -> Type :=
  Tuple1spec x (t : tT) : tuple1_spec [tuple of x :: t].

Lemma tupleP : forall t, tuple1_spec t.
Proof.
move=> [[|x t] //= sz_t]; pose t' := Tuple (sz_t : size t == n).
rewrite (_ : Tuple _ = [tuple of x :: t']) //; exact: val_inj.
Qed.

Lemma tnth_map : forall f (t : tT) i,
  tnth [tuple of map f t] i = f (tnth t i) :> rT.
Proof. by move=> f t i; apply: nth_map; rewrite size_tuple. Qed.

End SeqTuple.

Lemma tnth_behead : forall n T (t : n.+1.-tuple T) i,
  tnth [tuple of behead t] i = tnth t (inord i.+1).
Proof.
by move=> n T; case/tupleP=> x t i; rewrite !(tnth_nth x) inordK ?ltnS.
Qed.

Lemma tuple_eta : forall n T (t : n.+1.-tuple T),
  t = [tuple of thead t :: behead t].
Proof. move=> n T; case/tupleP=> x t; exact: val_inj. Qed.

Section EqTuple.

Variables (n : nat) (T : eqType).

Definition tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical Structure tuple_eqType :=
  Eval hnf in EqType (n.-tuple T) tuple_eqMixin.

Canonical Structure tuple_predType :=
  Eval hnf in mkPredType (fun t : n.-tuple T => mem_seq t).

Lemma memtE : forall t : n.-tuple T, mem t = mem (tval t).
Proof. by []. Qed.

End EqTuple.

Definition tuple_choiceMixin n (T : choiceType) :=
  [choiceMixin of n.-tuple T by <:].

Canonical Structure tuple_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (n.-tuple T) (tuple_choiceMixin n T).

Definition tuple_countMixin n (T : countType) :=
  [countMixin of n.-tuple T by <:].

Canonical Structure tuple_countType n (T : countType) :=
  Eval hnf in CountType (n.-tuple T) (tuple_countMixin n T).

Canonical Structure tuple_subCountType n (T : countType) :=
  Eval hnf in [subCountType of n.-tuple T].

Module Type FinTupleSig.
Section FinTupleSig.
Variables (n : nat) (T : finType).
Parameter enum : seq (n.-tuple T).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = #|T| ^ n.
End FinTupleSig.
End FinTupleSig.

Module FinTuple : FinTupleSig.
Section FinTuple.
Variables (n : nat) (T : finType).

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (map (fun x => map (cons x) e) (Finite.enum T)) in
  pmap insub (iter n extend [::[::]]).

Lemma enumP : Finite.axiom enum.
Proof.
case=> /= t t_n; rewrite -(count_map val (pred1 t)).
rewrite (pmap_filter (@insubK _ _ _)) count_filter -filter_predI -enumT.
rewrite -count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
elim: n t t_n => [|m IHm] [|x t] //=.
move/IHm; move: (iter m _ _) => em {IHm} IHm.
transitivity (x \in T : nat); rewrite // -mem_enum.
have:= enum_uniq T; rewrite enumT.
elim: (Finite.enum T) => //= y e IHe; case/andP; move/negPf=> ney.
rewrite count_cat count_map inE /preim /= {1}/eq_op /= eq_sym; move/IHe->.
by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IHm).
Qed.

Lemma size_enum : size enum = #|T| ^ n.
Proof.
rewrite /= cardE size_pmap_sub enumT; elim: n => //= m IHm.
rewrite expnS; elim: {2 3}(Finite.enum T) => //= x e IHe.
by rewrite count_cat {}IHe count_map IHm.
Qed.

End FinTuple.
End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).
Notation tT := (n.-tuple T).

Canonical Structure tuple_finMixin :=
  Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical Structure tuple_finType := Eval hnf in FinType tT tuple_finMixin.
Canonical Structure tuple_subFinType := Eval hnf in [subFinType of tT].

Lemma card_tuple : #|{:n.-tuple T}| = #|T| ^ n.
Proof. by rewrite [#|_|]cardT enumT unlock FinTuple.size_enum. Qed.

Lemma enum_tupleP : forall A : pred T, size (enum A) == #|A|.
Proof. by move=> A; rewrite -cardE. Qed.
Canonical Structure enum_tuple A := Tuple (enum_tupleP A).

Definition ord_tuple : n.-tuple 'I_n := Tuple (introT eqP (size_enum_ord n)).
Lemma val_ord_tuple : val ord_tuple = enum 'I_n. Proof. by []. Qed.

Lemma tuple_map_ord : forall T' (t : n.-tuple T'),
  t = [tuple of map (tnth t) ord_tuple].
Proof. by move=> T' t; apply: val_inj => /=; rewrite map_tnth_enum. Qed.

Lemma tnth_ord_tuple : forall i, tnth ord_tuple i = i.
Proof.
move=> i; apply: val_inj; rewrite (tnth_nth i) -(nth_map _ 0) ?size_tuple //.
by rewrite /= enumT unlock val_ord_enum nth_iota.
Qed.

End UseFinTuple.



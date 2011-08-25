(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool eqtype.

Lemma test (x : bool) : True.
have H1 x := x.
have (x) := x => H2.
have H3 T (x : T) := x.
have ? : bool := H1 _ x.
have ? : bool := H2 _ x.
have ? : bool := H3 _ x.
have ? (z : bool) : forall y : bool, z = z := fun y => refl_equal _.
have ? w : w = w := @refl_equal nat w.
have ? y : true by [].
have ? (z : bool) : z = z.
  exact: (@refl_equal _ z).
have ? (z w : bool) : z = z by exact: (@refl_equal _ z).
have H w (a := 3) (_ := 4) : w && true = w.
  by rewrite andbT.
Unset Automatic Introduction.
have ? w (a := 3) (_ := 4) : w && true = w.
  by move=> w _ _; rewrite andbT.
exact I.
Qed.

Lemma test1 : True.
suff (x : bool): x = x /\ True.
  by move/(_ true); case=> _.
move=> x; split; [ by [] | clear x].
Set Automatic Introduction.
suff (x : bool): x = x /\ True.
  by move/(_ true); case=> _.
split; first by exact: (@refl_equal _ x).
suff H y : y && true = y /\ True.
  by case: (H true).
suff H1 /= : true && true /\ True.
  by rewrite andbT; split; [exact: (@refl_equal _ y) | exact: I].
match goal with |- is_true true /\ True => idtac end.
by split.
Qed.
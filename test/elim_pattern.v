Require Import ssreflect ssrbool eqtype ssrnat.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Lemma test x : (x == x) = (x + x.+1 == 2 * x + 1).
case: (X in _ = X) / eqP => _.
match goal with |- (x == x) = true => admit end.
match goal with |- (x == x) = false => admit end.
Qed.

Lemma test1 x : (x == x) = (x + x.+1 == 2 * x + 1).
elim: (x in RHS).
match goal with |- (x == x) = _ => admit end.
match goal with |- forall n, (x == x) = _ -> (x == x) = _ => admit end.
Qed.


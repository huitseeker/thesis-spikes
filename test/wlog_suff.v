(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool.

Lemma test b : b || ~~b.
wlog _ : b / b = true.
  case: b; [ by apply | by rewrite orbC ].
wlog suff: b /  b || ~~b.
  by case: b.
by case: b.
Qed.
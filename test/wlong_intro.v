Require Import ssreflect ssrbool ssrnat.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Goal (forall x y : nat, True).
move=> x y.
wlog suff: x y / x <= y.
Admitted.

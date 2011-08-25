(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool.

Lemma test (a b : bool) (pab : a && b) : b.
have {pab} /= /andP [pa -> //] /= : true && (a && b) := pab.
Qed.

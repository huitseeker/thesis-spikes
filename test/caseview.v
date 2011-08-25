Require Import ssreflect.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Lemma test (A B : Prop) : A /\ B -> True.
Proof. by case=> _ /id _. Qed.
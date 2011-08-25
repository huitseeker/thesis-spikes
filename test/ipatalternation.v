(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect.

Lemma test1 : Prop -> Prop -> Prop -> Prop -> Prop -> True = False -> Prop -> True \/ True.
by move=> A /= /= /= B C {A} {B} ? _ {C} {1}-> *; right.
Qed.
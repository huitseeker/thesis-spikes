(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect.

Variable T : Type.

Lemma test0 : forall a b c d : T, True.
Proof. by move=> a b {a} a c; exact I. Qed.

Variable P : T -> Prop.

Lemma test1 : forall a b c : T, P a -> forall d : T, True.
Proof. move=> a b {a} a _ d; exact I. Qed.




Require Import ssreflect ssrbool ssrnat eqtype seq fintype zmodp.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Axiom P : forall T, seq T -> Prop.

Goal (forall T (s : seq T), P _ s).
move=> T s.
elim: s => [| x /lastP [| s] IH].
Admitted.

Goal forall x : 'I_1, x = 0 :> nat.
move=> /ord1 -> /=; exact: refl_equal.
Qed.

Goal forall x : 'I_1, x = 0 :> nat.
move=> x.
move=> /ord1 -> in x |- *.
exact: refl_equal.
Qed.

Require Import ssreflect ssrbool.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Lemma v : True -> bool -> bool. Proof. by []. Qed.

Reserved Notation " a -/ b " (at level 0).
Reserved Notation " a -// b " (at level 0).
Reserved Notation " a -/= b " (at level 0).
Reserved Notation " a -//= b " (at level 0).

Lemma test : forall a b c, a || b || c.
Proof.
move=> ---a--- - -/=- -//- -/=- -//=- b [|-].
move: {-}a => /v/v-H; have _ := H I I.
Fail move: {-}a {H} => /v-/v-H.
have - -> : a = a by [].
have --> : a = a by [].
have - - _ : a = a by [].
have -{1}-> : a = a by [].
  by admit.
move: a.
case: b => -[] //.
by admit.
Qed.

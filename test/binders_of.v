
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect seq.

Lemma test1 : True.
have f of seq nat & nat : nat.
  exact 3.
have g of nat := 3.
have h of nat : nat := 3.
have _ : f [::] 3 = g 3 + h 4.
  by admit.
by admit.
Qed.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require ssreflect.
Require Import Arith.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.

Section Foo.
Import ssreflect.SsrSyntax.

Goal (forall a b, a + b = b + a).
intros.
rewrite 2![_ + _]plus_comm. 
split.
Abort.
End Foo.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.
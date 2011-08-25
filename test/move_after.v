Require Import ssreflect.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Goal True -> True -> True.
move=> H1 H2.
move H1 after H2.
Admitted.

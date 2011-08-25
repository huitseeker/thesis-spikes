Require Import ssreflect ssrnat.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Goal 5 = 3.
Fail (rewrite -(addnK _ 5)).
Abort.
Require Import ssreflect ssrbool.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Goal forall x, x && true = x.
move=> x.
Fail (rewrite [X in _ && _]andbT).
Abort.

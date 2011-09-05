Require Import ssreflect ssrbool ssrnat.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Ltac SUFF1 h t := suff h x (p := x < 0) : t.
Ltac SUFF2 h t := suff h x (p := x < 0) : t by apply h.
Ltac HAVE1 h t u := have h x (p := x < 0) : t := u.
Ltac HAVE2 h t := have h x (p := x < 0) : t by [].
Ltac HAVE3 h t := have h x (p := x < 0) : t.
Ltac HAVES h t := have suff h : t.
Ltac SUFFH h t := suff have h : t.

Lemma foo z : z < 0.
SUFF1 h1 (z+1 < 0).
Undo.
SUFF2 h2 (z < 0).
Undo.
HAVE1 h3 (z = z) (refl_equal z).
Undo.
HAVE2 h4 (z = z).
Undo.
HAVE3 h5 (z < 0).
Undo.
HAVES h6 (z < 1).
Undo.
SUFFH h7 (z < 1).
Undo.
Admitted.



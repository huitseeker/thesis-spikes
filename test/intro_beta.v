Require Import ssreflect.
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

Axiom T : Type.

Definition C (P : T -> Prop) := forall x, P x.

Axiom P : T -> T -> Prop.

Lemma foo : C (fun x => forall y, let z := x in P y x).
move=> a b. 
match goal with |- (let y := _ in _) => idtac end.
admit.
Qed.

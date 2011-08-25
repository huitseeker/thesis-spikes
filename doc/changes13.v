(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool eqtype ssrnat fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* unfold expanding head constant of pattern *)
Definition double x := x + x.
Definition ddouble x := double (double x).
Lemma ex1 x : ddouble x = 4 * x. 
Proof. by rewrite [ddouble _]/double !mulSn addnA addn0. Qed.

(* contextual rewrite patterns *)
Axiom f : nat -> nat -> nat. 
Lemma ex2 x y z : (x.+1 + y) + f (x.+1 + y) (z + (x + y).+1) = 0.
Proof.
rewrite [in f _ _]addSn.
rewrite addSn -[X in _ = X]addn0.
rewrite -{2}[in X in _ = X](addn0 0).
rewrite [_.+1 in X in f _ X](addnC x.+1).
rewrite [x.+1 + y as X in f X _]addnC.
Admitted.

(* evars in rewrite *)
Lemma ex3 (x : 'I_2) y (le_1 : y < 1) (E : val x = y) : Some x = insub y.
Proof.
rewrite insubT ?(leq_trans le_1)// => le_2.
by congr (Some _); apply: val_inj=> /=; exact: E.
Qed.

(* evars in apply *)
Lemma ex4 y: 1 < y < 2 -> exists x : 'I_3, x > 0.
Proof.
case/andP=> y_gt1 y_lt2; apply: (ex_intro _ (@Ordinal _ y _)).
  by apply: leq_trans y_lt2 _.
by move=> y_lt3; apply: leq_trans _ y_gt1.
Qed.

(* deferred clear & views in have *)
Lemma ex5 y (y_le0 : y <= 0) : 2 + y = 2.
Proof.
have {y_le0 y} /eqP -> : y == 0 by rewrite eqn_leq y_le0 leq0n.
by rewrite addn0.
Qed.

(* multiple views *)
Lemma ex6 (P Q R : Prop) : P -> (R <-> P) -> (P -> (R <-> Q)) -> Q.
Proof. by move=> p rp rq; apply/rq/rp/p; exact: p. Qed.

(* view in intro patterns *)
Lemma ex7 A B C : A && B && C == true -> B.
Proof. by move=> /eqP /andP [/andP [_ ->] _]. Qed.

(* discharge modifiers *)
Lemma ex8 (n := 3) : n = 3.
Proof. by move: @n => m. Qed.

(* elim *)
Function plus (m n : nat) {struct n} : nat :=
   match n with
   | 0 => m
   | S p => S (plus m p)
   end.
Lemma ex9  x y z: plus (plus x y) z = plus x (plus y z).
Proof. by elim/plus_ind: {z}_ => //= _ z' _ ->. Qed.
Lemma ex10 x y z: plus (plus x y) z = plus x (plus y z).
Proof. by elim/plus_ind: {z}(plus _ _) => //= _ z' _ ->. Qed.
Lemma ex11 x y z: plus (plus x y) z = plus x (plus y z).
Proof. by elim/plus_ind: z / (plus _ z) => //= _ z' _ ->. Qed.




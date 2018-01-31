(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From mathcomp Require Import prime div cyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rather than the descriptive formulation of the contrib, we pick a *)
(* stronger formulation which consists in describing the key generation *)
(* process with less hypotheses.*)

Section RSA.
Variable p q : nat.
Variable prime_p : prime p.
Variable prime_q : prime q.
Variable neq_pq: p != q.

Local Notation n := (p * q).

(* Those two big primes are chosen for security reasons. See R. L. Rivest,
   A. Shamir, and L. Adleman.  A method for obtaining digital signatures
   and public-key cryptosystems. Communications of the ACM, 21
   (2):120–126, Feb. 1978. ISSN 00010782.  doi:10.1145/359340.359342

   We'll at least assume they are strictly greater than 2
   *)

Hypothesis big_p: 2 < p.
Hypothesis big_q: 2 < q.

(* We compute the totient of that product. *)

Lemma pq_coprime: coprime p q.
Proof. by rewrite prime_coprime // dvdn_prime2 //. Qed.

Lemma phi_prime : forall x, prime x -> totient x = x.-1.
Proof.
move=> x; move/totient_pfactor; move/(_ _ (ltn0Sn 0)).
by rewrite expn1 expn0 muln1.
Qed.

Lemma pq_phi: totient(n) = p.-1 * q.-1.
Proof.
rewrite totient_coprime; last by rewrite pq_coprime.
by rewrite !phi_prime //.
Qed.

(* We check that when n is not coprime to some x <= n, one of the two *)
(* primes of n divides x.*)

Lemma notcoprime: forall x, 0 < x < n -> ~~ (coprime x n) ->
  ((p %| x) && coprime x q) || ((q %| x) && coprime x p).
Proof.
move=> x; case/andP=>[x_gt0 x_lt_n]; rewrite coprime_mulr; move/nandP.
move/orP; rewrite coprime_sym [coprime _ q]coprime_sym 2?prime_coprime //.
case Hdvdn: (p %| x) =>/=; rewrite ?negbK ?andbF ?andbT // orbF=>_.
have xdpp_x: (x %/p) * p = x by move: (Hdvdn); rewrite dvdn_eq; move/eqP.
rewrite -xdpp_x; apply/negP=> H; move:H; rewrite (Euclid_dvdM _ _ prime_q).
rewrite [ _ %| p]dvdn_prime2 // eq_sym; move/negbTE: neq_pq=>->.
rewrite orbF=>H; move: (dvdn_mul (dvdnn p) H).
rewrite [_ * (_ %/ _)]mulnC xdpp_x; move/(dvdn_leq x_gt0).
by rewrite leqNgt x_lt_n.
Qed.

(*  We pick an exponent e coprime to phi(n) *)

Variable e : nat.
Hypothesis e_phin_coprime: coprime (totient n) e.

Definition d := (fst (egcdn e (totient n))).

(* We check that ed is 1 modulo (totient n) *)

Lemma ed_1_mod_phin: e * d = 1 %[mod (totient n)].
Proof.
by  rewrite -(chinese_modl e_phin_coprime 1 0) /chinese addn0 mul1n.
Qed.

(* Let's now check RSA*)

Definition encrypt (w : nat) := (w ^ e) %% n.

Definition decrypt (w : nat) := (w ^ d) %% n.

(* Of course, we chooose a sensible w s.t. w <= n*)

Theorem rsa_correct1 :
 forall w : nat, w <= n -> (decrypt (encrypt w)) = w %[mod n].
Proof.
move=> w w_leq_n; rewrite modn_mod modnXm -expnM.
have phi_gt1 : 1 < (totient n); first rewrite pq_phi -(muln1 1).
  by apply: ltn_mul; rewrite -ltnS prednK ?big_p ?big_q ?prime_gt0.
have ed_gt0: 0 < e * d.
  have:= (divn_eq (e*d) (totient n)); rewrite ed_1_mod_phin => ->.
  by rewrite [_ * totient n]mulnC (modn_small phi_gt1) addnS lt0n.
case w_gt0: (0 < w); last first.
  move/negbT: w_gt0; rewrite lt0n; move/negPn; move/eqP=>->.
  by rewrite exp0n ?ltn_addl // ?modn_small.
have:= (divn_eq (e*d) (totient n)); rewrite ed_1_mod_phin modn_small // =>->.
(* The interesting case *)
case cp_w_n : (coprime w n).
  rewrite expnD [_ * totient n]mulnC expnM -modnMm; move: cp_w_n.
  by move/Euler_exp_totient=>E; rewrite -modnXm E modnXm exp1n modnMm mul1n.
(* The degenerate case where w,n are not coprime*)
case w_eq_n: (w == n).
   by move/eqP: w_eq_n =>->; rewrite -modnXm modnn exp0n ?mod0n ?addn1.
move: w_leq_n; rewrite leq_eqVlt {}w_eq_n orFb; move=> w_lt_n.
apply/eqP; rewrite chinese_remainder; last first.
  by rewrite prime_coprime // dvdn_prime2.
rewrite mulnC {1 3}pq_phi {2}[_ * q.-1]mulnC -2!mulnA 2!expnD expnM.
rewrite [w ^ ( q.-1 * _ )]expnM expn1 -modnMm -(modnMm _ _ q).
rewrite -modnXm -(modnXm _ q); move/andP: (conj (idP w_gt0) w_lt_n).
move/notcoprime; move/(_ (negbT cp_w_n)); case/orP; move/andP=> [Hdvdn Hncp].
  move: Hdvdn; rewrite /dvdn; move/eqP=>->; rewrite muln0 mod0n /=.
  move/Euler_exp_totient:Hncp; rewrite (phi_prime prime_q)=>->.
  by rewrite modnXm exp1n modnMm mul1n.
move: Hdvdn; rewrite /dvdn; move/eqP=>->; rewrite muln0 mod0n /= andbT.
move/Euler_exp_totient:Hncp; rewrite (phi_prime prime_p)=>->.
by rewrite modnXm exp1n modnMm mul1n.
Qed.

End RSA.

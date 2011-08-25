(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq choice fintype.
Require Import finfun bigop.

(******************************************************************************)
(* This file defines a type for sets over a finite Type, similar to the type  *)
(* of functions over a finite Type defined in finfun.v (indeed, based in it): *)
(*  {set T} where T must have a finType structure                             *)
(* We equip {set T} itself with a finType structure, hence Leibnitz and       *)
(* extensional equalities coincide on {set T}, and we can form {set {set T}}  *)
(*   If A, B : {set T} and P : {set {set T}}, we define:                      *)
(*           x \in A == x belongs to A (i.e., {set T} implements predType,    *)
(*                      by coercion to pred_sort).                            *)
(*             mem A == the predicate corresponding to A.                     *)
(*          finset p == the A corresponding to a predicate p.                 *)
(*       [set x | C] == the A containing the x such that C holds (x is bound  *)
(*                      in C).                                                *)
(*     [set x \in D] == the A containing the x in the collective predicate D. *)
(* [set x \in D | C] == the A containing the x in D such that C holds.        *)
(*              set0 == the empty set.                                        *)
(*  [set: T] or setT == the full set (the A containing all x : T).            *)
(*           A :|: B == the union of A and B.                                 *)
(*            x |: A == A with the element x added (:= [set x] :| A).         *)
(*           A :&: B == the intersection of A and B.                          *)
(*              ~: A == the complement of A.                                  *)
(*           A :\: B == the difference A minus B.                             *)
(*            A :\ x == A with the element x removed (:= A :\: [set x]).      *)
(* \bigcup_<range> A == the union of all A, for i in <range> (i is bound in   *)
(*                      A, see bigop.v).                                      *)
(* \bigcap_<range> A == the intersection of all A, for i in <range>.          *)
(*           cover P == the union of the set of sets P.                       *)
(*        trivIset P == the elements of P are pairwise disjoint.              *)
(*     partition P A == P is a partition of A.                                *)
(*        powerset A == the set of all subset of A                            *)
(*          P ::&: A == those sets in P that are subsets of A.                *)
(*         f @^-1: R == the preimage of the collective predicate R under f.   *)
(*            f @: D == the image set of the collective predicate D by f.     *)
(*     f @2:(D1, D2) == the image of D1 and D2 by the binary function f.      *)
(*  [set E | x <- D] == the set of all the values of the expression E, for x  *)
(*                      drawn from the collective predicate D.                *)
(*  [set E | x <- D, P] == the set of values of E for x drawn from D and such *)
(*                      that P holds.                                         *)
(*  [set E | x <- D1, y <- D2] == the set of values of E for x drawn from D1  *)
(*                      and y drawn from D2.                                  *)
(*  [set E | x <- D1, y <- D2, P] == the set of values of E for x drawn from  *)
(*                      D1, y drawn from D2, such that P holds.               *)
(*        minset p A == A is a minimal set satisfying p.                      *)
(*        maxset p A == A is a maximal set satisfying p.                      *)
(* We also provide notations A :=: B, A :<>: B, A :==: B, A :!=: B, A :=P: B  *)
(* that specialize A = B, A <> B, A == B, etc., to {set _}. This is useful    *)
(* for subtypes of {set T}, such as {group T}, that coerce to {set T}.        *)
(*   We give many lemmas on these operations, on card, and on set inclusion.  *)
(* In addition to the standard suffixes described in ssrbool.v, we associate  *)
(* the following suffixes to set operations:                                  *)
(*  0 -- the empty set, as in in_set0 : (x \in set0) = false.                 *)
(*  T -- the full set, as in in_setT : x \in [set: T].                        *)
(*  1 -- a singleton set, as in in_set1 : (x \in [set a]) = (x == a).         *)
(*  2 -- an unordered pair, as in                                             *)
(*          in_set2 : (x \in [set a; b]) = (x == a) || (x == b).              *)
(*  C -- complement, as in setCK : ~: ~: A = A.                               *)
(*  I -- intersection, as in setIid : A :&: A = A.                            *)
(*  U -- union, as in setUid : A :|: A = A.                                   *)
(*  D -- difference, as in setDv : A :\: A = set0.                            *)
(*  S -- a subset argument, as in                                             *)
(*         setIS: B \subset C -> A :&: B \subset A :&: C                      *)
(* These suffixes are sometimes preceded with an `s' to distinguish them from *)
(* their basic ssrbool interpretation, e.g.,                                  *)
(*  card1 : #|pred1 x| = 1 and cards1 : #|[set x]| = 1                        *)
(* We also use a trailling `r' to distinguish a right-hand complement from    *)
(* commutativity, e.g.,                                                       *)
(*  setIC : A :&: B = B :&: A and setICr : A :&: ~: A = set0.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Canonical set_subType :=
  Eval hnf in [newType for finfun_of_set by set_type_rect].
Definition set_eqMixin := Eval hnf in [eqMixin of set_type by <:].
Canonical set_eqType := Eval hnf in EqType set_type set_eqMixin.
Definition set_choiceMixin := [choiceMixin of set_type by <:].
Canonical set_choiceType := Eval hnf in ChoiceType set_type set_choiceMixin.
Definition set_countMixin := [countMixin of set_type by <:].
Canonical set_countType := Eval hnf in CountType set_type set_countMixin.
Canonical set_subCountType := Eval hnf in [subCountType of set_type].
Definition set_finMixin := [finMixin of set_type by <:].
Canonical set_finType := Eval hnf in FinType set_type set_finMixin.
Canonical set_subFinType := Eval hnf in [subFinType of set_type].

End SetType.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set_type.
Bind Scope set_scope with set_of.
Open Scope set_scope.
Arguments Scope finfun_of_set [_ set_scope].

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

(* We later define several subtypes that coerce to set; for these it is       *)
(* preferable to state equalities at the {set _} level, even when comparing   *)
(* subtype values, because the primitive "injection" tactic tends to diverge  *)
(* on complex types (e.g., quotient groups). We provide some parse-only       *)
(* notation to make this technicality less obstrusive.                        *)
Notation "A :=: B" := (A = B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :<>: B" := (A <> B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :==: B" := (A == B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :!=: B" := (A != B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :=P: B" := (A =P B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.

Notation Local finset_def := (fun T P => @FinSet T (finfun P)).

Notation Local pred_of_set_def := (fun T (A : set_type T) => val A : _ -> _).

Module Type SetDefSig.
Parameter finset : forall T : finType, pred T -> {set T}.
Parameter pred_of_set : forall T, set_type T -> fin_pred_sort (predPredType T).
(* The weird type of pred_of_set is imposed by the syntactic restrictions on  *)
(* coercion declarations; it is unfortunately not possible to use a functor   *)
(* to retype the declaration, because this triggers an ugly bug in the Coq    *)
(* coercion chaining code.                                                    *)
Axiom finsetE : finset = finset_def.
Axiom pred_of_setE : pred_of_set = pred_of_set_def.
End SetDefSig.

Module SetDef : SetDefSig.
Definition finset := finset_def.
Definition pred_of_set := pred_of_set_def.
Lemma finsetE : finset = finset_def. Proof. by []. Qed.
Lemma pred_of_setE : pred_of_set = pred_of_set_def. Proof. by []. Qed.
End SetDef.

Notation finset := SetDef.finset.
Notation pred_of_set := SetDef.pred_of_set.
Canonical finset_unlock := Unlockable SetDef.finsetE.
Canonical pred_of_set_unlock := Unlockable SetDef.pred_of_setE.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P))
  (at level 0, x at level 69, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x at level 69, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x \in A | P ]" := [set x | (x \in A) && P]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A  |  P ]") : set_scope.
Notation "[ 'set' x \in A ]" := [set x | x \in A]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A ]") : set_scope.

(* This lets us use set and subtypes of set, like group or coset_of, both as  *)
(* collective predicates and as arguments of the \pi(_) notation.             *)
Coercion pred_of_set: set_type >-> fin_pred_sort.

(* Declare pred_of_set as a canonical instance of topred, but use the         *)
(* coercion to resolve mem A to @mem (predPredType T) (pred_of_set A).        *)
Canonical set_predType T :=
  Eval hnf in @mkPredType _ (unkeyed (set_type T)) (@pred_of_set T).

Section BasicSetTheory.

Variable T : finType.
Implicit Types (x : T) (A B : {set T}) (pA : pred T).

Canonical set_of_subType := Eval hnf in [subType of {set T}].
Canonical set_of_eqType := Eval hnf in [eqType of {set T}].
Canonical set_of_choiceType := Eval hnf in [choiceType of {set T}].
Canonical set_of_countType := Eval hnf in [countType of {set T}].
Canonical set_of_subCountType := Eval hnf in [subCountType of {set T}].
Canonical set_of_finType := Eval hnf in [finType of {set T}].
Canonical set_of_subFinType := Eval hnf in [subFinType of {set T}].

Lemma in_set pA x : x \in finset pA = pA x.
Proof. by rewrite [@finset]unlock unlock [x \in _]ffunE. Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
by split=> [eqAB|-> //]; apply/val_inj/ffunP=> x; have:= eqAB x; rewrite unlock.
Qed.

Definition set0 := [set x : T | false].
Definition setTfor (phT : phant T) := [set x : T | true].

Lemma in_setT x : x \in setTfor (Phant T).
Proof. by rewrite in_set. Qed.

Lemma eqsVneq A B : {A = B} + {A != B}.
Proof. exact: eqVneq. Qed.

End BasicSetTheory.

Definition inE := (in_set, inE).

Implicit Arguments set0 [T].
Prenex Implicits set0.
Hint Resolve in_setT.

Notation "[ 'set' : T ]" := (setTfor (Phant T))
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Notation setT := [set: _] (only parsing).

Section setOpsDefs.

Variable T : finType.
Implicit Types (a x : T) (A B D : {set T}) (P : {set {set T}}).

Definition set1 a := [set x | x == a].
Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition setI A B := [set x | (x \in A) && (x \in B)].
Definition setC A := [set x | x \notin A].
Definition setD A B := [set x | (x \notin B) && (x \in A)].
Definition ssetI P D := [set A \in P | A \subset D].
Definition powerset D := [set A : {set T} | A \subset D].

End setOpsDefs.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 69, format "[ 'set'  a ]") : set_scope.
Notation "A :|: B" := (setU A B) (at level 52, left associativity) : set_scope.
Notation "a |: A" := ([set a] :|: A)
  (at level 52, left associativity) : set_scope.
(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |: [set a2]) .. [set an])
  (at level 0, a1, a2, an at level 69,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : set_scope.
Notation "A :&: B" := (setI A B) (at level 48, left associativity) : set_scope.
Notation "~: A" := (setC A) (at level 35, right associativity) : set_scope.
Notation "[ 'set' ~ a ]" := (~: [set a])
  (at level 0, a at level 69, format "[ 'set' ~  a ]") : set_scope.
Notation "A :\: B" := (setD A B) (at level 50) : set_scope.
Notation "A :\ a" := (A :\: [set a]) (at level 50) : set_scope.
Notation "P ::&: D" := (ssetI P D) (at level 48) : set_scope.

Section setOps.

Variable T : finType.
Implicit Types (a x : T) (A B C D : {set T}) (pA pB : pred T).

Lemma eqEsubset A B : (A == B) = (A \subset B) && (B \subset A).
Proof. by apply/eqP/subset_eqP=> /setP. Qed.

Lemma subEproper A B : A \subset B = (A == B) || (A \proper B).
Proof. by rewrite eqEsubset -andb_orr orbN andbT. Qed.

Lemma eqVproper A B : A \subset B -> A = B \/ A \proper B.
Proof. by rewrite subEproper => /predU1P. Qed.

Lemma properEneq A B : A \proper B = (A != B) && (A \subset B).
Proof. by rewrite andbC eqEsubset negb_and andb_orr andbN. Qed.

Lemma proper_neq A B : A \proper B -> A != B.
Proof. by rewrite properEneq; case/andP. Qed.

Lemma eqEproper A B : (A == B) = (A \subset B) && ~~ (A \proper B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEsubset. Qed.

Lemma eqEcard A B : (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
rewrite eqEsubset; apply: andb_id2l => sAB.
by rewrite (geq_leqif (subset_leqif_card sAB)).
Qed.

Lemma properEcard A B : (A \proper B) = (A \subset B) && (#|A| < #|B|).
Proof. by rewrite properEneq ltnNge andbC eqEcard; case: (A \subset B). Qed.

Lemma subset_leqif_cards A B : A \subset B -> (#|A| <= #|B| ?= iff (A == B)).
Proof. by move=> sAB; rewrite eqEsubset sAB; exact: subset_leqif_card. Qed.

Lemma in_set0 x : x \in set0 = false.
Proof. by rewrite inE. Qed.

Lemma sub0set A : set0 \subset A.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subset0 A : (A \subset set0) = (A == set0).
Proof. by rewrite eqEsubset sub0set andbT. Qed.

Lemma proper0 A : (set0 \proper A) = (A != set0).
Proof. by rewrite properE sub0set subset0. Qed.

Lemma set_0Vmem A : (A = set0) + {x : T | x \in A}.
Proof.
case: (pickP (mem A)) => [x Ax | A0]; [by right; exists x | left].
apply/setP=> x; rewrite inE; exact: A0.
Qed.

Lemma subsetT A : A \subset setT.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subsetT_hint mA : subset mA (mem [set: T]).
Proof. by rewrite unlock; apply/pred0P=> x; rewrite !inE. Qed.
Hint Resolve subsetT_hint.

Lemma subTset A : (setT \subset A) = (A == setT).
Proof. by rewrite eqEsubset subsetT. Qed.

Lemma properT A : (A \proper setT) = (A != setT).
Proof. by rewrite properEneq subsetT andbT. Qed.

Lemma set1P x a : reflect (x = a) (x \in [set a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma in_set1 x a : (x \in [set a]) = (x == a).
Proof. exact: in_set. Qed.

Lemma set11 x : x \in [set x].
Proof. by rewrite inE. Qed.

Lemma set1_inj : injective (@set1 T).
Proof. by move=> a b eqsab; apply/set1P; rewrite -eqsab set11. Qed.

Lemma enum_set1 a : enum [set a] = [:: a].
Proof. by rewrite (eq_enum (in_set _)) enum1. Qed.

Lemma setU1P x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma in_setU1 x a B : (x \in a |: B) = (x == a) || (x \in B).
Proof. by rewrite !inE. Qed.

Lemma set_cons a s : [set x \in a :: s] = a |: [set x \in s].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setU11 x B : x \in x |: B.
Proof. by rewrite !inE eqxx. Qed.

Lemma setU1r x a B : x \in B -> x \in a |: B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma set1Ul x A b : x \in A -> x \in A :|: [set b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma set1Ur A b : b \in A :|: [set b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma in_setC1 x a : (x \in [set~ a]) = (x != a).
Proof. by rewrite !inE. Qed.

Lemma setC11 x : (x \in [set~ x]) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. rewrite !inE; exact: andP. Qed.

Lemma in_setD1 x A b : (x \in A :\ b) = (x != b) && (x \in A) .
Proof. by rewrite !inE. Qed.

Lemma setD11 b A : (b \in A :\ b) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1K a A : a \in A -> a |: (A :\ a) = A.
Proof. by move=> Aa; apply/setP=> x; rewrite !inE; case: eqP => // ->. Qed.

Lemma setU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/setP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma set2P x a b : reflect (x = a \/ x = b) (x \in [set a; b]).
Proof. rewrite !inE; exact: pred2P. Qed.

Lemma in_set2 x a b : (x \in [set a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma set21 a b : a \in [set a; b].
Proof. by rewrite !inE eqxx. Qed.

Lemma set22 a b : b \in [set a; b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma setUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma in_setU x A B : (x \in A :|: B) = (x \in A) || (x \in B).
Proof. exact: in_set. Qed.

Lemma setUC A B : A :|: B = B :|: A.
Proof. by apply/setP => x; rewrite !inE orbC. Qed.

Lemma setUS A B C : A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSU A B C : A \subset B -> A :|: C \subset B :|: C.
Proof. by move=> sAB; rewrite -!(setUC C) setUS. Qed.

Lemma setUSS A B C D : A \subset C -> B \subset D -> A :|: B \subset C :|: D.
Proof. by move=> /(setSU B) /subset_trans sAC /(setUS C)/sAC. Qed.

Lemma set0U A : set0 :|: A = A.
Proof. by apply/setP => x; rewrite !inE orFb. Qed.

Lemma setU0 A : A :|: set0 = A.
Proof. by rewrite setUC set0U. Qed.

Lemma setUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/setP => x; rewrite !inE orbA. Qed.

Lemma setUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof. by rewrite !setUA (setUC B). Qed.

Lemma setUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof. by rewrite -!setUA (setUC B). Qed.

Lemma setTU A : setT :|: A = setT.
Proof. by apply/setP => x; rewrite !inE orTb. Qed.

Lemma setUT A : A :|: setT = setT.
Proof. by rewrite setUC setTU. Qed.

Lemma setUid A : A :|: A = A.
Proof. by apply/setP=> x; rewrite inE orbb. Qed.

Lemma setUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by rewrite !(setUC A) setUUl. Qed.

(* intersection *)

(* setIdP is a generalisation of setIP that applies to comprehensions. *)
Lemma setIdP x pA pB : reflect (pA x /\ pB x) (x \in [set y | pA y && pB y]).
Proof. by rewrite !inE; exact: andP. Qed.

Lemma setIdE A pB : [set x \in A | pB x] = A :&: [set x | pB x].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. exact: (iffP (@setIdP _ _ _)). Qed.

Lemma in_setI x A B : (x \in A :&: B) = (x \in A) && (x \in B).
Proof. exact: in_set. Qed.

Lemma setIC A B : A :&: B = B :&: A.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setIS A B C : A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSI A B C : A \subset B -> A :&: C \subset B :&: C.
Proof. by move=> sAB; rewrite -!(setIC C) setIS. Qed.

Lemma setISS A B C D : A \subset C -> B \subset D -> A :&: B \subset C :&: D.
Proof. by move=> /(setSI B) /subset_trans sAC /(setIS C) /sAC. Qed.

Lemma setTI A : setT :&: A = A.
Proof. by apply/setP => x; rewrite !inE andTb. Qed.

Lemma setIT A : A :&: setT = A.
Proof. by rewrite setIC setTI. Qed.

Lemma set0I A : set0 :&: A = set0.
Proof. by apply/setP => x; rewrite !inE andFb. Qed.

Lemma setI0 A : A :&: set0 = set0.

Proof. by rewrite setIC set0I. Qed.

Lemma setIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma setICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof. by rewrite !setIA (setIC A). Qed.

Lemma setIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof. by rewrite -!setIA (setIC B). Qed.

Lemma setIid A : A :&: A = A.
Proof. by apply/setP=> x; rewrite inE andbb. Qed.

Lemma setIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orr. Qed.

Lemma setIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orl. Qed.

Lemma setUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andr. Qed.

Lemma setUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andl. Qed.

Lemma setUK A B : (A :|: B) :&: A = A.
Proof. by apply/setP=> x; rewrite !inE orbK. Qed.

Lemma setKU A B : A :&: (B :|: A) = A.
Proof. by apply/setP=> x; rewrite !inE orKb. Qed.

Lemma setIK A B : (A :&: B) :|: A = A.
Proof. by apply/setP=> x; rewrite !inE andbK. Qed.

Lemma setKI A B : A :|: (B :&: A) = A.
Proof. by apply/setP=> x; rewrite !inE andKb. Qed.

(* complement *)

Lemma setCP x A : reflect (~ x \in A) (x \in ~: A).
Proof. by rewrite !inE; exact: negP. Qed.

Lemma in_setC x A : (x \in ~: A) = (x \notin A).
Proof. exact: in_set. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; apply/setP=> x; rewrite !inE negbK. Qed.

Lemma setC_inj : injective (@setC T).
Proof. exact: can_inj setCK. Qed.

Lemma subsets_disjoint A B : (A \subset B) = [disjoint A & ~: B].
Proof. by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE. Qed.

Lemma disjoints_subset A B : [disjoint A & B] = (A \subset ~: B).
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma powersetCE A B : (A \in powerset (~: B)) = [disjoint A & B].
Proof. by rewrite inE disjoints_subset. Qed.

Lemma setCS A B : (~: A \subset ~: B) = (B \subset A).
Proof. by rewrite !subsets_disjoint setCK disjoint_sym. Qed.

Lemma setCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_or. Qed.

Lemma setCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_and. Qed.

Lemma setUCr A : A :|: ~: A = setT.
Proof. by apply/setP=> x; rewrite !inE orbN. Qed.

Lemma setICr A : A :&: ~: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbN. Qed.

Lemma setC0 : ~: set0 = setT :> {set T}.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setCT : ~: setT = set0 :> {set T}.
Proof. by rewrite -setC0 setCK. Qed.

(* difference *)

Lemma setDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by rewrite inE andbC; exact: andP. Qed.

Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A).
Proof. exact: in_set. Qed.

Lemma setDE A B : A :\: B = A :&: ~: B.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setSD A B C : A \subset B -> A :\: C \subset B :\: C.
Proof. by rewrite !setDE; exact: setSI. Qed.

Lemma setDS A B C : A \subset B -> C :\: B \subset C :\: A.
Proof. by rewrite !setDE -setCS; exact: setIS. Qed.

Lemma setDSS A B C D : A \subset C -> D \subset B -> A :\: B \subset C :\: D.
Proof. by move=> /(setSD B) /subset_trans sAC /(setDS C) /sAC. Qed.

Lemma setD0 A : A :\: set0 = A.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma set0D A : set0 :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbF. Qed.

Lemma setDT A : A :\: setT = set0.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setTD A : setT :\: A = ~: A.
Proof. by apply/setP=> x; rewrite !inE andbT. Qed.

Lemma setDv A : A :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andNb. Qed.

Lemma setCD A B : ~: (A :\: B) = ~: A :|: B.
Proof. by rewrite !setDE setCI setCK. Qed.

Lemma setID A B : A :&: B :|: A :\: B = A.
Proof. by rewrite setDE -setIUr setUCr setIT. Qed.

Lemma setDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. by rewrite !setDE setIUl. Qed.

Lemma setDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. by rewrite !setDE setCU setIIr. Qed.

Lemma setDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. by rewrite !setDE setIIl. Qed.

Lemma setDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. by rewrite !setDE setCI setIUr. Qed.

Lemma setDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof. by rewrite !setDE setCU setIA. Qed.

Lemma setDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. by rewrite !setDE setCI setIUr setCK. Qed.

(* powerset *)

Lemma powersetE A B : (A \in powerset B) = (A \subset B).
Proof. by rewrite inE. Qed.

Lemma powersetS A B : (powerset A \subset powerset B) = (A \subset B).
Proof.
apply/subsetP/idP=> [sAB | sAB C]; last by rewrite !inE => /subset_trans ->.
by rewrite -powersetE sAB // inE.
Qed.

Lemma powerset0 : powerset set0 = [set set0] :> {set {set T}}.
Proof. by apply/setP=> A; rewrite !inE subset0. Qed.

Lemma powersetT : powerset [set: T] = [set: {set T}].
Proof. by apply/setP=> A; rewrite !inE subsetT. Qed.

Lemma setI_powerset P A : P :&: powerset A = P ::&: A.
Proof. by apply/setP=> B; rewrite !inE. Qed.

(* cardinal lemmas for sets *)

Lemma cardsE pA : #|[set x \in pA]| = #|pA|.
Proof. by apply: eq_card; exact: in_set. Qed.

Lemma sum1dep_card pA : \sum_(x | pA x) 1 = #|[set x | pA x]|.
Proof. by rewrite sum1_card cardsE. Qed.

Lemma sum_nat_dep_const pA n : \sum_(x | pA x) n = #|[set x | pA x]| * n.
Proof. by rewrite sum_nat_const cardsE. Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof. by rewrite cardsE card0. Qed.

Lemma cards_eq0 A : (#|A| == 0) = (A == set0).
Proof. by rewrite (eq_sym A) eqEcard sub0set cards0 leqn0. Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != set0).
Proof. by rewrite -cards_eq0; exact: existsP. Qed.

Lemma card_gt0 A : (0 < #|A|) = (A != set0).
Proof. by rewrite lt0n cards_eq0. Qed.

Lemma cards0_eq A : #|A| = 0 -> A = set0.
Proof. by move=> A_0; apply/setP=> x; rewrite inE (card0_eq A_0). Qed.

Lemma cards1 x : #|[set x]| = 1.
Proof. by rewrite cardsE card1. Qed.

Lemma cardsUI A B : #|A :|: B| + #|A :&: B| = #|A| + #|B|.
Proof. by rewrite !cardsE cardUI. Qed.

Lemma cardsT : #|[set: T]| = #|T|.
Proof. by rewrite cardsE. Qed.

Lemma cardsID B A : #|A :&: B| + #|A :\: B| = #|A|.
Proof. by rewrite !cardsE cardID. Qed.

Lemma cardsC A : #|A| + #|~: A| = #|T|.
Proof. by rewrite cardsE cardC. Qed.

Lemma cardsCs A : #|A| = #|T| - #|~: A|.
Proof. by rewrite -(cardsC A) addnK. Qed.

Lemma cardsU1 a A : #|a |: A| = (a \notin A) + #|A|.
Proof. by rewrite -cardU1; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cards2 a b : #|[set a; b]| = (a != b).+1.
Proof. by rewrite -card2; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsC1 a : #|[set~ a]| = #|T|.-1.
Proof. by rewrite -(cardC1 a); apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsD1 a A : #|A| = (a \in A) + #|A :\ a|.
Proof.
by rewrite (cardD1 a); congr (_ + _); apply: eq_card => x; rewrite !inE.
Qed.

(* other inclusions *)

Lemma subsetIl A B : A :&: B \subset A.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetIr A B : A :&: B \subset B.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetUl A B : A \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE => ->. Qed.

Lemma subsetUr A B : B \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE orbC => ->. Qed.

Lemma subsetU1 x A : A \subset x |: A.
Proof. exact: subsetUr. Qed.

Lemma subsetDl A B : A :\: B \subset A.
Proof. by rewrite setDE subsetIl. Qed.

Lemma subD1set A x : A :\ x \subset A.
Proof. by rewrite subsetDl. Qed.

Lemma subsetDr A B : A :\: B \subset ~: B.
Proof. by rewrite setDE subsetIr. Qed.

Lemma sub1set A x : ([set x] \subset A) = (x \in A).
Proof. by rewrite -subset_pred1; apply: eq_subset=> y; rewrite !inE. Qed.

Lemma cards1P A : reflect (exists x, A = [set x]) (#|A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cards1.
rewrite eq_sym eqn_leq card_gt0 => /andP[/set0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEcard sub1set Ax cards1 leA1.
Qed.

Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0).
Proof.
rewrite eqEcard cards1 -cards_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cards0_eq A0) sub0set.
Qed.

Lemma powerset1 x : powerset [set x] = [set set0; [set x]].
Proof. by apply/setP=> A; rewrite !inE subset1 orbC. Qed.

Lemma setIidPl A B : reflect (A :&: B = A) (A \subset B).
Proof.
apply: (iffP subsetP) => [sAB | <- x /setIP[] //].
by apply/setP=> x; rewrite inE; apply: andb_idr; exact: sAB.
Qed.
Implicit Arguments setIidPl [A B].

Lemma setIidPr A B : reflect (A :&: B = B) (B \subset A).
Proof. rewrite setIC; exact: setIidPl. Qed.

Lemma setUidPl A B : reflect (A :|: B = A) (B \subset A).
Proof.
by rewrite -setCS (sameP setIidPl eqP) -setCU (inj_eq setC_inj); exact: eqP.
Qed.

Lemma setUidPr A B : reflect (A :|: B = B) (A \subset B).
Proof. rewrite setUC; exact: setUidPl. Qed.

Lemma setDidPl A B : reflect (A :\: B = A) [disjoint A & B].
Proof. rewrite setDE disjoints_subset; exact: setIidPl. Qed.

Lemma subIset A B C : (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof. by case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma subsetI A B C : (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
rewrite !(sameP setIidPl eqP) setIA; have [-> //| ] := altP (A :&: B =P A).
by apply: contraNF => /eqP <-; rewrite -setIA -setIIl setIAC.
Qed.

Lemma subsetIP A B C : reflect (A \subset B /\ A \subset C) (A \subset B :&: C).
Proof. by rewrite subsetI; exact: andP. Qed.

Lemma subsetIidl A B : (A \subset A :&: B) = (A \subset B).
Proof. by rewrite subsetI subxx. Qed.

Lemma subsetIidr A B : (B \subset A :&: B) = (B \subset A).
Proof. by rewrite setIC subsetIidl. Qed.

Lemma powersetI A B : powerset (A :&: B) = powerset A :&: powerset B.
Proof. by apply/setP=> C; rewrite !inE subsetI. Qed.

Lemma subUset A B C : (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof. by rewrite -setCS setCU subsetI !setCS. Qed.

Lemma subsetU A B C : (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof. by rewrite -!(setCS _ A) setCU; exact: subIset. Qed.

Lemma subUsetP A B C : reflect (A \subset C /\ B \subset C) (A :|: B \subset C).
Proof. by rewrite subUset; exact: andP. Qed.

Lemma subsetC A B : (A \subset ~: B) = (B \subset ~: A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subCset A B : (~: A \subset B) = (~: B \subset A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subsetD A B C : (A \subset B :\: C) = (A \subset B) && [disjoint A & C].
Proof. by rewrite setDE subsetI -disjoints_subset. Qed.

Lemma subDset A B C : (A :\: B \subset C) = (A \subset B :|: C).
Proof.
apply/subsetP/subsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?inE ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

Lemma subsetDP A B C :
  reflect (A \subset B /\ [disjoint A & C]) (A \subset B :\: C).
Proof. by rewrite subsetD; exact: andP. Qed.

Lemma setU_eq0 A B : (A :|: B == set0) = (A == set0) && (B == set0).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setD_eq0 A B : (A :\: B == set0) = (A \subset B).
Proof. by rewrite -subset0 subDset setU0. Qed.

Lemma setI_eq0 A B : (A :&: B == set0) = [disjoint A & B].
Proof. by rewrite disjoints_subset -setD_eq0 setDE setCK. Qed.

Lemma disjoint_setI0 A B : [disjoint A & B] -> A :&: B = set0.
Proof. by rewrite -setI_eq0; move/eqP. Qed.

Lemma subsetD1 A B x : (A \subset B :\ x) = (A \subset B) && (x \notin A).
Proof. by rewrite setDE subsetI subsetC sub1set inE. Qed.

Lemma subsetD1P A B x : reflect (A \subset B /\ x \notin A) (A \subset B :\ x).
Proof. by rewrite subsetD1; exact: andP. Qed.

Lemma properD1 A x : x \in A -> A :\ x \proper A.
Proof.
move=> Ax; rewrite properE subsetDl; apply/subsetPn; exists x=> //.
by rewrite in_setD1 Ax eqxx.
Qed.

Lemma properIr A B : ~~ (B \subset A) -> A :&: B \proper B.
Proof. by move=> nsAB; rewrite properE subsetIr subsetI negb_and nsAB. Qed.

Lemma properIl A B : ~~ (A \subset B) -> A :&: B \proper A.
Proof. by move=> nsBA; rewrite properE subsetIl subsetI negb_and nsBA orbT. Qed.

Lemma properUr A B : ~~ (A \subset B) ->  B \proper A :|: B.
Proof. by rewrite properE subsetUr subUset subxx /= andbT. Qed.

Lemma properUl A B : ~~ (B \subset A) ->  A \proper A :|: B.
Proof. by move=> not_sBA; rewrite setUC properUr. Qed.

Lemma proper1set A x : ([set x] \proper A) -> (x \in A).
Proof. by move/proper_sub; rewrite sub1set. Qed.

Lemma properIset A B C : (B \proper A) || (C \proper A) -> (B :&: C \proper A).
Proof. by case/orP; apply: sub_proper_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma properI A B C : (A \proper B :&: C) -> (A \proper B) && (A \proper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (proper_sub_trans pAI); rewrite (subsetIl, subsetIr).
Qed.

Lemma properU A B C : (B :|: C \proper A) -> (B \proper A) && (C \proper A).
Proof.
move=> pUA; apply/andP.
by split; apply: sub_proper_trans pUA; rewrite (subsetUr, subsetUl).
Qed.

Lemma properD A B C : (A \proper B :\: C) -> (A \proper B) && [disjoint A & C].
Proof. by rewrite setDE disjoints_subset => /properI/andP[-> /proper_sub]. Qed.

End setOps.

Implicit Arguments set1P [T x a].
Implicit Arguments set1_inj [T].
Implicit Arguments set2P [T x a b].
Implicit Arguments setIdP [T x pA pB].
Implicit Arguments setIP [T x A B].
Implicit Arguments setU1P [T x a B].
Implicit Arguments setD1P [T x A b].
Implicit Arguments setUP [T x A B].
Implicit Arguments setDP [T x A B].
Implicit Arguments cards1P [T A].
Implicit Arguments setCP [T x A].
Implicit Arguments setIidPl [T A B].
Implicit Arguments setIidPr [T A B].
Implicit Arguments setUidPl [T A B].
Implicit Arguments setUidPr [T A B].
Implicit Arguments setDidPl [T A B].
Implicit Arguments subsetIP [T A B C].
Implicit Arguments subUsetP [T A B C].
Implicit Arguments subsetDP [T A B C].
Implicit Arguments subsetD1P [T A B x].
Prenex Implicits set1P set1_inj set2P setU1P setD1P setIdP setIP setUP setDP.
Prenex Implicits cards1P setCP setIidPl setIidPr setUidPl setUidPr setDidPl.
Hint Resolve subsetT_hint.

Section setOpsAlgebra.

Import Monoid.

Variable T : finType.

Canonical setI_monoid := Law (@setIA T) (@setTI T) (@setIT T).

Canonical setI_comoid := ComLaw (@setIC T).
Canonical setI_muloid := MulLaw (@set0I T) (@setI0 T).

Canonical setU_monoid := Law (@setUA T) (@set0U T) (@setU0 T).
Canonical setU_comoid := ComLaw (@setUC T).
Canonical setU_muloid := MulLaw (@setTU T) (@setUT T).

Canonical setI_addoid := AddLaw (@setUIl T) (@setUIr T).
Canonical setU_addoid := AddLaw (@setIUl T) (@setIUr T).

End setOpsAlgebra.

Section CartesianProd.

Variables fT1 fT2 : finType.
Variables (A1 : {set fT1}) (A2 : {set fT2}).

Definition setX := [set u | (u.1 \in A1) && (u.2 \in A2)].

Lemma in_setX x1 x2 : ((x1, x2) \in setX) = (x1 \in A1) && (x2 \in A2).
Proof. by rewrite inE. Qed.

Lemma setXP x1 x2 : reflect (x1 \in A1 /\ x2 \in A2) ((x1, x2) \in setX).
Proof. by rewrite inE; exact: andP. Qed.

Lemma cardsX : #|setX| = #|A1| * #|A2|.
Proof. by rewrite cardsE cardX. Qed.

End CartesianProd.

Implicit Arguments setXP [x1 x2 fT1 fT2 A1 A2].
Prenex Implicits setXP.

Notation Local imset_def :=
  (fun (aT rT : finType) f (D : mem_pred aT) => [set y \in @image aT rT f D]).
Notation Local imset2_def :=
  (fun (aT1 aT2 rT : finType) f (D1 : mem_pred aT1) (D2 : _ -> mem_pred aT2) =>
     [set y \in @image _ rT (prod_curry f) [pred u | D1 u.1 && D2 u.1 u.2]]).

Module Type ImsetSig.
Parameter imset : forall aT rT : finType,
 (aT -> rT) -> mem_pred aT -> {set rT}.
Parameter imset2 : forall aT1 aT2 rT : finType,
 (aT1 -> aT2 -> rT) -> mem_pred aT1 -> (aT1 -> mem_pred aT2) -> {set rT}.
Axiom imsetE : imset = imset_def.
Axiom imset2E : imset2 = imset2_def.
End ImsetSig.

Module Imset : ImsetSig.
Definition imset := imset_def.
Definition imset2 := imset2_def.
Lemma imsetE : imset = imset_def. Proof. by []. Qed.
Lemma imset2E : imset2 = imset2_def. Proof. by []. Qed.
End Imset.

Notation imset := Imset.imset.
Notation imset2 := Imset.imset2.
Canonical imset_unlock := Unlockable Imset.imsetE.
Canonical imset2_unlock := Unlockable Imset.imset2E.
Definition preimset (aT : finType) rT f (R : mem_pred rT) :=
  [set x : aT | in_mem (f x) R].

Notation "f @^-1: R" := (preimset f (mem R)) (at level 24) : set_scope.
Notation "f @: D" := (imset f (mem D)) (at level 24) : set_scope.
Notation "f @2: ( D1 , D2 )" := (imset2 f (mem D1) (fun _ => (mem D2)))
  (at level 24, format "f  @2:  ( D1 ,  D2 )") : set_scope.
Notation "[ 'set' E | x <- A ]" := ((fun x => E) @: A)
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ]") : set_scope.
Notation "[ 'set' E | x <- A , P ]" := ((fun x => E) @: [set x \in A | P])
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ,  P ]") : set_scope.
Notation "[ 'set' E | x <- A , y <- B ]" :=
  (imset2 (fun x y => E) (mem A) (fun x => (mem B)))
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ,  y  <-  B ]") : set_scope.
Notation "[ 'set' E | x <- A , y <- B , P ]" :=
  [set E | x <- A, y <- [set y \in B | P]]
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ,  y  <-  B ,  P ]") : set_scope.
Notation "[ 'set' E | x <- A , y < - B ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ => mem B))
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ,  y  < -  B ]") : set_scope.
Notation "[ 'set' E | x <- A , y < - B , P ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ => mem [set y \in B | P]))
  (at level 0, E at level 69,
   format "[ 'set'  E  |  x  <-  A ,  y  < -  B ,  P ]") : set_scope.

Section FunImage.

Variables aT aT2 : finType.

Section ImsetTheory.

Variable rT : finType.

Section ImsetProp.

Variables (f : aT -> rT) (f2 : aT -> aT2 -> rT).

Lemma imsetP D y : reflect (exists2 x, in_mem x D & y = f x) (y \in imset f D).
Proof. rewrite [@imset]unlock inE; exact: imageP. Qed.

CoInductive imset2_spec D1 D2 y : Prop :=
  Imset2spec x1 x2 of in_mem x1 D1 & in_mem x2 (D2 x1) & y = f2 x1 x2.

Lemma imset2P D1 D2 y : reflect (imset2_spec D1 D2 y) (y \in imset2 f2 D1 D2).
Proof.
rewrite [@imset2]unlock inE.
apply: (iffP (imageP _ _ _)) => [[[x1 x2] Dx12] | [x1 x2 Dx1 Dx2]] -> {y}.
  by case/andP: Dx12; exists x1 x2.
by exists (x1, x2); rewrite //= Dx1.
Qed.

Lemma mem_imset (D : pred aT) x : x \in D -> f x \in f @: D.
Proof. by move=> Dx; apply/imsetP; exists x. Qed.

Lemma imset0 : f @: set0 = set0.
Proof. by apply/setP => y; rewrite inE; apply/imsetP=> [[x]]; rewrite inE. Qed.

Lemma imset_set1 x : f @: [set x] = [set f x].
Proof.
apply/setP => y.
by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11.
Qed.

Lemma mem_imset2 (D : pred aT) (D2 : aT -> pred aT2) x x2 :
    x \in D -> x2 \in D2 x ->
  f2 x x2 \in imset2 f2 (mem D) (fun x1 => mem (D2 x1)).
Proof. by move=> Dx Dx2; apply/imset2P; exists x x2. Qed.

Lemma sub_imset_pre (A : pred aT) (B : pred rT) :
  (f @: A \subset B) = (A \subset f @^-1: B).
Proof.
apply/subsetP/subsetP=> [sfAB x Ax | sAf'B fx].
  by rewrite inE sfAB ?mem_imset.
by case/imsetP=> x Ax ->; move/sAf'B: Ax; rewrite inE.
Qed.

Lemma preimsetS (A B : pred rT) :
  A \subset B -> (f @^-1: A) \subset (f @^-1: B).
Proof. move=> sAB; apply/subsetP=> y; rewrite !inE; exact: (subsetP sAB). Qed.

Lemma preimset0 : f @^-1: set0 = set0.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma preimsetT : f @^-1: setT = setT.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma preimsetI (A B : {set rT}) :
  f @^-1: (A :&: B) = (f @^-1: A) :&: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetU (A B : {set rT}) :
  f @^-1: (A :|: B) = (f @^-1: A) :|: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetD (A B : {set rT}) :
  f @^-1: (A :\: B) = (f @^-1: A) :\: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetC (A : {set rT}) : f @^-1: (~: A) = ~: f @^-1: A.
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma imsetS (A B : pred aT) : A \subset B -> f @: A \subset f @: B.
Proof.
move=> sAB; apply/subsetP=> _ /imsetP[x Ax ->].
by apply/imsetP; exists x; rewrite ?(subsetP sAB).
Qed.

Lemma imset_proper (A B : {set aT}) :
   {in B &, injective f} -> A \proper B -> f @: A \proper f @: B.
Proof.
move=> injf /properP[sAB [x Bx nAx]]; rewrite properE imsetS //=.
apply: contra nAx => sfBA.
have: f x \in f @: A by rewrite (subsetP sfBA) ?mem_imset.
by case/imsetP=> y Ay /injf-> //; exact: subsetP sAB y Ay.
Qed.

Lemma preimset_proper (A B : {set rT}) :
  B \subset codom f -> A \proper B -> (f @^-1: A) \proper (f @^-1: B).
Proof.
move=> sBc /properP[sAB [u Bu nAu]]; rewrite properE preimsetS //=.
by apply/subsetPn; exists (iinv (subsetP sBc  _ Bu)); rewrite inE /= f_iinv.
Qed.

Lemma imsetU (A B : {set aT}) : f @: (A :|: B) = (f @: A) :|: (f @: B).
Proof.
apply/eqP; rewrite eqEsubset subUset.
rewrite 2?imsetS (andbT, subsetUl, subsetUr) // andbT.
apply/subsetP=> _ /imsetP[x ABx ->]; apply/setUP.
by case/setUP: ABx => [Ax | Bx]; [left | right]; apply/imsetP; exists x.
Qed.

Lemma imsetU1 a (A : {set aT}) : f @: (a |: A) = f a |: (f @: A).
Proof. by rewrite imsetU imset_set1. Qed.

Lemma imsetI (A B : {set aT}) :
  {in A & B, injective f} -> f @: (A :&: B) = f @: A :&: f @: B.
Proof.
move=> injf; apply/eqP; rewrite eqEsubset subsetI.
rewrite 2?imsetS (andTb, subsetIl, subsetIr) //=.
apply/subsetP=> _ /setIP[/imsetP[x Ax ->] /imsetP[z Bz /injf eqxz]].
by rewrite mem_imset // inE Ax eqxz.
Qed.

Lemma imset2Sl (A B : pred aT) (C : pred aT2) :
  A \subset B -> f2 @2: (A, C) \subset f2 @2: (B, C).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2Sr (A B : pred aT2) (C : pred aT) :
  A \subset B -> f2 @2: (C, A) \subset f2 @2: (C, B).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2S (A B : pred aT) (A2 B2 : pred aT2) :
  A \subset B ->  A2 \subset B2 -> f2 @2: (A, A2) \subset f2 @2: (B, B2).
Proof.  by move=> /(imset2Sl B2) sBA /(imset2Sr A)/subset_trans->. Qed.

End ImsetProp.

Implicit Types (f g : aT -> rT) (D : {set aT}) (R : pred rT).

Lemma eq_preimset f g R : f =1 g -> f @^-1: R = g @^-1: R.
Proof. by move=> eqfg; apply/setP => y; rewrite !inE eqfg. Qed.

Lemma eq_imset f g D : f =1 g -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP=> y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset f g D : {in D, f =1 g} -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset2 (f g : aT -> aT2 -> rT) (D : pred aT) (D2 : pred aT2) :
  {in D & D2, f =2 g} -> f @2: (D, D2) = g @2: (D, D2).
Proof.
move=> eqfg; apply/setP => y.
by apply/imset2P/imset2P=> [] [x x2 Dx Dx2 ->]; exists x x2; rewrite ?eqfg.
Qed.

End ImsetTheory.

Lemma imset2_pair (A : {set aT}) (B : {set aT2}) :
  [set (x, y) | x <- A, y <- B] = setX A B.
Proof.
apply/setP=> [[x y]]; rewrite !inE /=.
by apply/imset2P/andP=> [[_ _ _ _ [-> ->]//]| []]; exists x y.
Qed.

Lemma setXS (A1 B1 : {set aT}) (A2 B2 : {set aT2}) :
  A1 \subset B1 -> A2 \subset B2 -> setX A1 A2 \subset setX B1 B2.
Proof. by move=> sAB1 sAB2; rewrite -!imset2_pair imset2S. Qed.

End FunImage.

Implicit Arguments imsetP [aT rT f D y].
Implicit Arguments imset2P [aT aT2 rT f2 D1 D2 y].
Prenex Implicits imsetP imset2P.

Section BigOps.

Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Implicit Type A B : {set I}.
Implicit Type h : I -> J.
Implicit Type P : pred I.
Implicit Type F : I -> R.

Lemma big_set0 F : \big[op/idx]_(i \in set0) F i = idx.
Proof. by apply: big_pred0 => i; rewrite inE. Qed.

Lemma big_set1 a F : \big[op/idx]_(i \in [set a]) F i = F a.
Proof. by apply: big_pred1 => i; rewrite !inE. Qed.

Lemma big_setIDdep A B P F :
  \big[aop/idx]_(i \in A | P i) F i =
     aop (\big[aop/idx]_(i \in A :&: B | P i) F i)
         (\big[aop/idx]_(i \in A :\: B | P i) F i).
Proof.
rewrite (bigID (mem B)) setDE.
by congr (aop _ _); apply: eq_bigl => i; rewrite !inE andbAC.
Qed.

Lemma big_setID A B F :
  \big[aop/idx]_(i \in A) F i =
     aop (\big[aop/idx]_(i \in A :&: B) F i)
         (\big[aop/idx]_(i \in A :\: B) F i).
Proof.
rewrite (bigID (mem B)) !(eq_bigl _ _ (in_set _)) //=.
by congr (aop _); apply: eq_bigl => i; rewrite andbC.
Qed.

Lemma big_setD1 a A F : a \in A ->
  \big[aop/idx]_(i \in A) F i = aop (F a) (\big[aop/idx]_(i \in A :\ a) F i).
Proof.
move=> Aa; rewrite (bigD1 a Aa); congr (aop _).
by apply: eq_bigl => x; rewrite !inE andbC.
Qed.

Lemma big_setU1 a A F : a \notin A ->
  \big[aop/idx]_(i \in a |: A) F i = aop (F a) (\big[aop/idx]_(i \in A) F i).
Proof. by move=> notAa; rewrite (@big_setD1 a) ?setU11 //= setU1K. Qed.

Lemma big_imset h A G :
     {in A &, injective h} ->
  \big[aop/idx]_(j \in h @: A) G j = \big[aop/idx]_(i \in A) G (h i).
Proof.
move=> injh; pose hA := [image h of A].
have [-> | [x0 Ax0]] := set_0Vmem A.
  by rewrite imset0 !big_pred0 // => x /=; rewrite inE.
rewrite (eq_bigl hA) => [|j]; last by exact/imsetP/imageP.
pose h' j := if insub j : {? j | hA j} is Some u then iinv (svalP u) else x0.
rewrite (reindex_onto h h') => [|j hAj]; rewrite {}/h'; last first.
  by rewrite (insubT hA hAj) f_iinv.
apply: eq_bigl => i; case: insubP => [u -> /= def_u | nhAhi].
  set i' := iinv _; have Ai' : i' \in A := mem_iinv (svalP u).
  by apply/eqP/idP=> [<- // | Ai]; apply: injh; rewrite ?f_iinv.
symmetry; rewrite (negbTE nhAhi); apply/idP=> Ai.
by case/imageP: nhAhi; exists i.
Qed.

Lemma partition_big_imset h A F :
  \big[aop/idx]_(i \in A) F i =
     \big[aop/idx]_(j \in h @: A) \big[aop/idx]_(i \in A | h i == j) F i.
Proof. by apply: partition_big => i Ai; apply/imsetP; exists i. Qed.

End BigOps.

Implicit Arguments big_setID [R idx aop I A].
Implicit Arguments big_setD1 [R idx aop I A F].
Implicit Arguments big_setU1 [R idx aop I A F].
Implicit Arguments big_imset [R idx aop h I J A].
Implicit Arguments partition_big_imset [R idx aop I J].

Section Fun2Set1.

Variables aT1 aT2 rT : finType.
Variables (f : aT1 -> aT2 -> rT).

Lemma imset2_set1l x1 (D2 : pred aT2) : f @2: ([set x1], D2) = f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x x2 /set1P->]| [x2 Dx2 ->]].
  by exists x2.
by exists x1 x2; rewrite ?set11.
Qed.

Lemma imset2_set1r x2 (D1 : pred aT1) : f @2: (D1, [set x2]) = f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x1 x Dx1 /set1P->]| [x1 Dx1 ->]].
  by exists x1.
by exists x1 x2; rewrite ?set11.
Qed.

End Fun2Set1.

Section CardFunImage.

Variables aT aT2 rT : finType.
Variables (f : aT -> rT) (g : rT -> aT) (f2 : aT -> aT2 -> rT).
Variables (D : pred aT) (D2 : pred aT).

Lemma imset_card : #|f @: D| = #|[image f of D]|.
Proof. by rewrite [@imset]unlock cardsE. Qed.

Lemma leq_imset_card : #|f @: D| <= #|D|.
Proof. by rewrite imset_card leq_image_card. Qed.

Lemma card_in_imset : {in D &, injective f} -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_in_image. Qed.

Lemma card_imset : injective f -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_image. Qed.

Lemma imset_injP : reflect {in D &, injective f} (#|f @: D| == #|D|).
Proof. by rewrite [@imset]unlock cardsE; exact: image_injP. Qed.

Lemma can2_in_imset_pre :
  {in D, cancel f g} -> {on D, cancel g & f} -> f @: D = g @^-1: D.
Proof.
move=> fK gK; apply/setP=> y; rewrite inE.
by apply/imsetP/idP=> [[x Ax ->] | Agy]; last exists (g y); rewrite ?(fK, gK).
Qed.

Lemma can2_imset_pre : cancel f g -> cancel g f -> f @: D = g @^-1: D.
Proof. by move=> fK gK; apply: can2_in_imset_pre; exact: in1W. Qed.

End CardFunImage.

Implicit Arguments imset_injP [aT rT f D].

Lemma on_card_preimset (aT rT : finType) (f : aT -> rT) (R : pred rT) :
  {on R, bijective f} -> #|f @^-1: R| = #|R|.
Proof.
case=> g fK gK; rewrite -(can2_in_imset_pre gK) // card_in_imset //.
exact: can_in_inj gK.
Qed.

Lemma can_imset_pre (T : finType) f g (A : {set T}) :
  cancel f g -> f @: A = g @^-1: A :> {set T}.
Proof.
move=> fK; apply: can2_imset_pre => // x.
suffices fx: codom f x by rewrite -(f_iinv fx) fK.
move: x; apply/(subset_cardP (card_codom (can_inj fK))); exact/subsetP.
Qed.

Lemma card_preimset (T : finType) (f : T -> T) (A : {set T}) :
  injective f -> #|f @^-1: A| = #|A|.
Proof.
move=> injf; apply: on_card_preimset; apply: onW_bij.
have ontof: codom f _ by exact/(subset_cardP (card_codom injf))/subsetP.
by exists (fun x => iinv (ontof x)) => x; rewrite (f_iinv, iinv_f).
Qed.

Lemma card_powerset (T : finType) (A : {set T}) : #|powerset A| = 2 ^ #|A|.
Proof.
rewrite -card_bool -(card_pffun_on false) -(card_imset _ val_inj).
apply: eq_card => f; pose sf := false.-support f; pose D := finset sf.
have sDA: (D \subset A) = (sf \subset A) by apply: eq_subset; exact: in_set.
have eq_sf x : sf x = f x by rewrite /= negb_eqb addbF.
have valD: val D = f by rewrite /D unlock; apply/ffunP=> x; rewrite ffunE eq_sf.
apply/imsetP/pffun_onP=> [[B] | [sBA _]]; last by exists D; rewrite // inE ?sDA.
by rewrite inE -sDA -valD => sBA /val_inj->.
Qed.

Section FunImageComp.

Variables T T' U : finType.

Lemma imset_comp (f : T' -> U) (g : T -> T') (H : pred T) :
  (f \o g) @: H = f @: (g @: H).
Proof.
apply/setP/subset_eqP/andP.
split; apply/subsetP=> _ /imsetP[x0 Hx0 ->]; apply/imsetP.
  by exists (g x0); first apply: mem_imset.
by move/imsetP: Hx0 => [x1 Hx1 ->]; exists x1.
Qed.

End FunImageComp.

Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcup_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \bigcup_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  \in  A ) '/  '  F ']'").

Notation "\bigcup_ ( <- r | P ) F" :=
  (\big[@setU _/set0]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@setU _/set0]_(i <- r | P) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@setU _/set0]_(i <- r) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@setU _/set0]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@setU _/set0]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@setU _/set0]_(i | P%B) F%SET) : set_scope.
Notation "\bigcup_ i F" :=
  (\big[@setU _/set0]_i F%SET) : set_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@setU _/set0]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@setU _/set0]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@setU _/set0]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@setU _/set0]_ (i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i \in A | P ) F" :=
  (\big[@setU _/set0]_(i \in A | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i \in A ) F" :=
  (\big[@setU _/set0]_(i \in A) F%SET) : set_scope.

Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \bigcap_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r  |  P )  F ']'").
Reserved Notation "\bigcap_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  \in  A ) '/  '  F ']'").

Notation "\bigcap_ ( <- r | P ) F" :=
  (\big[@setI _/setT]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r | P ) F" :=
  (\big[@setI _/setT]_(i <- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r ) F" :=
  (\big[@setI _/setT]_(i <- r) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n | P ) F" :=
  (\big[@setI _/setT]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n ) F" :=
  (\big[@setI _/setT]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setT]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ i F" :=
  (\big[@setI _/setT]_i F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i : t ) F" :=
  (\big[@setI _/setT]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcap_ ( i < n | P ) F" :=
  (\big[@setI _/setT]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\big[@setI _/setT]_(i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A | P ) F" :=
  (\big[@setI _/setT]_(i \in A | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A ) F" :=
  (\big[@setI _/setT]_(i \in A) F%SET) : set_scope.

Section BigSetOps.

Variables T I : finType.
Implicit Type U : pred T.
Implicit Type P : pred I.
Implicit Types A B : {set I}.
Implicit Type F :  I -> {set T}.

(* It is very hard to use this lemma, because the unification fails to *)
(* defer the F j pattern (even though it's a Miller pattern!).         *)
Lemma bigcup_sup j P F : P j -> F j \subset \bigcup_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigD1 j) //= subsetUl. Qed.

Lemma bigcup_max j U P F :
  P j -> U \subset F j -> U \subset \bigcup_(i | P i) F i.
Proof. by move=> Pj sUF; exact: subset_trans (bigcup_sup _ Pj). Qed.

Lemma bigcupP x P F :
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[i Pi]]; last first.
  apply: subsetP x; exact: bigcup_sup.
by elim/big_rec: _ => [|i _ Pi _ /setUP[|//]]; [rewrite inE | exists i].
Qed.

Lemma bigcupsP U P F :
  reflect (forall i, P i -> F i \subset U) (\bigcup_(i | P i) F i \subset U).
Proof.
apply: (iffP idP) => [sFU i Pi| sFU].
  by apply: subset_trans sFU; exact: bigcup_sup.
by apply/subsetP=> x /bigcupP[i Pi]; exact: (subsetP (sFU i Pi)).
Qed.

Lemma bigcup_disjoint U P F :
  (forall i, P i -> [disjoint U & F i]) -> [disjoint U & \bigcup_(i | P i) F i].
Proof.
move=> dUF; rewrite disjoint_sym disjoint_subset.
by apply/bigcupsP=> i /dUF; rewrite disjoint_sym disjoint_subset.
Qed.

Lemma bigcup_setU A B F :
  \bigcup_(i \in A :|: B) F i =
     (\bigcup_(i \in A) F i) :|: (\bigcup_ (i \in B) F i).
Proof.
apply/setP=> x; apply/bigcupP/setUP=> [[i] | ].
  by case/setUP; [left | right]; apply/bigcupP; exists i.
by case=> /bigcupP[i Pi]; exists i; rewrite // inE Pi ?orbT.
Qed.

Lemma bigcup_seq r F : \bigcup_(i <- r) F i = \bigcup_(i \in r) F i.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil big_pred0.
rewrite big_cons {}IHr; case r_i: (i \in r).
  rewrite (setUidPr _) ?bigcup_sup //.
  by apply: eq_bigl => j; rewrite !inE; case: eqP => // ->.
rewrite (bigD1 i (mem_head i r)) /=; congr (_ :|: _).
by apply: eq_bigl => j /=; rewrite andbC; case: eqP => // ->.
Qed.

(* Unlike its setU counterpart, this lemma is useable. *)
Lemma bigcap_inf j P F : P j -> \bigcap_(i | P i) F i \subset F j.
Proof. by move=> Pj; rewrite (bigD1 j) //= subsetIl. Qed.

Lemma bigcap_min j U P F :
  P j -> F j \subset U -> \bigcap_(i | P i) F i \subset U.
Proof. by move=> Pj; exact: subset_trans (bigcap_inf _ Pj). Qed.

Lemma bigcapsP U P F :
  reflect (forall i, P i -> U \subset F i) (U \subset \bigcap_(i | P i) F i).
Proof.
apply: (iffP idP) => [sUF i Pi | sUF].
  apply: subset_trans sUF _; exact: bigcap_inf.
elim/big_rec: _ => [|i V Pi sUV]; apply/subsetP=> x Ux; rewrite inE //.
by rewrite !(subsetP _ x Ux) ?sUF.
Qed.

Lemma bigcapP x P F :
  reflect (forall i, P i -> x \in F i) (x \in \bigcap_(i | P i) F i).
Proof.
rewrite -sub1set.
by apply: (iffP (bigcapsP _ _ _)) => Fx i /Fx; rewrite sub1set.
Qed.

Lemma setC_bigcup J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcup_(j <- r | P j) F j) = \bigcap_(j <- r | P j) ~: F j.
Proof. by apply: big_morph => [A B|]; rewrite ?setC0 ?setCU. Qed.

Lemma setC_bigcap J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcap_(j <- r | P j) F j) = \bigcup_(j <- r | P j) ~: F j.
Proof. by apply: big_morph => [A B|]; rewrite ?setCT ?setCI. Qed.

Lemma bigcap_setU A B F :
  (\bigcap_(i \in A :|: B) F i) =
    (\bigcap_(i \in A) F i) :&: (\bigcap_(i \in B) F i).
Proof. by apply: setC_inj; rewrite setCI !setC_bigcap bigcup_setU. Qed.

Lemma bigcap_seq r F : \bigcap_(i <- r) F i = \bigcap_(i \in r) F i.
Proof. by apply: setC_inj; rewrite !setC_bigcap bigcup_seq. Qed.

End BigSetOps.

Implicit Arguments bigcup_sup [T I P F].
Implicit Arguments bigcup_max [T I U P F].
Implicit Arguments bigcupP [T I x P F].
Implicit Arguments bigcupsP [T I U P F].
Implicit Arguments bigcap_inf [T I P F].
Implicit Arguments bigcap_min [T I U P F].
Implicit Arguments bigcapP [T I x P F].
Implicit Arguments bigcapsP [T I U P F].
Prenex Implicits bigcupP bigcupsP bigcapP bigcapsP.

Section ImsetCurry.

Variables (aT1 aT2 rT : finType) (f : aT1 -> aT2 -> rT).

Section Curry.

Variables (A1 : {set aT1}) (A2 : {set aT2}).
Variables (D1 : pred aT1) (D2 : pred aT2).

Lemma curry_imset2X : f @2: (A1, A2) = prod_curry f @: (setX A1 A2).
Proof.
rewrite [@imset]unlock unlock; apply/setP=> x; rewrite !in_set.
by apply: eq_image => u //=; rewrite inE.
Qed.

Lemma curry_imset2l : f @2: (D1, D2) = \bigcup_(x1 \in D1) f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x1 Dx1]].
  by exists x1; rewrite // mem_imset.
by case/imsetP=> x2 Dx2 ->{y}; exists x1 x2.
Qed.

Lemma curry_imset2r : f @2: (D1, D2) = \bigcup_(x2 \in D2) f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x2 Dx2]].
  by exists x2; rewrite // (mem_imset (f^~ x2)).
by case/imsetP=> x1 Dx1 ->{y}; exists x1 x2.
Qed.

End Curry.

Lemma imset2Ul (A B : {set aT1}) (C : {set aT2}) :
  f @2: (A :|: B, C) = f @2: (A, C) :|: f @2: (B, C).
Proof. by rewrite !curry_imset2l bigcup_setU. Qed.

Lemma imset2Ur (A : {set aT1}) (B C : {set aT2}) :
  f @2: (A, B :|: C) = f @2: (A, B) :|: f @2: (A, C).
Proof. by rewrite !curry_imset2r bigcup_setU. Qed.

End ImsetCurry.

Section Partitions.

Variable T I : finType.
Implicit Types A B D : {set T}.
Implicit Type J : {set I}.
Implicit Types F : I -> {set T}.
Implicit Types P Q : {set {set T}}.

Definition cover P := \bigcup_(A \in P) A.
Definition trivIset P := \sum_(A \in P) #|A| == #|cover P|.
Definition partition P D := [&& cover P == D, trivIset P & set0 \notin P].

Lemma leq_card_setU A B : #|A :|: B| <= #|A| + #|B| ?= iff [disjoint A & B].
Proof.
rewrite -(addn0 #|_|) -setI_eq0 -cards_eq0 -cardsUI eq_sym.
exact/(monotone_leqif (leq_add2l _)).
Qed.

Lemma leq_card_cover P :
  #|cover P| <= \sum_(A \in P) #|A| ?= iff trivIset P.
Proof.
split; last exact: eq_sym.
rewrite /cover; elim/big_rec2: _ => [|A n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU A U).1) ?leq_add2l.
Qed.

Lemma trivIsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]} (trivIset P).
Proof.
have->: P = [set x \in enum (mem P)] by apply/setP=> x; rewrite inE mem_enum.
elim: {P}(enum _) (enum_uniq (mem P)) => [_ | A e IHe] /=.
  by rewrite /trivIset /cover !big_set0 cards0; left=> A; rewrite inE.
case/andP; rewrite set_cons -(in_set (fun B => B \in e)) => PA {IHe}/IHe.
move: {e}[set x \in e] PA => P PA IHP.
rewrite /trivIset /cover !big_setU1 //= eq_sym.
move/(monotone_leqif (leq_add2l #|A|)): (leq_card_cover P).
move/(leqif_trans (leq_card_setU _ _))->; rewrite disjoints_subset setC_bigcup.
case: bigcapsP => [disjA | meetA]; last first.
  right=> [tI]; case: meetA => B PB; rewrite -disjoints_subset.
  by rewrite tI ?setU11 ?setU1r //; apply: contraNneq PA => ->.
apply: (iffP IHP) => [] tI B C PB PC; last by apply: tI; exact: setU1r.
by case/setU1P: PC PB => [->|PC] /setU1P[->|PB]; try by [exact: tI | case/eqP];
  first rewrite disjoint_sym; rewrite disjoints_subset disjA.
Qed.

Lemma trivIsetI P D : trivIset P -> trivIset (P ::&: D).
Proof.
move/trivIsetP=> tI; apply/trivIsetP => A B /setIdP[PA _] /setIdP[PB _].
exact: tI.
Qed.

Lemma cover_setI P D : cover (P ::&: D) \subset cover P :&: D.
Proof.
apply/bigcupsP=> A /setIdP[PA sAD].
by rewrite subsetI sAD andbT (bigcup_max A).
Qed.

Definition cover_at x P := odflt set0 (pick [pred A \in P | x \in A]).

Lemma mem_cover_at P x : (x \in cover_at x P) = (x \in cover P).
Proof.
rewrite /cover_at; symmetry; apply/bigcupP.
case: pickP => /= [A /andP[PA Ax]| noA]; first by rewrite Ax; exists A.
by rewrite inE => [[A PA Ax]]; case/andP: (noA A).
Qed.

Lemma cover_at_mem P x : x \in cover P -> cover_at x P \in P.
Proof.
rewrite -mem_cover_at /cover_at.
by case: pickP => [A /andP[]| _] //=; rewrite inE.
Qed.

Lemma cover_at_eq P A x :
  trivIset P -> A \in P -> (x \in cover P) && (cover_at x P == A) = (x \in A).
Proof.
move/trivIsetP=> tI PA; rewrite -mem_cover_at /cover_at.
case: pickP => /= [B /andP[PB Bx]| /(_ A)]; last by rewrite /= inE PA.
rewrite Bx; apply/eqP/idP=> [<- // | Ax].
by apply/(contraNeq (tI B A PB PA))/pred0Pn; exists x; exact/andP.
Qed.

Lemma same_cover_at P x y :
  trivIset P -> x \in cover_at y P -> cover_at x P = cover_at y P.
Proof.
rewrite {1 3}/cover_at => tI; case: pickP => [A|]; last by rewrite inE.
by case/andP=> PA _{y} /=; rewrite -(cover_at_eq _ tI) // => /andP[_ /eqP].
Qed.

Lemma trivIsetU1 A P :
    {in P, forall B, [disjoint A & B]} -> trivIset P -> set0 \notin P ->
  trivIset (A |: P) /\ A \notin P.
Proof.
move=> tiAP tiP notPset0; split; last first.
  apply: contra notPset0 => P_A.
  by have:= tiAP A P_A; rewrite -setI_eq0 setIid => /eqP <-.
apply/trivIsetP=> B1 B2 /setU1P[->|PB1] /setU1P[->|PB2];
  by [exact: (trivIsetP _ tiP) | rewrite ?eqxx // ?(tiAP, disjoint_sym)].
Qed.

Lemma cover_imset J F : cover (F @: J) = \bigcup_(i \in J) F i.
Proof.
apply/setP=> x.
apply/bigcupP/bigcupP=> [[_ /imsetP[i Ji ->]] | [i]]; first by exists i.
by exists (F i); first exact: mem_imset.
Qed.

Lemma trivIimset J F (P := F @: J) :
    {in J &, forall i j, j != i -> [disjoint F i & F j]} -> set0 \notin P ->
  trivIset P /\ {in J &, injective F}.
Proof.
move=> tiF notPset0; split=> [|i j Ji Jj /= eqFij].
  apply/trivIsetP=> _ _ /imsetP[i Ji ->] /imsetP[j Jj ->] neqFij.
  by rewrite tiF // (contraNneq _ neqFij) // => ->.
apply: contraNeq notPset0 => neq_ij; apply/imsetP; exists i => //; apply/eqP.
by rewrite eq_sym -[F i]setIid setI_eq0 {1}eqFij tiF.
Qed.

Section BigOps.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Let rhs_cond P K E := \big[op/idx]_(A \in P) \big[op/idx]_(x \in A | K x) E x.
Let rhs P E := \big[op/idx]_(A \in P) \big[op/idx]_(x \in A) E x.

Lemma big_trivIset_cond P (K : pred T) (E : T -> R) :
  trivIset P -> \big[op/idx]_(x \in cover P | K x) E x = rhs_cond P K E.
Proof.
move=> tiP; rewrite (partition_big (cover_at^~ P) (mem P)) -/op => [|x].
  by apply: eq_bigr => A PA; apply: eq_bigl => x; rewrite andbAC cover_at_eq.
by case/andP=> Px _; exact: cover_at_mem.
Qed.

Lemma big_trivIset P (E : T -> R) :
  trivIset P -> \big[op/idx]_(x \in cover P) E x = rhs P E.
Proof.
have biginT := eq_bigl _ _ (fun _ => andbT _) => tiP.
by rewrite -biginT big_trivIset_cond //; apply: eq_bigr => A _; exact: biginT.
Qed.

Lemma set_partition_big_cond P D (K : pred T) (E : T -> R) :
  partition P D -> \big[op/idx]_(x \in D | K x) E x = rhs_cond P K E.
Proof. by case/and3P=> /eqP <- tI_P _; exact: big_trivIset_cond. Qed.

Lemma set_partition_big P D (E : T -> R) :
  partition P D -> \big[op/idx]_(x \in D) E x = rhs P E.
Proof. by case/and3P=> /eqP <- tI_P _; exact: big_trivIset. Qed.

End BigOps.

Section Preim.

Variables (rT : eqType) (f : T -> rT).

Definition preim_at x := f @^-1: pred1 (f x).
Definition preim_partition D := [set D :&: preim_at x | x <- D].

Lemma preim_partitionP D : partition (preim_partition D) D.
Proof.
apply/and3P; split.
- apply/eqP/setP=> x; apply/bigcupP/idP=> [[_ /imsetP[y _ ->] /setIP[]//] | Dx].
  by exists (D :&: preim_at x); [exact: mem_imset | rewrite !inE Dx /=].
- apply/trivIsetP=> _ _ /imsetP[x _ ->] /imsetP[y _ ->]; apply: contraR.
  case/existsP=> z; rewrite !inE /preim_at -andbA => /andP[-> /=] /andP[].
  by do 2!move/eqP->.
apply/imsetP=> [[x Dx /eqP]]; rewrite eq_sym.
by case/set0Pn; exists x; rewrite !inE Dx /=.
Qed.

End Preim.

Lemma card_partition D P : partition P D -> #|D| = \sum_(A \in P) #|A|.
Proof. by case/and3P=> /eqP <- /eqnP. Qed.

Lemma card_uniform_partition D P n :
  {in P, forall A, #|A| = n} -> partition P D -> #|D| = #|P| * n.
Proof.
by move=> uniP /card_partition->; rewrite -sum_nat_const; exact: eq_bigr.
Qed.

End Partitions.

Implicit Arguments trivIsetP [T P].
Implicit Arguments big_trivIset_cond [T R idx op K E].
Implicit Arguments set_partition_big_cond [T R idx op D K E].
Implicit Arguments big_trivIset [T R idx op E].
Implicit Arguments set_partition_big [T R idx op D E].

Prenex Implicits cover trivIset partition cover_at trivIsetP.
Prenex Implicits preim_at preim_partition.

(**********************************************************************)
(*                                                                    *)
(*  Maximum and minimun (sub)set with respect to a given pred         *)
(*                                                                    *)
(**********************************************************************)

Section MaxSetMinSet.

Variable T : finType.
Notation sT := {set T}.
Implicit Types A B C : sT.
Implicit Type P : pred sT.

Definition minset P A := forallb B : sT, (B \subset A) ==> ((B == A) == P B).

Lemma minset_eq P1 P2 A : P1 =1 P2 -> minset P1 A = minset P2 A.
Proof. by move=> eP12; apply: eq_forallb => B; rewrite eP12. Qed.

Lemma minsetP P A :
  reflect ((P A) /\ (forall B, P B -> B \subset A -> B = A)) (minset P A).
Proof.
apply: (iffP forallP) => [minA | [PA minA] B].
  split; first by have:= minA A; rewrite subxx eqxx /= => /eqP.
  by move=> B PB sBA; have:= minA B; rewrite PB sBA /= eqb_id => /eqP.
by apply/implyP=> sBA; apply/eqP; apply/eqP/idP=> [-> // | /minA]; exact.
Qed.
Implicit Arguments minsetP [P A].

Lemma minsetp P A : minset P A -> P A.
Proof. by case/minsetP. Qed.

Lemma minsetinf P A B : minset P A -> P B -> B \subset A -> B = A.
Proof. by case/minsetP=> _; exact. Qed.

Lemma ex_minset P : (exists A, P A) -> {A | minset P A}.
Proof.
move=> exP; pose pS n := [pred B | P B && (#|B| == n)].
pose p n := ~~ pred0b (pS n); have{exP}: exists n, p n.
  by case: exP => A PA; exists #|A|; apply/existsP; exists A; rewrite /= PA /=.
case/ex_minnP=> n /pred0P; case: (pickP (pS n)) => // A /andP[PA] /eqP <-{n} _.
move=> minA; exists A => //; apply/minsetP; split=> // B PB sBA; apply/eqP.
by rewrite eqEcard sBA minA //; apply/pred0Pn; exists B; rewrite /= PB /=.
Qed.

Lemma minset_exists P C : P C -> {A | minset P A & A \subset C}.
Proof.
move=> PC; have{PC}: exists A, P A && (A \subset C) by exists C; rewrite PC /=.
case/ex_minset=> A /minsetP[/andP[PA sAC] minA]; exists A => //; apply/minsetP.
by split=> // B PB sBA; rewrite (minA B) // PB (subset_trans sBA).
Qed.

(* The 'locked' allows Coq to find the value of P by unification. *)
Definition maxset P A := minset (fun B => locked P (~: B)) (~: A).

Lemma maxset_eq P1 P2 A : P1 =1 P2 -> maxset P1 A = maxset P2 A.
Proof. by move=> eP12; apply: minset_eq=> x /=; rewrite -!lock eP12. Qed.

Lemma maxminset P A : maxset P A = minset [pred B | P (~: B)] (~: A).
Proof. by unlock maxset. Qed.

Lemma minmaxset P A : minset P A = maxset [pred B | P (~: B)] (~: A).
Proof.
by unlock maxset; rewrite setCK; apply: minset_eq => B /=; rewrite setCK.
Qed.

Lemma maxsetP P A :
  reflect ((P A) /\ (forall B, P B -> A \subset B -> B = A)) (maxset P A).
Proof.
apply: (iffP minsetP); rewrite ?setCK -lock => [] [PA minA].
  by split=> // B PB sAB; rewrite -[B]setCK [~: B]minA (setCK, setCS).
by split=> // B PB' sBA'; rewrite -(minA _ PB') -1?setCS setCK.
Qed.

Lemma maxsetp P A : maxset P A -> P A.
Proof. by case/maxsetP. Qed.

Lemma maxsetsup P A B : maxset P A -> P B -> A \subset B -> B = A.
Proof. by case/maxsetP=> _; exact. Qed.

Lemma ex_maxset P : (exists A, P A) -> {A | maxset P A}.
Proof.
move=> exP; have{exP}: exists A, P (~: A).
  by case: exP => A PA; exists (~: A); rewrite setCK.
by case/ex_minset=> A minA; exists (~: A); unlock maxset; rewrite setCK.
Qed.

Lemma maxset_exists P C : P C -> {A : sT | maxset P A & C \subset A}.
Proof.
move=> PC; pose P' B := P (~: B); have: P' (~: C) by rewrite /P' setCK.
case/minset_exists=> B; rewrite -[B]setCK setCS.
by exists (~: B); unlock maxset.
Qed.

End MaxSetMinSet.

Implicit Arguments minsetP [T P A].
Implicit Arguments maxsetP [T P A].
Prenex Implicits minset maxset minsetP maxsetP.


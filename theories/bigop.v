(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype.
Require Import finfun path.

(****************************************************************************)
(* This file provides a generic definition for iterating an operator over a *)
(* set of indexes (reducebig); this big operator is parametrized by the     *)
(* return type (R), the type of indexes (I), the operator (op), the default *)
(* value on empty lists (idx), the range of indexes (r), the filter applied *)
(* on this range (P) and the expression we are iterating (F). The definition*)
(* is not to be used directly, but via the wide range of notations provided *)
(* and which allows a natural use of big operators.                         *)
(*   The lemmas can be classified according to the operator being iterated: *)
(* 1. results independent of the operator: extensionality with respect to   *)
(*     the range  of indexes, to the filtering predicate or to the          *)
(*     expression being iterated; reindexing, widening or narrowing of the  *)
(*     range of indexes; we provide lemmas for the special case where       *)
(*     indexes are natural numbers                                          *)
(* 2. results depending on the properties of the operator:                  *)
(*     we distinguish: monoid laws (op is associative, idx is the neutral   *)
(*     element), abelian monoid laws (op is also comutative), the case      *)
(*     where we have 2 operators compatible with a certain property, the    *)
(*     case of 2 operators compatible with a certain relation (e.g. order)  *)
(*     the case of 2 operators that interact through distributivity (e.g.   *)
(*     the addition and multiplication in a ring structure).                *)
(* A special section is dedicated to big operators on natural numbers.      *)
(****************************************************************************)
(* Notations:                                                               *)
(* The general form for iterated operators is                               *)
(*         <bigop>_<range> <general_term>                                   *)
(* - <bigop> is one of \big[op/idx], \sum, \prod, or \max (see below)       *)
(* - <range> binds an index variable (say, i) in <general_term>, which can  *)
(*   be any expression; <range> is one of                                   *)
(*    (i <- s)     i ranges over the sequence s                             *)
(*    (m <= i < n) i ranges over the nat interval m, m.+1, ..., n.-1        *)
(*    (i < n)      i ranges over the (finite) type 'I_n (i.e., ordinal n)   *)
(*    (i : T)      i ranges over the finite type T                          *)
(*    i or (i)     i ranges over its (inferred) finite type                 *)
(*    (i \in A)    i ranges over the elements that satisfy the collective   *)
(*                 predicate A (the domain of A must be a finite type)      *)
(*    (i <- s | C) limits the range to those i for which C holds (i is thus *)
(*                 bound in C); works with all six kinds of ranges above.   *)
(* - the fall-back notation <bigop>_(<- s | predicate) function is used if  *)
(*   the Coq display algorithm fails to recognize any of the above (such    *)
(*   as when <general_term> does not depend on i);                          *)
(* - one can use the "\big[op/idx]" notations for any operator;             *)
(* - the "\sum", "\prod" and "\max"  notations in nat_scope are used for    *)
(*   natural numbers with addition, multiplication and maximum (and their   *)
(*   corresponding neutral elements), respectively;                         *)
(* - the "\sum" and "\prod" reserved notations are re-bounded in ssralg.v   *)
(*   in ring_scope to the addition and multiplication big operators of a    *)
(*   ring, and, in fingroup.v/group_scope, to iterated group product.       *)
(* - finset.v defines "\bigcup" and "\bigcap" notations for iterated        *)
(*   union and intersection.                                                *)
(****************************************************************************)
(* Tips for using lemmas in this file:                                      *)
(* to apply a lemma for a specific operator: if no special property is      *)
(* required for the operator, simply apply the lemma; if the lemma needs    *)
(* certain properties for the operator, make sure the appropriate           *)
(* Canonical Structures are declared.                                       *)
(****************************************************************************)
(* Interfaces for operator properties are paclaged in the Monoid submodule: *)
(*     Monoid.law idx == interface (keyed on the operator) for associative  *)
(*                       operators with identity element idx.               *)
(* Monoid.com_law idx == extension (telescope) of Monoid.law for operators  *)
(*                       that are also associative.                         *)
(* Monoid.mul_law abz == interface for operators with absorbing (zero)      *)
(*                       element abz.                                       *)
(* Monoid.add_law idx mop == extension of Monoid.com_law for operators over *)
(*                       which operation mop distributes (mop will often    *)
(*                       also have a Monoid.mul_law idx structure).         *)
(* [law of op], [com_law of op], [mul_law of op], [add_law mop of op] ==    *)
(*                       syntax for cloning Monoid structures.              *)
(*     Monoid.Theory == submodule containing basic generic algebra lemmas   *)
(*                      for operators satisfying the Monoid interfaces.     *)
(*      Monoid.simpm == generic monoid simplification rewrite multirule.    *)
(* Monoid structures are predeclared for many basic operators: (_ && _)%B,  *)
(* (_ || _)%B, (_ (+) _)%B (exclucive or) , (_ + _)%N, (_ * _)%N, maxn,     *)
(* gcdn, lcmn and (_ ++ _)%SEQ (list concatenation).                        *)
(****************************************************************************)
(* Additional documentation for this file:                                  *)
(* Y. Bertot, G. Gonthier, S. Ould Biha and I. Pasca.                       *)
(* Canonical Big Operators. In TPHOLs 2008, LNCS vol. 5170, Springer.       *)
(* Article available at:                                                    *)
(*     http://hal.inria.fr/docs/00/33/11/93/PDF/main.pdf                    *)
(****************************************************************************)
(* Examples of use in: poly.v, matrix.v                                     *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, r at level 50,
           format "'[' \big [ op / idx ]_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i \in A | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i \in A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\sum_ i F"
  (at level 41, F at level 41, i at level 0,
           right associativity,
           format "'[' \sum_ i '/  '  F ']'").
Reserved Notation "\sum_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \sum_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\max_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \max_ i '/  '  F ']'").
Reserved Notation "\max_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \max_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \max_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n )  F ']'").
Reserved Notation "\max_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\prod_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \prod_ i '/  '  F ']'").
Reserved Notation "\prod_ ( <- r | P ) F"
  (at level 36, F at level 36, r at level 50,
           format "'[' \prod_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i \in A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  \in  A  |  P )  F ']'").
Reserved Notation "\prod_ ( i \in A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  \in  A ) '/  '  F ']'").

Module Monoid.

Section Definitions.
Variables (T : Type) (idm : T).

Structure law : Type := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : left_id idm operator;
  _ : right_id idm operator
}.
Local Coercion operator : law >-> Funclass.

Structure com_law : Type := ComLaw {
   com_operator : law;
   _ : commutative com_operator
}.
Local Coercion com_operator : com_law >-> law.

Structure mul_law : Type := MulLaw {
  mul_operator : T -> T -> T;
  _ : left_zero idm mul_operator;
  _ : right_zero idm mul_operator
}.
Local Coercion mul_operator : mul_law >-> Funclass.

Structure add_law (mul : T -> T -> T) : Type := AddLaw {
  add_operator : com_law;
  _ : left_distributive mul add_operator;
  _ : right_distributive mul add_operator
}.
Local Coercion add_operator : add_law >-> com_law.

Let op_id (op1 op2 : T -> T -> T) := phant_id op1 op2.

Definition clone_law op :=
  fun (opL : law) & op_id opL op =>
  fun opmA op1m opm1 (opL' := @Law op opmA op1m opm1)
    & phant_id opL' opL => opL'.

Definition clone_com_law op :=
  fun (opL : law) (opC : com_law) & op_id opL op & op_id opC op =>
  fun opmC (opC' := @ComLaw opL opmC) & phant_id opC' opC => opC'.

Definition clone_mul_law op :=
  fun (opM : mul_law) & op_id opM op =>
  fun op0m opm0 (opM' := @MulLaw op op0m opm0) & phant_id opM' opM => opM'.

Definition clone_add_law mop aop :=
  fun (opC : com_law) (opA : add_law mop) & op_id opC aop & op_id opA aop =>
  fun mopDm mopmD (opA' := @AddLaw mop opC mopDm mopmD)
    & phant_id opA' opA => opA'.

End Definitions.

Module Import Exports.
Coercion operator : law >-> Funclass.
Coercion com_operator : com_law >-> law.
Coercion mul_operator : mul_law >-> Funclass.
Coercion add_operator : add_law >-> com_law.
Notation "[ 'law' 'of' f ]" := (@clone_law _ _ f _ id _ _ _ id)
  (at level 0, format"[ 'law'  'of'  f ]") : form_scope.
Notation "[ 'com_law' 'of' f ]" := (@clone_com_law _ _ f _ _ id id _ id)
  (at level 0, format "[ 'com_law'  'of'  f ]") : form_scope.
Notation "[ 'mul_law' 'of' f ]" := (@clone_mul_law _ _ f _ id _ _ id)
  (at level 0, format"[ 'mul_law'  'of'  f ]") : form_scope.
Notation "[ 'add_law' m 'of' a ]" := (@clone_add_law _ _ m a _ _ id id _ _ id)
  (at level 0, format "[ 'add_law'  m  'of'  a ]") : form_scope.
End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T) (inv : T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof. by move=>  mul1x x; rewrite mulC. Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof. by move=> mul0x x; rewrite mulC. Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof. by move=> mul_addl x y z; rewrite !(mulC x). Qed.

End CommutativeAxioms.

Module Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul. Proof. by case mul. Qed.
Lemma mulm1 : right_id idm mul. Proof. by case mul. Qed.
Lemma mulmA : associative mul. Proof. by case mul. Qed.
Lemma iteropE : forall n x, iterop n mul x idm = iter n (mul x) idm.
Proof. by case=> // n x; rewrite iterSr mulm1 iteropS. Qed.
End Plain.

Section Commutative.
Variable mul : com_law idm.
Lemma mulmC : commutative mul. Proof. by case mul. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA (mulmC x). Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA (mulmC y). Qed.
End Commutative.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul. Proof. by case mul. Qed.
Lemma mulm0 : right_zero idm mul. Proof. by case mul. Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_id idm add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_id idm add. Proof. exact: mulm1. Qed.
Lemma mulm_addl : left_distributive mul add. Proof. by case add. Qed.
Lemma mulm_addr : right_distributive mul add. Proof. by case add. Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

End Theory.
Include Theory.

End Monoid.
Export Monoid.Exports.

Section PervasiveMonoids.

Import Monoid.

Canonical Structure andb_monoid := Law andbA andTb andbT.
Canonical Structure andb_comoid := ComLaw andbC.

Canonical Structure andb_muloid := MulLaw andFb andbF.
Canonical Structure orb_monoid := Law orbA orFb orbF.
Canonical Structure orb_comoid := ComLaw orbC.
Canonical Structure orb_muloid := MulLaw orTb orbT.
Canonical Structure addb_monoid := Law addbA addFb addbF.
Canonical Structure addb_comoid := ComLaw addbC.
Canonical Structure orb_addoid := AddLaw andb_orl andb_orr.
Canonical Structure andb_addoid := AddLaw orb_andl orb_andr.
Canonical Structure addb_addoid := AddLaw andb_addl andb_addr.

Canonical Structure addn_monoid := Law addnA add0n addn0.
Canonical Structure addn_comoid := ComLaw addnC.
Canonical Structure muln_monoid := Law mulnA mul1n muln1.
Canonical Structure muln_comoid := ComLaw mulnC.
Canonical Structure muln_muloid := MulLaw mul0n muln0.
Canonical Structure addn_addoid := AddLaw muln_addl muln_addr.

Canonical Structure maxn_monoid := Law maxnA max0n maxn0.
Canonical Structure maxn_comoid := ComLaw maxnC.
Canonical Structure maxn_addoid := AddLaw maxn_mull maxn_mulr.

Canonical Structure gcdn_monoid := Law gcdnA gcd0n gcdn0.
Canonical Structure gcdn_comoid := ComLaw gcdnC.
Canonical Structure gcdn_addoid := AddLaw muln_gcdl muln_gcdr.

Canonical Structure lcmn_monoid := Law lcmnA lcm1n lcmn1.
Canonical Structure lcmn_comoid := ComLaw lcmnC.
Canonical Structure lcmn_addoid := AddLaw muln_lcml muln_lcmr.

Canonical Structure cat_monoid T := Law (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.

(* Unit test for the [...law of ...] Notations
Definition myp := addn. Definition mym := muln.
Canonical Structure myp_mon := [law of myp].
Canonical Structure myp_cmon := [com_law of myp].
Canonical Structure mym_mul := [mul_law of mym].
Canonical Structure myp_add := [add_law _ of myp].
Print myp_add.
Print Canonical Projections.
*)

Delimit Scope big_scope with BIG.
Open Scope big_scope.

Definition reducebig R I idx op r (P : pred I) (F : I -> R) : R :=
  foldr (fun i x => if P i then op (F i) x else x) idx r.

Module Type BigOpSig.
Parameter bigop : forall R I,
   R -> (R -> R -> R) -> seq I -> pred I -> (I -> R) -> R.
Axiom bigopE : bigop = reducebig.
End BigOpSig.

Module BigOp : BigOpSig.
Definition bigop := reducebig.
Lemma bigopE : bigop = reducebig. Proof. by []. Qed.
End BigOp.

Notation bigop := BigOp.bigop (only parsing).
Canonical Structure bigop_unlock := Unlockable BigOp.bigopE.

Definition index_iota m n := iota m (n - m).

Definition index_enum (T : finType) := Finite.enum T.

Lemma mem_index_iota : forall m n i, i \in index_iota m n = (m <= i < n).
Proof.
move=> m n i; rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_sub_add leq_subS // -subn_gt0 subn_sub subnKC // subn_gt0.
Qed.

Lemma filter_index_enum : forall T P, filter P (index_enum T) = enum P.
Proof. by []. Qed.

Notation "\big [ op / idx ]_ ( <- r | P ) F" :=
  (bigop idx op r P F) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (bigop idx op r (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (bigop idx op r (fun _ => true) (fun  i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (bigop idx op (index_iota m n) (fun i : nat => P%B) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop idx op (index_iota m n) (fun _ => true) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (bigop idx op (index_enum _) (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ i F" :=
  (bigop idx op (index_enum _) (fun _ => true) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx op (index_enum _) (fun i : t => P%B) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (bigop idx op (index_enum _) (fun _ => true) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n | P ) F" :=
  (\big[op/idx]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / idx ]_ ( i \in A | P ) F" :=
  (\big[op/idx]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / idx ]_ ( i \in A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

Notation Local "+%N" := addn (at level 0, only parsing).
Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%N/0%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%N/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%N/0%N]_(i <- r) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%N/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\sum_ i F" :=
  (\big[+%N/0%N]_i F%N) : nat_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%N/0%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%N/0%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%N/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%N/0%N]_(i < n) F%N) : nat_scope.
Notation "\sum_ ( i \in A | P ) F" :=
  (\big[+%N/0%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\sum_ ( i \in A ) F" :=
  (\big[+%N/0%N]_(i \in A) F%N) : nat_scope.

Notation Local "*%N" := muln (at level 0, only parsing).
Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%N/1%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%N/1%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%N/1%N]_(i <- r) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%N/1%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%N/1%N]_(m <= i < n) F%N) : nat_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%N/1%N]_(i | P%B) F%N) : nat_scope.
Notation "\prod_ i F" :=
  (\big[*%N/1%N]_i F%N) : nat_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%N/1%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%N/1%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%N/1%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%N/1%N]_(i < n) F%N) : nat_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[*%N/1%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[*%N/1%N]_(i \in A) F%N) : nat_scope.

Notation "\max_ ( <- r | P ) F" :=
  (\big[maxn/0%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r | P ) F" :=
  (\big[maxn/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[maxn/0%N]_(i <- r) F%N) : nat_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[maxn/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\max_ i F" :=
  (\big[maxn/0%N]_i F%N) : nat_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[maxn/0%N]_(i : I | P%B) F%N) (only parsing) : nat_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[maxn/0%N]_(i : I) F%N) (only parsing) : nat_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
 (\big[maxn/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( m <= i < n ) F" :=
 (\big[maxn/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\max_ ( i < n | P ) F" :=
 (\big[maxn/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[maxn/0%N]_(i < n) F%N) : nat_scope.
Notation "\max_ ( i \in A | P ) F" :=
 (\big[maxn/0%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\max_ ( i \in A ) F" :=
 (\big[maxn/0%N]_(i \in A) F%N) : nat_scope.

(* Redundant, unparseable notation to print some constant sums and products. *)
Notation "\su 'm_' ( i | P ) e" :=
  (\sum_(<- index_enum _ | (fun i => P)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  |  P )  e") : nat_scope.

Notation "\su 'm_' ( i \in A ) e" :=
  (\sum_(<- index_enum _ | (fun i => i \in A)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  \in  A )  e") : nat_scope.

Notation "\su 'm_' ( i \in A | P ) e" :=
  (\sum_(<- index_enum _ | (fun i => (i \in A) && P)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  \in  A  |  P )  e")
    : nat_scope.

Notation "\pro 'd_' ( i | P ) e" :=
  (\prod_(<- index_enum _ | (fun i => P)) (fun _ => e%N))
  (at level 36, e at level 36, format "\pro 'd_' ( i  |  P )  e") : nat_scope.

Section Extensionality.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Section SeqExtension.

Variable I : Type.

Lemma big_filter : forall r (P : pred I) F,
  \big[op/idx]_(i <- filter P r) F i = \big[op/idx]_(i <- r | P i) F i.
Proof. by rewrite unlock => r P F; elim: r => //= i r <-; case (P i). Qed.

Lemma big_filter_cond : forall r (P1 P2 : pred I) F,
  \big[op/idx]_(i <- filter P1 r | P2 i) F i
     = \big[op/idx]_(i <- r | P1 i && P2 i) F i.
Proof.
move=> r P1 P2 F; rewrite -big_filter -(big_filter r); congr bigop.
rewrite -filter_predI; apply: eq_filter => i; exact: andbC.
Qed.

Lemma eq_bigl : forall r (P1 P2 : pred I) F, P1 =1 P2 ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Proof.
by move=> r P1 P2 F eqP12; rewrite -big_filter (eq_filter eqP12) big_filter.
Qed.

Lemma eq_bigr : forall r (P : pred I) F1 F2, (forall i, P i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof.
move=> r P F1 F2 eqF12; rewrite unlock.
by elim: r => //= x r ->; case Px: (P x); rewrite // eqF12.
Qed.

Lemma eq_big : forall r (P1 P2 : pred I) F1 F2,
  P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P1 i) F1 i = \big[op/idx]_(i <- r | P2 i) F2 i.
Proof. by move=> r P1 P2 F1 F2; move/eq_bigl <-; move/eq_bigr->. Qed.

Lemma congr_big : forall r1 r2 (P1 P2 : pred I) F1 F2,
  r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
    \big[op/idx]_(i <- r1 | P1 i) F1 i = \big[op/idx]_(i <- r2 | P2 i) F2 i.
Proof. move=> r1 r2 P1 P2 F1 F2 <-{r2}; exact: eq_big. Qed.

Lemma big_nil : forall (P : pred I) F,
  \big[op/idx]_(i <- [::] | P i) F i = idx.
Proof. by rewrite unlock. Qed.

Lemma big_cons : forall i r (P : pred I) F,
  let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- i :: r | P j) F j = if P i then op (F i) x else x.
Proof. by rewrite unlock. Qed.

Lemma big_map : forall (J : eqType) (h : J -> I) r (P : pred I) F,
  \big[op/idx]_(i <- map h r | P i) F i
     = \big[op/idx]_(j <- r | P (h j)) F (h j).
Proof. by rewrite unlock => J h r P F; elim: r => //= j r ->. Qed.

Lemma big_nth : forall x0 r (P : pred I) F,
  \big[op/idx]_(i <- r | P i) F i
     = \big[op/idx]_(0 <= i < size r | P (nth x0 r i)) (F (nth x0 r i)).
Proof.
by move=> x0 r P F; rewrite -{1}(mkseq_nth x0 r) big_map /index_iota subn0.
Qed.

Lemma big_hasC : forall r (P : pred I) F,
  ~~ has P r -> \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
move=> r P F; rewrite -big_filter has_count count_filter.
case: filter => // _; exact: big_nil.
Qed.

Lemma big_pred0_eq : forall (r : seq I) F,
  \big[op/idx]_(i <- r | false) F i = idx.
Proof. by move=> r F; rewrite big_hasC // has_pred0. Qed.

Lemma big_pred0 : forall r (P : pred I) F, P =1 xpred0 ->
  \big[op/idx]_(i <- r | P i) F i = idx.
Proof. move=> r P F; move/eq_bigl->; exact: big_pred0_eq. Qed.

Lemma big_cat_nested : forall r1 r2 (P : pred I) F,
  let x := \big[op/idx]_(i <- r2 | P i) F i in
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/x]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite unlock /reducebig foldr_cat. Qed.

Lemma big_catl : forall r1 r2 (P : pred I) F, ~~ has P r2 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite big_cat_nested; move/big_hasC->. Qed.

Lemma big_catr : forall r1 r2 (P : pred I) F, ~~ has P r1 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r2 | P i) F i.
Proof.
move=> r1 r2 P F; rewrite -big_filter -(big_filter r2) filter_cat.
by rewrite has_count count_filter; case: filter.
Qed.

Lemma big_const_seq : forall r (P : pred I) x,
  \big[op/idx]_(i <- r | P i) x = iter (count P r) (op x) idx.
Proof. by rewrite unlock => r P x; elim: r => //= i r ->; case: (P i). Qed.

End SeqExtension.

(* The following lemma can be used to localise extensionality to     *)
(* the specific index sequence. This is done by ssreflect rewriting, *)
(* before applying congruence or induction lemmas. This is important *)
(* for the latter, because ssreflect 1.1 still relies on primitive   *)
(* Coq matching unification for second-order application (e.g., for  *)
(* elim), and the latter can't handle the eqType constraint on I, as *)
(* it doesn't recognize canonical projections.                       *)
Lemma big_cond_seq : forall (I : eqType) r (P : pred I) F,
  \big[op/idx]_(i <- r | P i) F i
    = \big[op/idx]_(i <- r | P i && (i \in r)) F i.
Proof.
move=> I r P F; rewrite -!(big_filter r); congr bigop.
by apply: eq_in_filter => i ->; rewrite andbT.
Qed.

Lemma congr_big_nat : forall m1 n1 m2 n2 P1 P2 F1 F2,
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i = F2 i) ->
  \big[op/idx]_(m1 <= i < n1 | P1 i) F1 i
    = \big[op/idx]_(m2 <= i < n2 | P2 i) F2 i.
Proof.
move=> m n _ _ P1 P2 F1 F2 <- <- eqP12 eqF12.
rewrite big_cond_seq (big_cond_seq _ P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iota; last exact: eqF12.
case inmn_i: (m <= i < n); rewrite ?(andbT, andbF) //; exact: eqP12.
Qed.

Lemma big_geq : forall m n (P : pred nat) F, m >= n ->
  \big[op/idx]_(m <= i < n | P i) F i = idx.
Proof.
by move=> m n P F ge_m_n; rewrite /index_iota (eqnP ge_m_n) big_nil.
Qed.

Lemma big_ltn_cond : forall m n (P : pred nat) F, m < n ->
  let x := \big[op/idx]_(m.+1 <= i < n | P i) F i in
  \big[op/idx]_(m <= i < n | P i) F i = if P m then op (F m) x else x.
Proof.
by move=> m [//|n] P F le_m_n; rewrite /index_iota leq_subS // big_cons.
Qed.

Lemma big_ltn : forall m n F, m < n ->
  \big[op/idx]_(m <= i < n) F i = op (F m) (\big[op/idx]_(m.+1 <= i < n) F i).
Proof. move=> *; exact: big_ltn_cond. Qed.

Lemma big_addn : forall m n a (P : pred nat) F,
  \big[op/idx]_(m + a <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
move=> m n a P F; rewrite /index_iota subn_sub addnC iota_addl big_map.
by apply: eq_big => ? *; rewrite addnC.
Qed.

Lemma big_add1 : forall m n (P : pred nat) F,
  \big[op/idx]_(m.+1 <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
move=> m n P F; rewrite -addn1 big_addn subn1.
by apply: eq_big => ? *; rewrite addn1.
Qed.

Lemma big_nat_recl : forall n F,
  \big[op/idx]_(0 <= i < n.+1) F i =
     op (F 0) (\big[op/idx]_(0 <= i < n) F i.+1).
Proof. by move=> n F; rewrite big_ltn // big_add1. Qed.

Lemma big_mkord : forall n (P : pred nat) F,
  \big[op/idx]_(0 <= i < n | P i) F i = \big[op/idx]_(i < n | P i) F i.
Proof.
move=> n P F; rewrite /index_iota subn0 -(big_map (@nat_of_ord n)).
by congr bigop; rewrite /index_enum unlock val_ord_enum.
Qed.

Lemma big_nat_widen : forall m n1 n2 (P : pred nat) F, n1 <= n2 ->
  \big[op/idx]_(m <= i < n1 | P i) F i
      = \big[op/idx]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> m n1 n2 P F len12; symmetry.
rewrite -big_filter filter_predI big_filter.
congr bigop; rewrite /index_iota; set d1 := n1 - m; set d2 := n2 - m.
rewrite -(@subnKC d1 d2) /=; last by rewrite leq_sub2r ?leq_addr.
have: ~~ has (fun i => i < n1) (iota (m + d1) (d2 - d1)).
  apply/hasPn=> i; rewrite mem_iota -leqNgt; case/andP=> le_mn1_i _.
  by apply: leq_trans le_mn1_i; rewrite -leq_sub_add.
rewrite iota_add filter_cat has_filter /=; case: filter => // _.
rewrite cats0; apply/all_filterP; apply/allP=> i.
rewrite mem_iota; case/andP=> le_m_i lt_i_md1.
apply: (leq_trans lt_i_md1); rewrite subnKC // ltnW //.
rewrite -subn_gt0 -(ltn_add2l m) addn0; exact: leq_trans lt_i_md1.
Qed.

Lemma big_ord_widen_cond : forall n1 n2 (P : pred nat) (F : nat -> R),
     n1 <= n2 ->
  \big[op/idx]_(i < n1 | P i) F i
      = \big[op/idx]_(i < n2 | P i && (i < n1)) F i.
Proof.
move=> n1 n2 P F len12.
by rewrite -big_mkord (big_nat_widen _ _ _ len12) big_mkord.
Qed.

Lemma big_ord_widen : forall n1 n2 (F : nat -> R),
 n1 <= n2 ->
  \big[op/idx]_(i < n1) F i = \big[op/idx]_(i < n2 | i < n1) F i.
Proof. move=> *; exact: (big_ord_widen_cond (predT)). Qed.

Lemma big_ord_widen_leq : forall n1 n2 (P : pred 'I_(n1.+1)) F,
 n1 < n2 ->
  \big[op/idx]_(i < n1.+1 | P i) F i
      = \big[op/idx]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> n1 n2 P F len12; pose g G i := G (inord i : 'I_(n1.+1)).
rewrite -(big_ord_widen_cond (g _ P) (g _ F) len12) {}/g.
by apply: eq_big => i *; rewrite inord_val.
Qed.

Lemma big_ord_narrow_cond : forall n1 n2 (P : pred 'I_n2) F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/idx]_(i < n2 | P i && (i < n1)) F i
    = \big[op/idx]_(i < n1 | P (w i)) F (w i).
Proof.
move=> [|n1] n2 P F ltn12 /=.
  by rewrite !big_pred0 // => [[//] | i]; rewrite andbF.
rewrite (big_ord_widen_leq _ _ ltn12); apply: eq_big => i.
  rewrite ltnS; case: leqP => [le_i_n1|_]; last by rewrite !andbF.
  by congr (P _ && _); apply: val_inj; rewrite /= inordK.
by case/andP=> _ le_i_n1; congr F; apply: val_inj; rewrite /= inordK.
Qed.

Lemma big_ord_narrow_cond_leq : forall n1 n2 (P : pred 'I_(n2.+1)) F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/idx]_(i < n2.+1 | P i && (i <= n1)) F i
  = \big[op/idx]_(i < n1.+1 | P (w i)) F (w i).
Proof. move=> n1 n2; exact: big_ord_narrow_cond n1.+1 n2.+1. Qed.

Lemma big_ord_narrow : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/idx]_(i < n2 | i < n1) F i = \big[op/idx]_(i < n1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond (predT)). Qed.

Lemma big_ord_narrow_leq : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/idx]_(i < n2.+1 | i <= n1) F i = \big[op/idx]_(i < n1.+1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond_leq (predT)). Qed.

Lemma big_ord0 : forall P F, \big[op/idx]_(i < 0 | P i) F i = idx.
Proof. by move=> P F; rewrite big_pred0 => [|[]]. Qed.

Lemma big_ord_recl : forall n F,
  \big[op/idx]_(i < n.+1) F i =
     op (F ord0) (\big[op/idx]_(i < n) F (@lift n.+1 ord0 i)).
Proof.
move=> n F; pose G i := F (inord i).
have eqFG: forall i, F i = G i by move=> i; rewrite /G inord_val.
rewrite (eq_bigr _ (fun i _ => eqFG i)) -(big_mkord _ (fun _ => _) G) eqFG.
rewrite big_ltn // big_add1 /= big_mkord; congr op.
by apply: eq_bigr => i _; rewrite eqFG.
Qed.

Lemma big_const : forall (I : finType) (A : pred I) x,
  \big[op/idx]_(i \in A) x = iter #|A| (op x) idx.
Proof. by move=> I A x; rewrite big_const_seq count_filter cardE. Qed.

Lemma big_const_nat : forall m n x,
  \big[op/idx]_(m <= i < n) x = iter (n - m) (op x) idx.
Proof. by move=> *; rewrite big_const_seq count_predT size_iota. Qed.

Lemma big_const_ord : forall n x,
  \big[op/idx]_(i < n) x = iter n (op x) idx.
Proof. by move=> *; rewrite big_const card_ord. Qed.

End Extensionality.

Section MonoidProperties.

Import Monoid.Theory.

Variable R : Type.

Variable idx : R.
Notation Local "1" := idx.

Section Plain.

Variable op : Monoid.law 1.

Notation Local "*%M" := op (at level 0).
Notation Local "x * y" := (op x y).

Lemma eq_big_idx_seq : forall idx' I r (P : pred I) F,
     right_id idx' *%M -> has P r ->
   \big[*%M/idx']_(i <- r | P i) F i =\big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> idx' I r P F op_idx'.
rewrite -!(big_filter _ _ r) has_count count_filter.
case/lastP: (filter P r) => {r}// r i _.
by rewrite -cats1 !(big_cat_nested, big_cons, big_nil) op_idx' mulm1.
Qed.

Lemma eq_big_idx  : forall idx' (I : finType) i0 (P : pred I) F,
     P i0 -> right_id idx' *%M ->
  \big[*%M/idx']_(i | P i) F i =\big[*%M/1]_(i | P i) F i.
Proof.
move=> idx' I i0 P F op_idx' Pi0; apply: eq_big_idx_seq => //.
by apply/hasP; exists i0; first rewrite /index_enum -enumT mem_enum.
Qed.

Lemma big1_eq : forall I r (P : pred I), \big[*%M/1]_(i <- r | P i) 1 = 1.
Proof.
move=> *; rewrite big_const_seq; elim: (count _ _) => //= n ->; exact: mul1m.
Qed.

Lemma big1 : forall (I : finType) (P : pred I) F,
  (forall i, P i -> F i = 1) -> \big[*%M/1]_(i | P i) F i = 1.
Proof. by move=> I P F eq_F_1; rewrite (eq_bigr _ _ _ eq_F_1) big1_eq. Qed.

Lemma big1_seq : forall (I : eqType) r (P : pred I) F,
  (forall i, P i && (i \in r) -> F i = 1)
  -> \big[*%M/1]_(i <- r | P i) F i = 1.
Proof.
by move=> I r P F eqF1; rewrite big_cond_seq (eq_bigr _ _ _ eqF1) big1_eq.
Qed.

Lemma big_seq1 : forall I (i : I) F, \big[*%M/1]_(j <- [:: i]) F j = F i.
Proof. by rewrite unlock => /= *; rewrite mulm1. Qed.

Lemma big_mkcond : forall I r (P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i =
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof.
by rewrite unlock => I r P F; elim: r => //= i r ->; case P; rewrite ?mul1m.
Qed.

Lemma big_cat : forall I r1 r2 (P : pred I) F,
  \big[*%M/1]_(i <- r1 ++ r2 | P i) F i =
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; rewrite !(big_mkcond _ P).
elim: r1 => [|i r1 IHr1]; first by rewrite big_nil mul1m.
by rewrite /= !big_cons IHr1 mulmA.
Qed.

Lemma big_pred1_eq : forall (I : finType) (i : I) F,
  \big[*%M/1]_(j | j == i) F j = F i.
Proof.
by move=> I i F; rewrite -big_filter filter_index_enum enum1 big_seq1.
Qed.

Lemma big_pred1 : forall (I : finType) i (P : pred I) F,
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j = F i.
Proof. move=> I i P F; move/(eq_bigl _ _)->; exact: big_pred1_eq. Qed.

Lemma big_cat_nat : forall n m p (P : pred nat) F, m <= n -> n <= p ->
  \big[*%M/1]_(m <= i < p | P i) F i =
   (\big[*%M/1]_(m <= i < n | P i) F i) * (\big[*%M/1]_(n <= i < p | P i) F i).
Proof.
move=> n m p F P le_mn le_np; rewrite -big_cat.
by rewrite -{2}(subnKC le_mn) -iota_add -subn_sub subnKC // leq_sub2.
Qed.

Lemma big_nat1 : forall n F, \big[*%M/1]_(n <= i < n.+1) F i = F n.
Proof. by move=> n F; rewrite big_ltn // big_geq // mulm1. Qed.

Lemma big_nat_recr : forall n F,
  \big[*%M/1]_(0 <= i < n.+1) F i = (\big[*%M/1]_(0 <= i < n) F i) * F n.
Proof. by move=> n F; rewrite (@big_cat_nat n) ?leqnSn // big_nat1. Qed.

Lemma big_ord_recr : forall n F,
  \big[*%M/1]_(i < n.+1) F i =
     (\big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i)) * F ord_max.
Proof.
move=> n F; transitivity (\big[*%M/1]_(0 <= i < n.+1) F (inord i)).
  by rewrite big_mkord; apply: eq_bigr=> i _; rewrite inord_val.
rewrite big_nat_recr big_mkord; congr (_ * F _); last first.
  by apply: val_inj; rewrite /= inordK.
by apply: eq_bigr => [] i _; congr F; apply: ord_inj; rewrite inordK //= leqW.
Qed.

Lemma big_sumType : forall (I1 I2 : finType) (P : pred (I1 + I2)) F,
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (inl _ i)) F (inl _ i))
      * (\big[*%M/1]_(i | P (inr _ i)) F (inr _ i)).
Proof.
move=> I1 I2 P F.
by rewrite /index_enum [@Finite.enum _]unlock /= big_cat !big_map.
Qed.

Lemma big_split_ord : forall m n (P : pred 'I_(m + n)) F,
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (lshift n i)) F (lshift n i))
      * (\big[*%M/1]_(i | P (rshift m i)) F (rshift m i)).
Proof.
move=> m n P F.
rewrite -(big_map _ _ (lshift n) _ P F) -(big_map _ _ (@rshift m _) _ P F).
rewrite -big_cat; congr bigop; apply: (inj_map val_inj).
rewrite /index_enum -!enumT val_enum_ord map_cat -map_comp val_enum_ord.
rewrite -map_comp (map_comp (addn m)) val_enum_ord.
by rewrite -iota_addl addn0 iota_add.
Qed.

End Plain.

Section Abelian.

Variable op : Monoid.com_law 1.

Notation Local "'*%M'" := op (at level 0).
Notation Local "x * y" := (op x y).

Lemma eq_big_perm : forall (I : eqType) r1 r2 (P : pred I) F,
    perm_eq r1 r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; move/perm_eqP; rewrite !(big_mkcond _ _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *; rewrite big_cat /= !big_cons.
rewrite mulmCA; congr (_ * _); rewrite -big_cat; apply: IHr1 => a.
move/(_ a): eq_r12; rewrite !count_cat /= addnCA; exact: addnI.
Qed.

Lemma big_uniq : forall (I : finType) (r : seq I) F,
  uniq r -> \big[*%M/1]_(i <- r) F i = \big[*%M/1]_(i | i \in r) F i.
Proof.
move=> I r F uniq_r; rewrite -(big_filter _ _ _ (mem r)); apply: eq_big_perm.
by rewrite filter_index_enum uniq_perm_eq ?enum_uniq // => i; rewrite mem_enum.
Qed.

Lemma big_split : forall I r (P : pred I) F1 F2,
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) =
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
rewrite unlock => I r P F1 F2.
elim: r => /= [|i r ->]; [by rewrite mulm1 | case: (P i) => //=].
rewrite !mulmA; congr (_ * _); exact: mulmAC.
Qed.

Lemma bigID : forall I r (a P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i
  = \big[*%M/1]_(i <- r | P i && a i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Proof.
move=> I r a P F; rewrite !(big_mkcond _ _ _ F) -big_split.
by apply: eq_bigr => i; case: (a i); rewrite !simpm.
Qed.
Implicit Arguments bigID [I r].

Lemma bigU : forall (I : finType) (A B : pred I) F,
  [disjoint A & B] ->
  \big[*%M/1]_(i \in [predU A & B]) F i =
    (\big[*%M/1]_(i \in A) F i) * (\big[*%M/1]_(i \in B) F i).
Proof.
move=> I A B F dAB; rewrite (bigID (mem A)).
congr (_ * _); apply: eq_bigl => i; first by rewrite orbK.
by have:= pred0P dAB i; rewrite andbC /= !inE; case: (i \in A).
Qed.

Lemma bigD1 : forall (I : finType) j (P : pred I) F,
  P j -> \big[*%M/1]_(i | P i) F i
    = F j * \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
move=> I j P F Pj; rewrite (bigID (pred1 j)); congr (_ * _).
by apply: big_pred1 => i; rewrite /= andbC; case: eqP => // ->.
Qed.
Implicit Arguments bigD1 [I P F].

Lemma cardD1x : forall (I : finType) (A : pred I) j,
  A j -> #|SimplPred A| = 1 + #|[pred i | A i && (i != j)]|.
Proof.
move=> I A j Aj; rewrite (cardD1 j) [j \in A]Aj; congr (_ + _).
by apply: eq_card => i; rewrite inE /= andbC.
Qed.
Implicit Arguments cardD1x [I A].

Lemma partition_big : forall (I J : finType) (P : pred I) p (Q : pred J) F,
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i =
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> I J P p Q F Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply: eq_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x j Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)); congr (_ * _); apply: eq_bigl => i.
  by case: eqP => [-> | _]; rewrite !(Qj, simpm).
by rewrite andbA.
Qed.

Implicit Arguments partition_big [I J P F].

Lemma reindex_onto : forall (I J : finType) (h : J -> I) h' (P : pred I) F,
   (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> I J h h' P F h'K.
elim: {P}_.+1 {-3}P h'K (ltnSn #|P|) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  by rewrite !big_pred0 // => j; rewrite P0.
rewrite ltnS (cardD1x i Pi); move/IHn {n IHn} => IH.
rewrite (bigD1 i Pi) (bigD1 (h' i)) h'K ?Pi ?eq_refl //=; congr (_ * _).
rewrite {}IH => [|j]; [apply: eq_bigl => j | by case/andP; auto].
rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK; congr (_ && ~~ _).
by apply/eqP/eqP=> [<-|->] //; rewrite h'K.
Qed.
Implicit Arguments reindex_onto [I J P F].

Lemma reindex : forall (I J : finType) (h : J -> I) (P : pred I) F,
  {on [pred i | P i], bijective h} ->
  \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
move=> I J h P F [h' hK h'K]; rewrite (reindex_onto h h' h'K).
by apply: eq_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Implicit Arguments reindex [I J P F].

Lemma reindex_inj : forall (I : finType) (h : I -> I) (P : pred I) F,
  injective h -> \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof. move=> I h P F injh; exact: reindex (onW_bij _ (injF_bij injh)). Qed.
Implicit Arguments reindex_inj [I h P F].

Lemma big_nat_rev : forall m n P F,
  \big[*%M/1]_(m <= i < n | P i) F i
     = \big[*%M/1]_(m <= i < n | P (m + n - i.+1)) F (m + n - i.+1).
Proof.
move=> m n P F; case: (ltnP m n) => ltmn; last by rewrite !big_geq.
rewrite -{3 4}(subnK (ltnW ltmn)) addnA.
do 2!rewrite (big_addn _ _ 0) big_mkord; rewrite (reindex_inj rev_ord_inj) /=.
by apply: eq_big => [i | i _]; rewrite /= -addSn subn_add2r addnC addn_subA.
Qed.

Lemma pair_big_dep : forall (I J : finType) (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Proof.
move=> I J P Q F.
rewrite (partition_big (fun p => p.1) P) => [|j]; last by case/andP.
apply: eq_bigr => i /= Pi; rewrite (reindex_onto (pair i) (fun p => p.2)).
   by apply: eq_bigl => j; rewrite !eqxx [P i]Pi !andbT.
by case=> i' j /=; case/andP=> _ /=; move/eqP->.
Qed.

Lemma pair_big : forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma pair_bigA : forall (I J : finType) (F : I -> J -> R),
  \big[*%M/1]_i \big[*%M/1]_j F i j = \big[*%M/1]_p F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma exchange_big_dep :
    forall (I J : finType) (P : pred I) (Q : I -> pred J) (xQ : pred J) F,
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(j | xQ j) \big[*%M/1]_(i | P i && Q i j) F i j.
Proof.
move=> I J P Q xQ F PQxQ; pose p u := (u.2, u.1).
rewrite !pair_big_dep (reindex_onto (p J I) (p I J)) => [|[//]].
apply: eq_big => [] [j i] //=; symmetry; rewrite eq_refl andbC.
case: (@andP (P i)) => //= [[]]; exact: PQxQ.
Qed.
Implicit Arguments exchange_big_dep [I J P Q F].

Lemma exchange_big :  forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i) F i j.
Proof.
move=> I J P Q F; rewrite (exchange_big_dep Q) //; apply: eq_bigr => i /= Qi.
by apply: eq_bigl => j; rewrite [Q i]Qi andbT.
Qed.

Lemma exchange_big_dep_nat :
  forall m1 n1 m2 n2 (P : pred nat) (Q : rel nat) (xQ : pred nat) F,
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q i j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | xQ j)
       \big[*%M/1]_(m1 <= i < n1 | P i && Q i j) F i j.
Proof.
move=> m1 n1 m2 n2 P Q xQ F PQxQ.
transitivity
  (\big[*%M/1]_(i < n1 - m1| P (i + m1))
    \big[*%M/1]_(j < n2 - m2 | Q (i + m1) (j + m2)) F (i + m1) (j + m2)).
- rewrite -{1}[m1]add0n big_addn big_mkord; apply: eq_bigr => i _.
  by rewrite -{1}[m2]add0n big_addn big_mkord.
rewrite (exchange_big_dep (fun j: 'I__ => xQ (j + m2))) => [|i j]; last first.
  by apply: PQxQ; rewrite leq_addl addnC -subn_gt0 -subn_sub subn_gt0 ltn_ord.
symmetry; rewrite -{1}[m2]add0n big_addn big_mkord; apply: eq_bigr => j _.
by rewrite -{1}[m1]add0n big_addn big_mkord.
Qed.
Implicit Arguments exchange_big_dep_nat [m1 n1 m2 n2 P Q F].

Lemma exchange_big_nat : forall m1 n1 m2 n2 (P Q : pred nat) F,
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | Q j) \big[*%M/1]_(m1 <= i < n1 | P i) F i j.
Proof.
move=> m1 n1 m2 n2 P Q F; rewrite (exchange_big_dep_nat Q) //.
by apply: eq_bigr => i /= Qi; apply: eq_bigl => j; rewrite [Q i]Qi andbT.
Qed.

End Abelian.

End MonoidProperties.

Implicit Arguments big_filter [R op idx I].
Implicit Arguments big_filter_cond [R op idx I].
Implicit Arguments congr_big [R op idx I r1 P1 F1].
Implicit Arguments eq_big [R op idx I r P1 F1].
Implicit Arguments eq_bigl [R op idx  I r P1].
Implicit Arguments eq_bigr [R op idx I r  P F1].
Implicit Arguments eq_big_idx [R op idx idx' I P F].
Implicit Arguments big_cond_seq [R op idx I r].
Implicit Arguments congr_big_nat [R op idx m1 n1 P1 F1].
Implicit Arguments big_map [R op idx I J r].
Implicit Arguments big_nth [R op idx I r].
Implicit Arguments big_catl [R op idx I r1 r2 P F].
Implicit Arguments big_catr [R op idx I r1 r2  P F].
Implicit Arguments big_geq [R op idx m n P F].
Implicit Arguments big_ltn_cond [R op idx m n P F].
Implicit Arguments big_ltn [R op idx m n F].
Implicit Arguments big_addn [R op idx].
Implicit Arguments big_mkord [R op idx n].
Implicit Arguments big_nat_widen [R op idx] .
Implicit Arguments big_ord_widen_cond [R op idx n1].
Implicit Arguments big_ord_widen [R op idx n1].
Implicit Arguments big_ord_widen_leq [R op idx n1].
Implicit Arguments big_ord_narrow_cond [R op idx n1 n2 P F].
Implicit Arguments big_ord_narrow_cond_leq [R op idx n1 n2 P F].
Implicit Arguments big_ord_narrow [R op idx n1 n2 F].
Implicit Arguments big_ord_narrow_leq [R op idx n1 n2 F].
Implicit Arguments big_mkcond [R op idx I r].
Implicit Arguments big1_eq [R op idx I].
Implicit Arguments big1_seq [R op idx I].
Implicit Arguments big1 [R op idx I].
Implicit Arguments big_pred1 [R op idx I P F].
Implicit Arguments eq_big_perm [R op idx I r1 P F].
Implicit Arguments big_uniq [R op idx I F].
Implicit Arguments bigID [R op idx I r].
Implicit Arguments bigU [R op idx I].
Implicit Arguments bigD1 [R op idx I P F].
Implicit Arguments partition_big [R op idx I J P F].
Implicit Arguments reindex_onto [R op idx I J P F].
Implicit Arguments reindex [R op idx I J P F].
Implicit Arguments reindex_inj [R op idx I h P F].
Implicit Arguments pair_big_dep [R op idx I J].
Implicit Arguments pair_big [R op idx I J].
Implicit Arguments exchange_big_dep [R op idx I J P Q F].
Implicit Arguments exchange_big_dep_nat [R op idx m1 n1 m2 n2 P Q F].
Implicit Arguments big_ord_recl [R op idx].
Implicit Arguments big_ord_recr [R op idx].
Implicit Arguments big_nat_recl [R op idx].
Implicit Arguments big_nat_recr [R op idx].

Section BigProp.

Variables (R : Type) (Pb : R -> Type).
Variables (idx : R) (op1 op2 : R -> R -> R).
Hypothesis (Pb_idx : Pb idx)
           (Pb_op1 : forall x y, Pb x -> Pb y -> Pb (op1 x y))
           (Pb_eq_op : forall x y, Pb x -> Pb y -> op1 x y = op2 x y).

Lemma big_prop : forall I r (P : pred I) F,
  (forall i, P i -> Pb (F i)) -> Pb (\big[op1/idx]_(i <- r | P i) F i).
Proof.
by rewrite unlock => I r P F PbF; elim: r => //= i *; case Pi: (P i); auto.
Qed.

(* Pb must be given explicitly for the lemma below, because Coq second-order *)
(* unification will not handle the eqType constraint on I.                   *)
Lemma big_prop_seq : forall (I : eqType) (r : seq I) (P : pred I) F,
  (forall i, P i && (i \in r) -> Pb (F i)) ->
   Pb (\big[op1/idx]_(i <- r | P i) F i).
Proof. move=> I r P F; rewrite big_cond_seq; exact: big_prop. Qed.

(* Change operation *)
Lemma eq_big_op :  forall I r (P : pred I) F,
   (forall i, P i -> Pb (F i)) ->
  \big[op1/idx]_(i <- r | P i) F i = \big[op2/idx]_(i <- r | P i) F i.
Proof.
have:= big_prop; rewrite unlock => Pb_big I r P F Pb_F.
by elim: r => //= i r <-; case Pi: (P i); auto.
Qed.

Lemma eq_big_op_seq :  forall (I : eqType) r (P : pred I) F,
    (forall i, P i && (i \in r) -> Pb (F i)) ->
  \big[op1/idx]_(i <- r | P i) F i = \big[op2/idx]_(i <- r | P i) F i.
Proof. move=> I r P F Pb_F; rewrite !(big_cond_seq P); exact: eq_big_op. Qed.

End BigProp.

(* The implicit arguments expect an explicit Pb *)
Implicit Arguments eq_big_op_seq [R idx op1 I r P F].
Implicit Arguments eq_big_op [R idx op1 I P F].

Section BigRel.

Variables (R1 R2 : Type) (Pr : R1 -> R2 -> Type).
Variables (idx1 : R1) (op1 : R1 -> R1 -> R1).
Variables (idx2 : R2) (op2 : R2 -> R2 -> R2).
Hypothesis Pr_idx : Pr idx1 idx2.
Hypothesis Pr_rel : forall x1 x2 y1 y2,
  Pr x1 x2 -> Pr y1 y2 -> Pr (op1 x1 y1) (op2 x2 y2).

(* Pr must be given explicitly *)
Lemma big_rel : forall I r (P : pred I) F1 F2,
  (forall i, (P i) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/idx1]_(i <- r | P i) F1 i) (\big[op2/idx2]_(i <- r | P i) F2 i).
Proof.
rewrite !unlock => I r P F1 F2 PrF.
elim: r => //= i *; case Pi: (P i); auto.
Qed.

Lemma big_rel_seq : forall (I : eqType) (r : seq I) (P : pred I) F1 F2,
    (forall i, P i && (i \in r) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/idx1]_(i <- r | P i) F1 i) (\big[op2/idx2]_(i <- r | P i) F2 i).
Proof. move=> I r P *; rewrite !(big_cond_seq P); exact: big_rel. Qed.

End BigRel.

Implicit Arguments big_rel_seq [R1 R2 idx1 op1 idx2 op2 I r P F1 F2].
Implicit Arguments big_rel [R1 R2 idx1 op1 idx2 op2 I P F1 F2].

Section Morphism.

Variables R1 R2 : Type.
Variables (idx1 : R1) (idx2 : R2).
Variables (op1 : R1 -> R1 -> R1) (op2 : R2 -> R2 -> R2).
Variable phi : R1 -> R2.
Hypothesis phiM : {morph phi : x y / op1 x y >-> op2 x y}.
Hypothesis phi_id : phi idx1 = idx2.

Lemma big_morph : forall I r (P : pred I) F,
  phi (\big[op1/idx1]_(i <- r | P i) F i) =
     \big[op2/idx2]_(i <- r | P i) phi (F i).
Proof. by rewrite !unlock => I r P F; elim: r => //= i r <-; case: (P i). Qed.

End Morphism.

(* Allows apply: (big_morph phi). *)
Implicit Arguments big_morph [R1 R2 idx1 idx2 op1 op2].

Section Distributivity.

Import Monoid.Theory.

Variable R : Type.
Variables zero one : R.
Notation Local "0" := zero.
Notation Local "1" := one.
Variable times : Monoid.mul_law 0.
Notation Local "*%M" := times (at level 0).
Notation Local "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Notation Local "+%M" := plus (at level 0).
Notation Local "x + y" := (plus x y).

Lemma big_distrl : forall I r a (P : pred I) F,
  \big[+%M/0]_(i <- r | P i) F i * a = \big[+%M/0]_(i <- r | P i) (F i * a).
Proof.
move=> I r a P F; apply: (big_morph ( *%M^~ a) _ (mul0m _ a)) => x y.
exact: mulm_addl.
Qed.

Lemma big_distrr : forall I r a (P : pred I) F,
  a * \big[+%M/0]_(i <- r | P i) F i = \big[+%M/0]_(i <- r | P i) (a * F i).
Proof.
move=> I r a P F; apply: (big_morph _ _ (mulm0 _ a)) => x y; exact: mulm_addr.
Qed.

Lemma big_distr_big_dep :
  forall (I J : finType) j0 (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j =
     \big[+%M/0]_(f | pfamily j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite -big_filter filter_index_enum; set r := enum P.
pose fIJ := {ffun I -> J}; pose Pf := pfamily j0 _ Q; symmetry.
transitivity (\big[+%M/0]_(f | Pf (mem r) f) \big[*%M/1]_(i <- r) F i (f i)).
  apply: eq_big=> f; last by rewrite -big_filter filter_index_enum.
  by apply: eq_forallb => i; rewrite /= mem_enum.
have: uniq r by exact: enum_uniq.
elim: {P}r => /= [_|i r IHr].
  rewrite (big_pred1 [ffun => j0]) ?big_nil //= => f.
  apply/familyP/eqP=> /= [Df |->{f} i]; last by rewrite ffunE.
  apply/ffunP=> i; rewrite ffunE; exact/eqP.
case/andP=> nri; rewrite big_cons big_distrl; move/IHr {IHr} <-.
rewrite (partition_big (fun f : fIJ => f i) (Q i)); last first.
  by move=> f; move/familyP; move/(_ i); rewrite /= inE /= eqxx.
pose seti j (f : fIJ) := [ffun k => if k == i then j else f k].
apply: eq_bigr => j Qij; rewrite (reindex_onto (seti j) (seti j0)); last first.
  move=> f /=; case/andP; move/familyP=> eq_f; move/eqP=> fi.
  by apply/ffunP => k; rewrite !ffunE; case: eqP => // ->.
rewrite big_distrr; apply: eq_big => [f | f eq_f]; last first.
  rewrite big_cons ffunE eq_refl !(big_cond_seq predT) /=; congr (_ * _).
  by apply: eq_bigr => k; rewrite ffunE; case: eqP => // ->; case/idPn.
rewrite !ffunE !eq_refl andbT; apply/andP/familyP=> [[Pjf fij0] k | Pff].
  have:= familyP _ _ Pjf k; rewrite /= ffunE in_cons; case: eqP => // -> _.
  by rewrite (negbTE nri) -(eqP fij0) !ffunE ?inE /= !eqxx.
split.
  apply/familyP=> k; move/(_ k): Pff; rewrite /= ffunE in_cons.
  by case: eqP => // ->.
apply/eqP; apply/ffunP=> k; have:= Pff k; rewrite !ffunE /=.
by case: eqP => // ->; rewrite (negbTE nri) /=; move/eqP.
Qed.

Lemma big_distr_big :
  forall (I J : finType) j0 (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j =
     \big[+%M/0]_(f | pffun_on j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite (big_distr_big_dep j0); apply: eq_bigl => f.
by apply/familyP/familyP=> Pf i; move/(_ i): Pf; case: (P i).
Qed.

Lemma bigA_distr_big_dep :
  forall (I J : finType) (Q : I -> pred J) F,
  \big[*%M/1]_i \big[+%M/0]_(j | Q i j) F i j
    = \big[+%M/0]_(f | family Q f) \big[*%M/1]_i F i (f i).
Proof.
move=> I J Q F; case: (pickP J) => [j0 _ | J0].
   exact: (big_distr_big_dep j0).
rewrite /index_enum -enumT; case: (enum I) (mem_enum I) => [I0 | i r _].
  have f0: I -> J by move=> i; have:= I0 i.
  rewrite (big_pred1 (finfun f0)) ?big_nil // => g.
  by apply/familyP/eqP=> _; first apply/ffunP; move=> i; have:= I0 i.
have Q0: Q _ =1 pred0 by move=> ? j; have:= J0 j.
rewrite big_cons /= big_pred0 // mul0m big_pred0 // => f.
by apply/familyP; move/(_ i); rewrite Q0.
Qed.

Lemma bigA_distr_big :
  forall (I J : finType) (Q : pred J) (F : I -> J -> R),
  \big[*%M/1]_i \big[+%M/0]_(j | Q j) F i j
    = \big[+%M/0]_(f | ffun_on Q f) \big[*%M/1]_i F i (f i).
Proof. move=> *; exact: bigA_distr_big_dep. Qed.

Lemma bigA_distr_bigA :
  forall (I J : finType) F,
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Proof.
move=> *; rewrite bigA_distr_big; apply: eq_bigl => ?; exact/familyP.
Qed.

End Distributivity.

Implicit Arguments big_distrl [R zero times plus I r].
Implicit Arguments big_distrr [R zero times plus I r].
Implicit Arguments big_distr_big_dep [R zero one times plus I J].
Implicit Arguments big_distr_big [R zero one times plus I J].
Implicit Arguments bigA_distr_big_dep [R zero one times plus I J].
Implicit Arguments bigA_distr_big [R zero one times plus I J].
Implicit Arguments bigA_distr_bigA [R zero one times plus I J].

Section BigBool.

Variables (I : finType) (P : pred I).

Lemma big_orE : forall B,
  \big[orb/false]_(i | P i) B i = (existsb i, P i && B i).
Proof.
move=> B; case: existsP => [[i] | no_i].
  by case/andP=> Pi Bi; rewrite (bigD1 i) // Bi.
by rewrite big1 // => i Pi; apply/idP=> Bi; case: no_i; exists i; rewrite Pi.
Qed.

Lemma big_andE : forall B,
  \big[andb/true]_(i | P i) B i = (forallb i, P i ==> B i).
Proof.
move=> B; apply: negb_inj.
rewrite (big_morph negb negb_and (erefl (~~ true))) big_orE negb_forall.
by apply: eq_existsb => i; case: (P i).
Qed.

End BigBool.

Section NatConst.

Variables (I : finType) (A : pred I).

Lemma sum_nat_const : forall n, \sum_(i \in A) n = #|A| * n.
Proof. by move=> n; rewrite big_const; elim: #|A| => //= i ->. Qed.

Lemma sum1_card : \sum_(i \in A) 1 = #|A|.
Proof. by rewrite sum_nat_const muln1. Qed.

Lemma prod_nat_const : forall n, \prod_(i \in A) n = n ^ #|A|.
Proof. by move=> n; rewrite big_const -Monoid.iteropE. Qed.

Lemma sum_nat_const_nat : forall n1 n2 n,
  \sum_(n1 <= i < n2) n = (n2 - n1) * n.
Proof. by move=> *; rewrite big_const_nat; elim: (_ - _) => //= ? ->. Qed.

Lemma prod_nat_const_nat : forall n1 n2 n,
  \prod_(n1 <= i < n2) n = n ^ (n2 - n1).
Proof. by move=> *; rewrite big_const_nat -Monoid.iteropE. Qed.

End NatConst.

Lemma leqif_sum : forall (I : finType) (P C : pred I) (E1 E2 : I -> nat),
  (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff (forallb i, P i ==> C i).
Proof.
move=> I P C E1 E2 leE12; rewrite -big_andE.
elim: (index_enum _) => [|i r IHr]; first by rewrite !big_nil.
rewrite !big_cons; case Pi: (P i) => //=.
by apply: leqif_add; first exact: leE12.
Qed.

Lemma sum_nat_eq0 : forall (I : finType) (P : pred I) (E : I -> nat),
  (\sum_(i | P i) E i == 0)%N = (forallb i, P i ==> (E i == 0))%N.
Proof.
by move=> I P E; rewrite eq_sym -(@leqif_sum I P _ (fun _ => 0%N) E) ?big1_eq.
Qed.

Lemma prodn_cond_gt0 : forall I r (P : pred I) F,
  (forall i, P i -> 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof.
by move=> I r P F Fpos; apply big_prop => // n1 n2; rewrite muln_gt0 => ->.
Qed.

Lemma prodn_gt0 : forall I r (P : pred I) F,
  (forall i, 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof. move=> I r P F Fpos; exact: prodn_cond_gt0. Qed.

Lemma leq_bigmax_cond : forall (I : finType) (P : pred I) F i0,
  P i0 -> F i0 <= \max_(i | P i) F i.
Proof.
by move=> I P F i0 Pi0; rewrite -eqn_maxr (bigD1 i0) // maxnA /= maxnn eqxx.
Qed.
Implicit Arguments leq_bigmax_cond [I P F].

Lemma leq_bigmax : forall (I : finType) F (i0 : I), F i0 <= \max_i F i.
Proof. by move=> *; exact: leq_bigmax_cond. Qed.
Implicit Arguments leq_bigmax [I F].

Lemma bigmax_leqP : forall (I : finType) (P : pred I) m F,
  reflect (forall i, P i -> F i <= m) (\max_(i | P i) F i <= m).
Proof.
move=> I P m F; apply: (iffP idP) => leFm => [i Pi|].
  by apply: leq_trans leFm; exact: leq_bigmax_cond.
by apply big_prop => // m1 m2; rewrite leq_maxl => ->.
Qed.

Lemma bigmax_sup : forall (I : finType) i0 (P : pred I) m F,
  P i0 -> m <= F i0 -> m <= \max_(i | P i) F i.
Proof.
by move=> I i0 P m F Pi0 le_m_Fi0; exact: leq_trans (leq_bigmax_cond i0 Pi0).
Qed.
Implicit Arguments bigmax_sup [I P m F].

Lemma bigmax_eq_arg : forall (I : finType) i0 (P : pred I) F,
  P i0 -> \max_(i | P i) F i = F [arg max_(i > i0 | P i) F i].
Proof.
move=> I i0 P F Pi0; case: arg_maxP => //= i Pi maxFi.
by apply/eqP; rewrite eqn_leq leq_bigmax_cond // andbT; exact/bigmax_leqP.
Qed.
Implicit Arguments bigmax_eq_arg [I P F].

Lemma eq_bigmax_cond : forall (I : finType) (A : pred I) F,
  #|A| > 0 -> {i0 | i0 \in A & \max_(i \in A) F i = F i0}.
Proof.
move=> I A F; case: (pickP A) => [i0 Ai0 _ | ]; last by move/eq_card0->.
by exists [arg max_(i > i0 \in A) F i]; [case: arg_maxP | exact: bigmax_eq_arg].
Qed.

Lemma eq_bigmax : forall (I : finType) F,
  #|I| > 0 -> {i0 : I | \max_i F i = F i0}.
Proof. by move=> I F; case/(eq_bigmax_cond F) => x _ ->; exists x. Qed.

Lemma expn_sum : forall m I r (P : pred I) F,
  (m ^ (\sum_(i <- r | P i) F i) = \prod_(i <- r | P i) m ^ F i)%N.
Proof. move=> m; exact: big_morph (expn_add m) _. Qed.

Lemma dvdn_biglcmP : forall (I : finType) (P : pred I) F m,
  reflect (forall i, P i -> F i %| m) (\big[lcmn/1%N]_(i | P i) F i %| m).
Proof.
move=> I P F m; apply: (iffP idP) => [dvFm i Pi | dvFm].
  by rewrite (bigD1 i) // dvdn_lcm in dvFm; case/andP: dvFm.
by apply big_prop => // [p q p_m]; rewrite dvdn_lcm p_m.
Qed. 

Lemma biglcmn_sup : forall (I : finType) i0 (P : pred I) F m,
  P i0 -> m %| F i0 -> m %| \big[lcmn/1%N]_(i | P i) F i.
Proof.
move=> I i0 P F m Pi0 m_Fi0.
by rewrite (dvdn_trans m_Fi0) // (bigD1 i0) ?dvdn_lcml.
Qed.
Implicit Arguments biglcmn_sup [I P F m].

Lemma dvdn_biggcdP : forall (I : finType) (P : pred I) F m,
  reflect (forall i, P i -> m %| F i) (m %| \big[gcdn/0]_(i | P i) F i).
Proof.
move=> I P F m; apply: (iffP idP) => [dvmF i Pi | dvmF].
  by rewrite (bigD1 i) // dvdn_gcd in dvmF; case/andP: dvmF.
by apply big_prop => // [p q m_p]; rewrite dvdn_gcd m_p.
Qed. 

Lemma biggcdn_inf : forall (I : finType) i0 (P : pred I) F m,
  P i0 -> F i0 %| m -> \big[gcdn/0]_(i | P i) F i %| m.
Proof.
by move=> I i0 P F m Pi0; apply: dvdn_trans; rewrite (bigD1 i0) ?dvdn_gcdl.
Qed.
Implicit Arguments biggcdn_inf [I P F m].

Unset Implicit Arguments.

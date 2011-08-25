(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix.

(*****************************************************************************)
(* In this file we develop the rank and row space theory of matrices, based  *)
(* on an extended gaussian elimination procedure similar to LUP              *)
(* decomposition. This provides us with a concrete but generic model of      *)
(* finite dimensional vector spaces and F-algebras, in which vectors, linear *)
(* functions, families, bases, subspaces, ideals and subrings are all        *)
(* represented using matrices. This model can be used as a foundation for    *)
(* the usual theory of abstract linear algebra, but it can also be used to   *)
(* develop directly substantial theories, such as the theory of finite group *)
(* linear representation.                                                    *)
(*   Here we define the following concepts and notations:                    *)
(* gaussian_elimination A == a permuted triangular decomposition (L, U, r)   *)
(*                   of A, with L a column permutation of a lower triangular *)
(*                   invertible matrix, U a row permutation of an upper      *)
(*                   triangular invertible matrix, and r the rank of A, all  *)
(*                   satisfying the identity L *m pid_mx r *m U = A.         *)
(*        \rank A == the rank of A.                                          *)
(*    row_free A <=> the rows of A are linearly free (i.e., the rank and     *)
(*                   height of A are equal).                                 *)
(*    row_full A <=> the row-space of A spans all row-vectors (i.e., the     *)
(*                   rank and width of A are equal).                         *)
(*    col_ebase A == the extended column basis of A (the first matrix L      *)
(*                   returned by gaussian_elimination A).                    *)
(*    row_ebase A == the extended row base of A (the second matrix U         *)
(*                   returned by gaussian_elimination A).                    *)
(*     col_base A == a basis for the columns of A: a row-full matrix         *)
(*                   consisting of the first \rank A columns of col_ebase A. *)
(*     row_base A == a basis for the rows of A: a row-free matrix consisting *)
(*                   of the first \rank A rows of row_ebase A.               *)
(*       pinvmx A == a partial inverse for A in its row space (or on its     *)
(*                   column space, equivalently). In particular, if u is a   *)
(*                   row vector in the row_space of A, then u *m pinvmx A is *)
(*                   the row vector of the coefficients of a decomposition   *)
(*                   of u as a sub of rows of A.                             *)
(*        kermx A == the row kernel of A : a square matrix whose row space   *)
(*                   consists of all u such that u *m A = 0 (it consists of  *)
(*                   the inverse of col_ebase A, with the top \rank A rows   *)
(*                   zeroed out). Also, kermx A is a partial right inverse   *)
(*                   to col_ebase A, in the row space anihilated by A.       *)
(*      cokermx A == the cokernel of A : a square matrix whose column space  *)
(*                   consists of all v such that A *m v = 0 (it consists of  *)
(*                   the inverse of row_ebase A, with the leftmost \rank A   *)
(*                   columns zeroed out).                                    *)
(* eigenvalue g a <=> a is an eigenvalue of the square matrix g.             *)
(* eigenspace g a == a square matrix whose row space is the eigenspace of    *)
(*                   the eigenvalue a of g (or 0 if a is not an eigenvalue). *)
(* We use a different scope %MS for matrix row-space set-like operations; to *)
(* avoid confusion, this scope should not be opened globally. Note that the  *)
(* the arguments of \rank _ and the operations below have default scope %MS. *)
(*    (A <= B)%MS <=> the row-space of A is included in the row-space of B.  *)
(*                   We test for this by testing if cokermx B anihilates A.  *)
(*     (A < B)%MS <=> the row-space of A is properly included in the         *)
(*                   row-space of B.                                         *)
(*  (A <= B <= C)%MS == (A <= B)%MS && (B <= C)%MS, and similarly for        *)
(*                   (A < B <= C)%MS, (A < B <= C)%MS and (A < B < C)%MS.    *)
(*    (A == B)%MS == (A <= B <= A)%MS (A and B have the same row-space).     *)
(*   (A :=: B)%MS == A and B behave identically wrt. \rank and <=. This      *)
(*                   triple rewrite rule is the Prop version of (A == B)%MS. *)
(*                   Note that :=: cannot be treated as a setoid-style       *)
(*                   Equivalence because its arguments can have different    *)
(*                   types: A and B need not have the same number of rows,   *)
(*                   and often don't (e.g., in row_base A :=: A).            *)
(*       <<A>>%MS == a square matrix with the same row-space as A; <<A>>%MS  *)
(*                   is a canonical representation of the subspace generated *)
(*                   by A, viewed as a list of row-vectors: if (A == B)%MS,  *)
(*                   then <<A>>%MS = <<B>>%MS.                               *)
(*     (A + B)%MS == a square matrix whose row-space is the sum of the       *)
(*                   row-spaces of A and B; thus (A + B == col_mx A B)%MS.   *)
(*  (\sum_i <expr i>)%MS == the "big" version of (_ + _)%MS; as the latter   *)
(*                   has a canonical abelian monoid structure, most generic  *)
(*                   bigop lemmas apply (the other bigop indexing notations  *)
(*                   are also defined).                                      *)
(*   (A :&: B)%MS == a square matrix whose row-space is the intersection of  *)
(*                   the row-spaces of A and B.                              *)
(*  (\bigcap_i <expr i>)%MS == the "big" version of (_ :&: _)%MS, which also *)
(*                   has a canonical abelian monoid structure.               *)
(*         A^C%MS == a square matrix whose row-space is a complement to the  *)
(*                   the row-space of A (it consists of row_ebase A with the *)
(*                   top \rank A rows zeroed out).                           *)
(*   (A :\: B)%MS == a square matrix whose row-space is a complement of the  *)
(*                   the row-space of (A :&: B)%MS in the row-space of A.    *)
(*                   We have (A :\: B == A :&: (capmx_gen A B)^C)%MS, with   *)
(*                   capmx_gen A B a recatangular matrix that generates      *)
(*                   (A :&: B)%MS, i.e., (capmx_gen A B == A :&: B)%MS.      *)
(*    proj_mx A B == a square matrix that projects (A + B)%MS onto A         *)
(*                   parellel to B, when (A :&: B)%MS = 0 (A and B must also *)
(*                   be square).                                             *)
(*     mxdirect S == the sum expression S is a direct sum. This is a NON     *)
(*                   EXTENSIONAL notation: the exact boolean expression is   *)
(*                   inferred from the syntactic form of S (expanding        *)
(*                   definitions, however); both (\sum_(i | _) _)%MS and     *)
(*                   (_ + _)%MS sums are recognized. This construct uses a   *)
(*                   variant of the reflexive ("quote") canonical structure, *)
(*                   mxsum_expr. The structure also recognizes sums of       *)
(*                   matrix ranks, so that lemmas concerning the rank of     *)
(*                   direct sums can be used bidirectionally.                *)
(* The next set of definitions let us represent F-algebras using matrices:   *)
(*   'A[F]_(m, n) == the type of matrices encoding (sub)algebras of square   *)
(*                   n x n matrices, via mxvec; as in the matrix type        *)
(*                   notation, m and F can be omitted (m defaults to n ^ 2). *)
(*                := 'M[F]_(m, n ^ 2).                                       *)
(*   (A \in R)%MS <=> the square matrix A belongs to the linear set of       *)
(*                    matrices (most often, a sub-algebra) encoded by the    *)
(*                    row space of R. This is simply notation, so all the    *)
(*                    lemmas and rewrite rules for (_ <= _)%MS can apply.    *)
(*                := (mxvec A <= R)%MS.                                      *)
(*     (R * S)%MS == a square n^2 x n^2 matrix whose row-space encodes the   *)
(*                   linear set of n x n matrices generated by the pointwise *)
(*                   product of the sets of matrices encoded by R and S.     *)
(*       'C(R)%MS == a square matric encoding the centraliser of the set of  *)
(*                   square matrices encoded by R.                           *)
(*     'C_S(R)%MS := (S :&: 'C(R))%MS (the centraliser of R in S).           *)
(*       'Z(R)%MS == the center of R (i.e., 'C_R(R)%MS).                     *)
(*  left_mx_ideal R S <=> S is a left ideal for R (R * S <= S)%MS.           *)
(* right_mx_ideal R S <=> S is a right ideal for R (S * R <= S)%MS.          *)
(*       mx_ideal R S <=> S is a bilateral ideal for R.                      *)
(*      mxring_id R e <-> e is an identity element for R (Prop predicate).   *)
(*    has_mxring_id R <=> R has a nonzero identity element (bool predicate). *)
(*           mxring R <=> R encodes a nontrivial subring.                    *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").
Reserved Notation "A :+: B" (at level 50, left associativity).
Reserved Notation "A ^C"    (at level 8, format "A ^C").

Notation "''A_' ( m , n )" := 'M_(m, n ^ 2)
  (at level 8, format "''A_' ( m ,  n )") : type_scope.

Notation "''A_' ( n )" := 'A_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "''A_' n" := 'A_(n)
  (at level 8, n at next level, format "''A_' n") : type_scope.

Notation "''A' [ F ]_ ( m , n )" := 'M[F]_(m, n ^ 2)
  (at level 8, only parsing) : type_scope.

Notation "''A' [ F ]_ ( n )" := 'A[F]_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "''A' [ F ]_ n" := 'A[F]_(n)
  (at level 8, n at level 2, only parsing) : type_scope.

Delimit Scope matrix_set_scope with MS.

Notation Local simp := (Monoid.Theory.simpm, oppr0).

(*****************************************************************************)
(******************** Rank and row-space theory ******************************)
(*****************************************************************************)

Section RowSpaceTheory.

Variable F : fieldType.

Local Notation "''M_' ( m , n )" := 'M[F]_(m, n) : type_scope.
Local Notation "''M_' n" := 'M[F]_(n, n) : type_scope.

(* Decomposition with double pivoting; computes the rank, row and column  *)
(* images, kernels, and complements of a matrix.                          *)

Fixpoint gaussian_elimination {m n} : 'M_(m, n) -> 'M_m * 'M_n * nat :=
  match m, n return 'M_(m, n) -> 'M_m * 'M_n * nat with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if [pick ij | A ij.1 ij.2 != 0] is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := gaussian_elimination (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Section Defs.

Variables (m n : nat) (A : 'M_(m, n)).

Let LUr := locked (@gaussian_elimination) m n A.

Definition col_ebase := LUr.1.1.
Definition row_ebase := LUr.1.2.
Definition mxrank := if [|| m == 0 | n == 0]%N then 0%N else LUr.2.

Definition row_free := mxrank == m.
Definition row_full := mxrank == n.

Definition row_base : 'M_(mxrank, n) := pid_mx mxrank *m row_ebase.
Definition col_base : 'M_(m, mxrank) := col_ebase *m pid_mx mxrank.

Definition complmx : 'M_n := copid_mx mxrank *m row_ebase.
Definition kermx : 'M_m := copid_mx mxrank *m invmx col_ebase.
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

Definition pinvmx : 'M_(n, m) :=
  invmx row_ebase *m pid_mx mxrank *m invmx col_ebase.

End Defs.

Arguments Scope mxrank [nat_scope nat_scope matrix_set_scope].
Local Notation "\rank A" := (mxrank A) : nat_scope.
Arguments Scope complmx [nat_scope nat_scope matrix_set_scope].
Local Notation "A ^C" := (complmx A) : matrix_set_scope.

Let mxopE : forall k opty (op : forall m : nat, opty m) m1,
  (let f := let: tt := k in fun m => op m in f) m1 = op m1.
Proof. by case. Qed.

Definition submx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  A *m cokermx B == 0.
Fact submx_key : unit. Proof. by []. Qed.
Definition submx := let: tt := submx_key in submx_def.
Arguments Scope submx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits submx.
Local Notation "A <= B" := (submx A B) : matrix_set_scope.
Local Notation "A <= B <= C" := ((A <= B) && (B <= C))%MS : matrix_set_scope.
Local Notation "A == B" := (A <= B <= A)%MS : matrix_set_scope.

Definition ltmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  (A <= B)%MS && ~~ (B <= A)%MS.
Arguments Scope ltmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits ltmx.
Local Notation "A < B" := (ltmx A B) : matrix_set_scope.

Definition eqmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  prod (\rank A = \rank B)
       (forall m3 (C : 'M_(m3, n)),
            ((A <= C) = (B <= C)) * ((C <= A) = (C <= B)))%MS.
Arguments Scope eqmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Local Notation "A :=: B" := (eqmx A B) : matrix_set_scope.

Section LtmxIdentities.

Variables (m1 m2 n : nat) (A : 'M_(m1, n)) (B : 'M_(m2, n)).

Lemma ltmxE : (A < B)%MS = ((A <= B)%MS && ~~ (B <= A)%MS). Proof. by []. Qed.

Lemma ltmxW : (A < B)%MS -> (A <= B)%MS. Proof. by case/andP. Qed.

Lemma ltmxEneq : (A < B)%MS = (A <= B)%MS && ~~ (A == B)%MS.
Proof. by apply: andb_id2l => ->. Qed.

Lemma submxElt : (A <= B)%MS = (A == B)%MS || (A < B)%MS.
Proof. by rewrite -andb_orr orbN andbT. Qed.

End LtmxIdentities.

(* The definition of the row-space operator is rigged to return the identity  *)
(* matrix for full matrices. To allow for further tweaks that will make the   *)
(* row-space intersection operator strictly commutative and monoidal, we      *)
(* slightly generalize some auxiliary definitions: we parametrize the         *)
(* "equivalent subspace and identity" choice predicate equivmx by a boolean   *)
(* determining whether the matrix should be the identity (so for genmx A its  *)
(* value is row_full A), and introduce a "quasi-identity" predicate qidmx     *)
(* that selects non-square full matrices along with the identity matrix 1%:M  *)
(* (this does not affect genmx, which chooses a square matrix).               *)
(*   The choice witness for genmx A is either 1%:M for a row-full A, or else  *)
(* row_base A padded with null rows.                                          *)
Let qidmx m n (A : 'M_(m, n)) :=
  if m == n then A == pid_mx n else row_full A.
Let equivmx m n (A : 'M_(m, n)) idA (B : 'M_n) :=
  (B == A)%MS && (qidmx B == idA).
Let equivmx_spec m n (A : 'M_(m, n)) idA (B : 'M_n) :=
  prod (B :=: A)%MS (qidmx B = idA).
Definition genmx_witness m n (A : 'M_(m, n)) : 'M_n :=
  if row_full A then 1%:M else pid_mx (\rank A) *m row_ebase A.
Definition genmx_def m n (A : 'M_(m, n)) : 'M_n :=
  choose (equivmx A (row_full A)) (genmx_witness A).
Fact genmx_key : unit. Proof. by []. Qed.
Definition genmx := let: tt := genmx_key in genmx_def.
Local Notation "<< A >>" := (genmx A) : matrix_set_scope.

(* The setwise sum is tweaked so that 0 is a strict identity element for      *)
(* square matrices, because this lets us use the bigop component. As a result *)
(* setwise sum is not quite strictly extensional.                             *)
Let addsmx_nop m n (A : 'M_(m, n)) := conform_mx <<A>>%MS A.
Definition addsmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : 'M_n :=
  if A == 0 then addsmx_nop B else if B == 0 then addsmx_nop A else
  <<col_mx A B>>%MS.
Fact addsmx_key : unit. Proof. by []. Qed.
Definition addsmx := let: tt := addsmx_key in addsmx_def.
Arguments Scope addsmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits addsmx.
Local Notation "A + B" := (addsmx A B) : matrix_set_scope.
Local Notation "\sum_ ( i | P ) B" := (\big[addsmx/0]_(i | P) B%MS)
  : matrix_set_scope.

(* The set intersection is similarly biased so that the identity matrix is a  *)
(* strict identity. This is somewhat more delicate than for the sum, because  *)
(* the test for the identity is non-extensional. This forces us to actually   *)
(* bias the choice operator so that it does not accidentally map an           *)
(* intersection of non-identity matrices to 1%:M; this would spoil            *)
(* associativity: if B :&: C = 1%:M but B and C are not identity, then for a  *)
(* square matrix A we have A :&: (B :&: C) = A != (A :&: B) :&: C in general. *)
(* To complicate matters there may not be a square non-singular matrix        *)
(* different than 1%:M, since we could be dealing with 'M['F_2]_1. We         *)
(* sidestep the issue by making all non-square row-full matrices identities,  *)
(* and choosing a normal representative that preserves the qidmx property.    *)
(* Thus A :&: B = 1%:M iff A and B are both identities, and this suffices for *)
(* showing that associativity is strict.                                      *)
Let capmx_witness m n (A : 'M_(m, n)) :=
  if row_full A then conform_mx 1%:M A else <<A>>%MS.
Let capmx_norm m n (A : 'M_(m, n)) :=
  choose (equivmx A (qidmx A)) (capmx_witness A).
Let capmx_nop m n (A : 'M_(m, n)) := conform_mx (capmx_norm A) A.
Definition capmx_gen m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  lsubmx (kermx (col_mx A B)) *m A.
Definition capmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : 'M_n :=
  if qidmx A then capmx_nop B else
  if qidmx B then capmx_nop A else
  if row_full B then capmx_norm A else capmx_norm (capmx_gen A B).
Fact capmx_key : unit. Proof. by []. Qed.
Definition capmx := let: tt := capmx_key in capmx_def.
Arguments Scope capmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits capmx.
Local Notation "A :&: B" := (capmx A B) : matrix_set_scope.
Local Notation "\bigcap_ ( i | P ) B" := (\big[capmx/1%:M]_(i | P) B)
  : matrix_set_scope.

Definition diffmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : 'M_n :=
  <<capmx_gen A (capmx_gen A B)^C>>%MS.
Fact diffmx_key : unit. Proof. by []. Qed.
Definition diffmx := let: tt := diffmx_key in diffmx_def.
Arguments Scope diffmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits diffmx.
Local Notation "A :\: B" := (diffmx A B) : matrix_set_scope.

Definition proj_mx n (U V : 'M_n) : 'M_n := pinvmx (col_mx U V) *m col_mx U 0.

Local Notation gaussE := gaussian_elimination.

Fact mxrankE : forall m n (A : 'M_(m, n)), \rank A = (gaussE A).2.
Proof. by unlock mxrank => [[|m] [|n]]. Qed.

Lemma rank_leq_row : forall m n (A : 'M_(m, n)), \rank A <= m.
Proof.
move=> m n A; rewrite mxrankE.
elim: m n A => [|m IHm] [|n] //= A; case: pickP => [[i j] _|] //=.
by move: (_ - _) => B; case: gaussE (IHm _ B) => [[L U] r] /=.
Qed.

Lemma row_leq_rank : forall m n (A : 'M_(m, n)), (m <= \rank A) = row_free A.
Proof. by move=> m n A; rewrite /row_free eqn_leq rank_leq_row. Qed.

Lemma rank_leq_col : forall m n (A : 'M_(m, n)), \rank A <= n.
Proof.
move=> m n A; rewrite mxrankE.
elim: m n A => [|m IHm] [|n] //= A; case: pickP => [[i j] _|] //=.
by move: (_ - _) => B; case: gaussE (IHm _ B) => [[L U] r] /=.
Qed.

Lemma col_leq_rank : forall m n (A : 'M_(m, n)), (n <= \rank A) = row_full A.
Proof. by move=> m n A; rewrite /row_full eqn_leq rank_leq_col. Qed.

Let unitmx1F := @unitmx1 F.
Lemma row_ebase_unit : forall m n (A : 'M_(m, n)), row_ebase A \in unitmx.
Proof.
unlock row_ebase; elim=> [|m IHm] [|n] //= A.
case: pickP => [[i j] /= nzAij | //=]; move: (_ - _) => B.
case: gaussE (IHm _ B) => [[L U] r] /= uU.
rewrite unitmxE xcolE det_mulmx (@det_ublock _ 1) det_scalar1 !unitr_mul.
by rewrite unitfE nzAij -!unitmxE uU unitmx_perm.
Qed.

Lemma col_ebase_unit : forall m n (A : 'M_(m, n)), col_ebase A \in unitmx.
Proof.
unlock col_ebase; elim=> [|m IHm] [|n] //= A; case: pickP => [[i j] _|] //=.
move: (_ - _) => B; case: gaussE (IHm _ B) => [[L U] r] /= uL.
rewrite unitmxE xrowE det_mulmx (@det_lblock _ 1) det1 mul1r unitr_mul.
by rewrite -unitmxE unitmx_perm.
Qed.
Hint Resolve rank_leq_row rank_leq_col row_ebase_unit col_ebase_unit.

Lemma mulmx_ebase : forall m n (A : 'M_(m, n)),
  col_ebase A *m pid_mx (\rank A) *m row_ebase A = A.
Proof.
move=> m n A; rewrite mxrankE /col_ebase /row_ebase -!lock.
elim: m n A => [n A | m IHm]; first by rewrite [A]flatmx0 [_ *m _]flatmx0.
case=> [A | n]; first by rewrite [_ *m _]thinmx0 [A]thinmx0.
rewrite -(add1n m) -?(add1n n) => A /=.
case: pickP => [[i0 j0] | A0] /=; last first.
  apply/matrixP=> i j; rewrite pid_mx_0 mulmx0 mul0mx mxE.
  by move/eqP: (A0 (i, j)).
set a := A i0 j0 => nz_a; set A1 := xrow _ _ _.
set u := ursubmx _; set v := _ *: _; set B : 'M_(m, n) := _ - _.
move: (rank_leq_col B) (rank_leq_row B) {IHm}(IHm n B); rewrite mxrankE.
case: (gaussE B) => [[L U] r] /= r_m r_n defB.
have ->: pid_mx (1 + r) = block_mx 1 0 0 (pid_mx r) :> 'M[F]_(1 + m, 1 + n).
  rewrite -(subnKC r_m) -(subnKC r_n) pid_mx_block -col_mx0 -row_mx0.
  by rewrite block_mxA castmx_id col_mx0 row_mx0 -scalar_mx_block -pid_mx_block.
rewrite xcolE xrowE mulmxA -xcolE -!mulmxA.
rewrite !(addr0, add0r, mulmx0, mul0mx, mulmx_block, mul1mx) mulmxA defB.
rewrite addrC subrK mul_mx_scalar scalerA divff // scale1r.
have ->: a%:M = ulsubmx A1 by rewrite [_ A1]mx11_scalar !mxE !lshift0 !tpermR.
rewrite submxK /A1 xrowE !xcolE -!mulmxA mulmxA -!perm_mxM !tperm2 !perm_mx1.
by rewrite mulmx1 mul1mx.
Qed.

Lemma mulmx_base : forall m n (A : 'M_(m, n)), col_base A *m row_base A = A.
Proof.
by move=> m n A; rewrite mulmxA -[col_base A *m _]mulmxA pid_mx_id ?mulmx_ebase.
Qed.

Lemma mulmx1_min_rank : forall r m n (A : 'M_(m, n)) M N,
  M *m A *m N = 1%:M :> 'M_r -> r <= \rank A.
Proof.
move=> r m n A M N.
by rewrite -{1}(mulmx_base A) mulmxA -mulmxA; move/mulmx1_min.
Qed.
Implicit Arguments mulmx1_min_rank [r m n A].

Lemma mulmx_max_rank : forall r m n (M : 'M_(m, r)) (N : 'M_(r, n)),
  \rank (M *m N) <= r.
Proof.
move=> r m n M N; set MN := M *m N; set rMN := \rank _.
pose L : 'M_(rMN, m) := pid_mx rMN *m invmx (col_ebase MN).
pose U : 'M_(n, rMN) := invmx (row_ebase MN) *m pid_mx rMN.
suffices: L *m M *m (N *m U) = 1%:M by exact: mulmx1_min.
rewrite mulmxA -(mulmxA L) -[M *m N]mulmx_ebase -/MN.
by rewrite !mulmxA mulmxKV // mulmxK // !pid_mx_id /rMN ?pid_mx_1.
Qed.
Implicit Arguments mulmx_max_rank [r m n].

Lemma mxrank_tr : forall m n (A : 'M_(m, n)), \rank A^T = \rank A.
Proof.
move=> m n A; apply/eqP; rewrite eqn_leq -{3}[A]trmxK.
by rewrite -{1}(mulmx_base A) -{1}(mulmx_base A^T) !trmx_mul !mulmx_max_rank.
Qed.

Lemma mxrank_add : forall m n (A B : 'M_(m, n)),
  \rank (A + B)%R <= \rank A + \rank B.
Proof.
move=> m n A B; rewrite -{1}(mulmx_base A) -{1}(mulmx_base B) -mul_row_col.
exact: mulmx_max_rank.
Qed.

Lemma mxrankM_maxl : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank A.
Proof.
by move=> m n p A B; rewrite -{1}(mulmx_base A) -mulmxA mulmx_max_rank.
Qed.

Lemma mxrankM_maxr : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank B.
Proof.
by move=> m n p A B; rewrite -mxrank_tr -(mxrank_tr B) trmx_mul mxrankM_maxl.
Qed.

Lemma mxrank_scale : forall m n a (A : 'M_(m, n)),
  \rank (a *: A) <= \rank A.
Proof. by move=> m n a A; rewrite -mul_scalar_mx mxrankM_maxr. Qed.

Lemma mxrank_scale_nz : forall m n a (A : 'M_(m, n)),
  a != 0 -> \rank (a *: A) = \rank A.
Proof.
move=> m n a A nza; apply/eqP; rewrite eqn_leq -{3}[A]scale1r -(mulVf nza).
by rewrite -scalerA !mxrank_scale.
Qed.

Lemma mxrank_opp : forall m n (A : 'M_(m, n)), \rank (- A) = \rank A.
Proof.
by move=> m n A; rewrite -scaleN1r mxrank_scale_nz // oppr_eq0 oner_eq0.
Qed.

Lemma mxrank0 : forall m n, \rank (0 : 'M_(m, n)) = 0%N.
Proof.
by move=> m n; apply/eqP; rewrite -leqn0 -(@mulmx0 _ m 0 n 0) mulmx_max_rank.
Qed.

Lemma mxrank_eq0 : forall m n (A : 'M_(m, n)), (\rank A == 0%N) = (A == 0).
Proof.
move=> m n A; apply/eqP/eqP=> [rA0 | ->{A}]; last exact: mxrank0.
move: (col_base A) (row_base A) (mulmx_base A); rewrite rA0 => Ac Ar <-.
by rewrite [Ac]thinmx0 mul0mx.
Qed.

Lemma mulmx_coker : forall m n (A : 'M_(m, n)), A *m cokermx A = 0.
Proof.
move=> m n A; rewrite -{1}[A]mulmx_ebase -!mulmxA mulKVmx //.
by rewrite mul_pid_mx_copid ?mulmx0.
Qed.

Lemma submxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS = (A *m cokermx B == 0).
Proof. by move=> m1; rewrite mxopE. Qed.

Lemma mulmxKpV : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> A *m pinvmx B *m B = A.
Proof.
move=> m n p A B; rewrite submxE !mulmxA mulmx_subr mulmx1 subr_eq0.
move/eqP=> defA; rewrite -{4}[B]mulmx_ebase -!mulmxA mulKmx //.
by rewrite (mulmxA (pid_mx _)) pid_mx_id // !mulmxA -{}defA mulmxKV.
Qed.

Lemma submxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (exists D, A = D *m B) (A <= B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [|[D ->]].
  by move/mulmxKpV; exists (A *m pinvmx B).
by rewrite submxE -mulmxA mulmx_coker mulmx0.
Qed.
Implicit Arguments submxP [m1 m2 n A B].

Lemma submx_refl : forall m n (A : 'M_(m, n)), (A <= A)%MS.
Proof. by move=> m n A; rewrite submxE mulmx_coker. Qed.
Hint Resolve submx_refl.

Lemma submxMl : forall m n p (D : 'M_(m, n)) (A : 'M_(n, p)),
  (D *m A <= A)%MS.
Proof. by move=> m n p D A; rewrite submxE -mulmxA mulmx_coker mulmx0. Qed.

Lemma submxMr : forall m1 m2 n p,
                   forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A <= B)%MS -> (A *m C <= B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C; case/submxP=> D ->; rewrite -mulmxA submxMl.
Qed.

Lemma mulmx_sub : forall m n1 n2 p (C : 'M_(m, n1)) A (B : 'M_(n2, p)),
  (A <= B -> C *m A <= B)%MS.
Proof.
by move=> m n1 n2 p C A B; case/submxP=> D ->; rewrite mulmxA submxMl.
Qed.

Lemma submx_trans : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= B -> B <= C -> A <= C)%MS.
Proof.
move=> m1 m2 m3 n A B C; case/submxP=> D ->{A}; exact: mulmx_sub.
Qed.

Lemma ltmx_sub_trans : forall m1 m2 m3 n
  (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A < B)%MS -> (B <= C)%MS -> (A < C)%MS.
Proof.
move=> m1 m2 m3 n A B C; case/andP=> sAB ltAB sBC.
rewrite ltmxE (submx_trans sAB) //.
by apply: contra ltAB; exact: submx_trans.
Qed.

Lemma sub_ltmx_trans : forall m1 m2 m3 n
  (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= B)%MS -> (B < C)%MS -> (A < C)%MS.
Proof.
move=> m1 m2 m3 n A B C sAB; case/andP=> sBC ltBC.
rewrite ltmxE (submx_trans sAB) //.
by apply: contra ltBC => sCA; exact: submx_trans sAB.
Qed.

Lemma ltmx_trans : forall m n, transitive (@ltmx m m n).
Proof. by move=> m n A B C; move/ltmxW; exact: sub_ltmx_trans. Qed.

Lemma ltmx_irrefl : forall m n, irreflexive (@ltmx m m n).
Proof. by move=> m n A; rewrite /ltmx submx_refl andbF. Qed.

Lemma sub0mx : forall m1 m2 n (A : 'M_(m2, n)),
  ((0 : 'M_(m1, n)) <= A)%MS.
Proof. by move=> m1 m2 n A; rewrite submxE mul0mx. Qed.

Lemma submx0null : forall m1 m2 n (A : 'M[F]_(m1, n)),
  (A <= (0 : 'M_(m2, n)))%MS -> A = 0.
Proof. by move=> m1 m2 n A; case/submxP=> D; rewrite mulmx0. Qed.

Lemma submx0 : forall m n (A : 'M_(m, n)), (A <= (0 : 'M_n))%MS = (A == 0).
Proof.
move=> m n A; apply/idP/eqP=> [|->]; [exact: submx0null | exact: sub0mx].
Qed.

Lemma lt0mx : forall m n (A : 'M_(m, n)), ((0 : 'M_n) < A)%MS = (A != 0).
Proof. by move=> m n A; rewrite /ltmx sub0mx submx0. Qed.

Lemma ltmx0 : forall m n (A : 'M[F]_(m, n)), (A < (0 : 'M_n))%MS = false.
Proof. by move=> m n A; rewrite /ltmx sub0mx andbF. Qed.

Lemma eqmx0P : forall m n (A : 'M_(m, n)),
  reflect (A = 0) (A == (0 : 'M_n))%MS.
Proof. by move=> m n A; rewrite submx0 sub0mx andbT; exact: eqP. Qed.

Lemma eqmx_eq0 : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MS -> (A == 0) = (B == 0).
Proof. by move=> m1 m2 n A B eqAB; rewrite -!submx0 eqAB. Qed.

Lemma addmx_sub : forall m1 m2 n,
                  forall (A : 'M_(m1, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (A <= C)%MS -> (B <= C)%MS -> ((A + B)%R <= C)%MS.
Proof.
move=> m1 m2 n A B C; case/submxP=> A' ->; case/submxP=> B' ->.
by rewrite -mulmx_addl submxMl.
Qed.

Lemma summx_sub : forall m1 m2 n (B : 'M_(m2, n)),
                     forall I r (P : pred I) (A_ : I -> 'M_(m1, n)),
  (forall i, P i -> A_ i <= B)%MS -> ((\sum_(i <- r | P i) A_ i)%R <= B)%MS.
Proof.
move=> m1 m2 n B; pose leB (A : 'M_(m1, n)) := (A <= B)%MS.
apply: (@big_prop _ leB) => [| A1 A2]; [exact: sub0mx | exact: addmx_sub].
Qed.

Lemma scalemx_sub : forall m1 m2 n a (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> (a *: A <= B)%MS.
Proof.
by move=> m1 m2 n a A B; case/submxP=> A' ->; rewrite scalemxAl submxMl.
Qed.

Lemma row_sub : forall m n i (A : 'M_(m, n)), (row i A <= A)%MS.
Proof. by move=> m n i A; rewrite rowE submxMl. Qed.

Lemma eq_row_sub : forall m n v (A : 'M_(m, n)) i, row i A = v -> (v <= A)%MS.
Proof. by move=> m n v A i <-; rewrite row_sub. Qed.

Lemma nz_row_sub : forall m n (A : 'M_(m, n)), (nz_row A <= A)%MS.
Proof.
by rewrite /nz_row => m n A; case: pickP => [i|] _; rewrite ?row_sub ?sub0mx.
Qed.

Lemma row_subP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (forall i, row i A <= B)%MS (A <= B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [sAB i|sAB].
  by apply: submx_trans sAB; exact: row_sub.
rewrite submxE; apply/eqP; apply/row_matrixP=> i; apply/eqP.
by rewrite row_mul row0 -submxE.
Qed.
Implicit Arguments row_subP [m1 m2 n A B].

Lemma rV_subP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (forall v : 'rV_n, v <= A -> v <= B)%MS (A <= B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [sAB v Av | sAB].
  exact: submx_trans sAB.
by apply/row_subP=> i; rewrite sAB ?row_sub.
Qed.
Implicit Arguments rV_subP [m1 m2 n A B].

Lemma row_subPn : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (exists i, ~~ (row i A <= B)%MS) (~~ (A <= B)%MS).
Proof.
move=> m1 m2 n A B; rewrite (sameP row_subP forallP) negb_forall.
exact: existsP.
Qed.

Lemma sub_rVP : forall n (u v : 'rV_n),
  reflect (exists a, u = a *: v) (u <= v)%MS.
Proof.
move=> n u v; apply: (iffP submxP) => [[w ->] | [a ->]].
  by exists (w 0 0); rewrite -mul_scalar_mx -mx11_scalar.
by exists a%:M; rewrite mul_scalar_mx.
Qed.

Lemma rank_rV : forall n (v : 'rV_n), \rank v = (v != 0).
Proof.
move=> n v; case: eqP => [-> | nz_v]; first by rewrite mxrank0.
by apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0; exact/eqP.
Qed.

Lemma rowV0Pn : forall m n (A : 'M_(m, n)),
  reflect (exists2 v : 'rV_n, v <= A & v != 0)%MS (A != 0).
Proof.
move=> m n A; rewrite -submx0; apply: (iffP idP) => [| [v svA]]; last first.
  by rewrite -submx0; exact: contra (submx_trans _).
by case/row_subPn=> i; rewrite submx0; exists (row i A); rewrite ?row_sub.
Qed.

Lemma rowV0P : forall m n (A : 'M_(m, n)),
  reflect (forall v : 'rV_n, v <= A -> v = 0)%MS (A == 0).
Proof.
move=> m n A; rewrite -[A == 0]negbK; case: rowV0Pn => IH.
  by right; case: IH => v svA nzv IH; case/eqP: nzv; exact: IH.
by left=> v svA; apply/eqP; apply/idPn=> nzv; case: IH; exists v.
Qed.

Lemma submx_full : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full B -> (A <= B)%MS.
Proof.
move=> m1 m2 n A B; rewrite submxE /cokermx; move/eqnP->.
by rewrite /copid_mx pid_mx_1 subrr !mulmx0.
Qed.

Lemma row_fullP : forall m n (A : 'M_(m, n)),
  reflect (exists B, B *m A = 1%:M) (row_full A).
Proof.
move=> m n A; apply: (iffP idP) => [Afull | [B kA]].
  by exists (1%:M *m pinvmx A); apply: mulmxKpV (submx_full _ Afull).
by rewrite [_ A]eqn_leq rank_leq_col (mulmx1_min_rank B 1%:M) ?mulmx1.
Qed.
Implicit Arguments row_fullP [m n A].

Lemma row_full_inj : forall m n p A, row_full A -> injective (@mulmx _ m n p A).
Proof.
move=> m n p A; case/row_fullP=> A' A'K; apply: can_inj (mulmx A') _ => B.
by rewrite mulmxA A'K mul1mx.
Qed.

Lemma row_freeP : forall m n (A : 'M_(m, n)),
  reflect (exists B, A *m B = 1%:M) (row_free A).
Proof.
move=> m n A; rewrite /row_free -mxrank_tr.
apply: (iffP row_fullP) => [] [B kA];
  by exists B^T; rewrite -trmx1 -kA trmx_mul ?trmxK.
Qed.

Lemma row_free_inj : forall m n p A,
  row_free A -> injective ((@mulmx _ m n p)^~ A).
Proof.
move=> m n p A; case/row_freeP=> A' AK; apply: can_inj (mulmx^~ A') _ => B.
by rewrite -mulmxA AK mulmx1.
Qed.

Lemma row_free_unit : forall n (A : 'M_n), row_free A = (A \in unitmx).
Proof.
move=> n A; apply/row_fullP/idP=> [[A'] | uA]; first by case/mulmx1_unit.
by exists (invmx A); rewrite mulVmx.
Qed.

Lemma row_full_unit : forall n (A : 'M_n), row_full A = (A \in unitmx).
Proof. exact: row_free_unit. Qed.
  
Lemma mxrank_unit : forall n (A : 'M_n), A \in unitmx -> \rank A = n.
Proof. by move=> n A; rewrite -row_full_unit; move/eqnP. Qed.

Lemma mxrank1 : forall n, \rank (1%:M : 'M_n) = n.
Proof. move=> n; apply: mxrank_unit; exact: unitmx1. Qed.

Lemma mxrank_delta : forall m n i j, \rank (delta_mx i j : 'M_(m, n)) = 1%N.
Proof.
move=> m n i j; apply/eqP; rewrite eqn_leq lt0n mxrank_eq0.
rewrite -{1}(mul_delta_mx (0 : 'I_1)) mulmx_max_rank.
by apply/eqP; move/matrixP; move/(_ i j); move/eqP; rewrite !mxE !eqxx oner_eq0.
Qed.

Lemma mxrankS : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B.
Proof. by move=> m1 m2 n A B; case/submxP=> D ->; rewrite mxrankM_maxr. Qed.

Lemma submx1 : forall m n (A : 'M_(m, n)), (A <= 1%:M)%MS.
Proof. by move=> m n A; rewrite submx_full // row_full_unit unitmx1. Qed.

Lemma sub1mx : forall m n (A : 'M_(m, n)), (1%:M <= A)%MS = row_full A.
Proof.
move=> m n A; apply/idP/idP; last exact: submx_full.
by move/mxrankS; rewrite mxrank1 col_leq_rank.
Qed.

Lemma ltmx1 : forall m n (A : 'M_(m, n)), (A < 1%:M)%MS = ~~ row_full A.
Proof. by move=> m n A; rewrite /ltmx sub1mx submx1. Qed.

Lemma lt1mx : forall m n (A : 'M_(m, n)), (1%:M < A)%MS = false.
Proof. by move=> m n A; rewrite /ltmx submx1 andbF. Qed.

Lemma eqmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :=: B)%MS (A == B)%MS.
Proof.
move=> m1 m2 n A B.
apply: (iffP andP) => [[sAB sBA] | eqAB]; last by rewrite !eqAB.
split=> [|m3 C]; first by apply/eqP; rewrite eqn_leq !mxrankS.
split; first by apply/idP/idP; exact: submx_trans.
by apply/idP/idP=> sC; exact: submx_trans sC _.
Qed.
Implicit Arguments eqmxP [m1 m2 n A B].

Lemma rV_eqP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (forall u : 'rV_n, (u <= A) = (u <= B))%MS (A == B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [eqAB u | eqAB].
  by rewrite (eqmxP eqAB).
by apply/andP; split; apply/rV_subP=> u; rewrite eqAB.
Qed.

Lemma eqmx_refl : forall m1 n (A : 'M_(m1, n)), (A :=: A)%MS.
Proof. by []. Qed.

Lemma eqmx_sym : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MS -> (B :=: A)%MS.
Proof. by move=> m1 m2 n A B eqAB; split=> [|m3 C]; rewrite !eqAB. Qed.

Lemma eqmx_trans : forall m1 m2 m3 n,
                   forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A :=: B)%MS -> (B :=: C)%MS -> (A :=: C)%MS.
Proof.
by move=> m1 m2 m3 n A B C eqAB eqBC; split=> [|m4 D]; rewrite !eqAB !eqBC.
Qed.

Lemma eqmx_rank : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A == B)%MS -> \rank A = \rank B.
Proof. by move=> m1 m2 n A B; move/eqmxP->. Qed.

Lemma lt_eqmx : forall m1 m2 m3 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
    (A :=: B)%MS ->
  forall C : 'M_(m3, n), (((A < C) = (B < C))%MS * ((C < A) = (C < B))%MS)%type.
Proof. by move=> m1 m2 m3 n A B eqAB C; rewrite /ltmx !eqAB. Qed.

Lemma eqmxMr : forall m1 m2 n p,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A :=: B)%MS -> (A *m C :=: B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C eqAB; apply/eqmxP; rewrite !submxMr ?eqAB.
Qed.

Lemma eqmxMfull : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  row_full A -> (A *m B :=: B)%MS.
Proof.
move=> m n p A B; case/row_fullP=> A' A'A; apply/eqmxP; rewrite submxMl /=.
by apply/submxP; exists A'; rewrite mulmxA A'A mul1mx.
Qed.

Lemma eqmx0 : forall m n, ((0 : 'M[F]_(m, n)) :=: (0 : 'M_n))%MS.
Proof. by move=> m n; apply/eqmxP; rewrite !sub0mx. Qed.

Lemma eqmx_scale : forall m n a (A : 'M_(m, n)), a != 0 -> (a *: A :=: A)%MS.
Proof.
move=> m n a A nz_a; apply/eqmxP; rewrite scalemx_sub //.
by rewrite -{1}[A]scale1r -(mulVf nz_a) -scalerA scalemx_sub.
Qed.

Lemma eqmx_opp : forall m n (A : 'M_(m, n)), (- A :=: A)%MS.
Proof.
move=> m n A; rewrite -scaleN1r; apply: eqmx_scale => //.
by rewrite oppr_eq0 oner_eq0.
Qed.

Lemma submxMfree : forall m1 m2 n p,
                     forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  row_free C -> (A *m C <= B *m C)%MS = (A <= B)%MS.
Proof.
move=> m1 m2 n p A B C; case/row_freeP=> C' C_C'_1.
apply/idP/idP=> sAB; last exact: submxMr.
by rewrite -[A]mulmx1 -[B]mulmx1 -C_C'_1 !mulmxA submxMr.
Qed.

Lemma eqmxMfree : forall m1 m2 n p,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  row_free C -> (A *m C :=: B *m C)%MS -> (A :=: B)%MS.
Proof.
move=> m1 m2 n p A B C Cfree eqAB; apply/eqmxP; move/eqmxP: eqAB.
by rewrite !submxMfree.
Qed.

Lemma mxrankMfree : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  row_free B -> \rank (A *m B) = \rank A.
Proof.
move=> m n p A B Bfree.
by rewrite -mxrank_tr trmx_mul eqmxMfull /row_full mxrank_tr.
Qed.

Lemma eq_row_base : forall m n (A : 'M_(m, n)), (row_base A :=: A)%MS.
Proof.
move=> m n A; apply/eqmxP; apply/andP; split; apply/submxP.
  exists (pid_mx (\rank A) *m invmx (col_ebase A)).
  by rewrite -{8}[A]mulmx_ebase !mulmxA mulmxKV // pid_mx_id.
exists (col_ebase A *m pid_mx (\rank A)).
by rewrite mulmxA -(mulmxA _ _ (pid_mx _)) pid_mx_id // mulmx_ebase.
Qed.

Let qidmx_eq1 : forall n (A : 'M_n), qidmx A = (A == 1%:M).
Proof. by move=> A; rewrite /qidmx eqxx pid_mx_1. Qed.

Let genmx_witnessP : forall m n (A : 'M_(m, n)),
  equivmx A (row_full A) (genmx_witness A).
Proof.
move=> m n A; rewrite /equivmx qidmx_eq1 /genmx_witness.
case fullA: (row_full A); first by rewrite eqxx sub1mx submx1 fullA.
set B := _ *m _; have defB : (B == A)%MS.
  apply/andP; split; apply/submxP.
    exists (pid_mx (\rank A) *m invmx (col_ebase A)).
    by rewrite -{3}[A]mulmx_ebase !mulmxA mulmxKV // pid_mx_id.
  exists (col_ebase A *m pid_mx (\rank A)).
  by rewrite mulmxA -(mulmxA _ _ (pid_mx _)) pid_mx_id // mulmx_ebase.
rewrite defB -negb_add addbF; case: eqP defB => // ->.
by rewrite sub1mx fullA.
Qed.

Lemma genmxE : forall m n (A : 'M_(m, n)), (<<A>> :=: A)%MS.
Proof.
move=> m n A; rewrite mxopE; apply/eqmxP.
by case/andP: (chooseP (genmx_witnessP A)).
Qed.

Lemma eq_genmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B -> <<A>> = <<B>>)%MS.
Proof.
move=> m1 m2 n A B eqAB; rewrite ![@genmx _]mxopE.
have{eqAB} eqAB: equivmx A (row_full A) =1 equivmx B (row_full B).
  by move=> C; rewrite /row_full /equivmx !eqAB.
rewrite (eq_choose eqAB) (choose_id _ (genmx_witnessP B)) //.
by rewrite -eqAB genmx_witnessP.
Qed.

Lemma genmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (<<A>> = <<B>>)%MS (A == B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => eqAB; first exact: eq_genmx (eqmxP _).
by rewrite -!(genmxE A) eqAB !genmxE andbb.
Qed.
Implicit Arguments genmxP [m1 m2 n A B].

Lemma genmx0 : forall m n, <<0 : 'M_(m, n)>>%MS = 0.
Proof. by move=> m n; apply/eqP; rewrite -submx0 genmxE sub0mx. Qed.

Lemma genmx1 : forall n, <<1%:M : 'M_n>>%MS = 1%:M.
Proof.
move=> n; rewrite mxopE; case/andP: (chooseP (@genmx_witnessP n n 1%:M)) => _.
by move/eqP; rewrite qidmx_eq1 row_full_unit unitmx1; move/eqP.
Qed.

Lemma genmx_id : forall m n (A : 'M_(m, n)), (<<<<A>>>> = <<A>>)%MS.
Proof. by move=> m n A; apply: eq_genmx; exact: genmxE. Qed.

Lemma row_base_free : forall m n (A : 'M_(m, n)), row_free (row_base A).
Proof. by move=> m n A; apply/eqnP; rewrite eq_row_base. Qed.

Lemma mxrank_gen : forall m n (A : 'M_(m, n)), \rank <<A>> = \rank A.
Proof. by move=> m n A; rewrite genmxE. Qed.

Lemma col_base_full : forall m n (A : 'M_(m, n)), row_full (col_base A).
Proof.
move=> m n A; apply/row_fullP.
exists (pid_mx (\rank A) *m invmx (col_ebase A)).
by rewrite !mulmxA mulmxKV // pid_mx_id // pid_mx_1.
Qed.
Hint Resolve row_base_free col_base_full.

Lemma mxrank_leqif_sup : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B ?= iff (B <= A)%MS.
Proof.
move=> m1 m2 n A B sAB; split; first by rewrite mxrankS.
apply/idP/idP=> [| sBA]; last by rewrite eqn_leq !mxrankS.
case/submxP: sAB => D ->; rewrite -{-2}(mulmx_base B) mulmxA.
rewrite mxrankMfree //; case/row_fullP=> E kE.
by rewrite -{1}[row_base B]mul1mx -kE -(mulmxA E) (mulmxA _ E) submxMl.
Qed.

Lemma mxrank_leqif_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B ?= iff (A == B)%MS.
Proof. by move=> m1 m2 n A B sAB; rewrite sAB; exact: mxrank_leqif_sup. Qed.

Lemma ltmxErank : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A < B)%MS = (A <= B)%MS && (\rank A < \rank B).
Proof.
move=> m1 m2 n A B; apply: andb_id2l => sAB.
by rewrite (ltn_leqif (mxrank_leqif_sup sAB)).
Qed.

Lemma rank_ltmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A < B)%MS -> \rank A < \rank B.
Proof. by move=> m1 m2 n A B; rewrite ltmxErank; case/andP. Qed.

Lemma eqmx_cast : forall m1 m2 n (A : 'M_(m1, n)) e,
  ((castmx e A : 'M_(m2, n)) :=: A)%MS.
Proof. by move=> m1 m2 n A [e]; case: m2 / e A => A e; rewrite castmx_id. Qed.

Lemma eqmx_conform : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (conform_mx A B :=: A \/ conform_mx A B :=: B)%MS.
Proof.
move=> m1 m2 n A; case: (eqVneq m2 m1) => [-> | neqm12] B.
  by right; rewrite conform_mx_id.
by left; rewrite nonconform_mx ?neqm12.
Qed.

Let eqmx_sum_nop : forall m n (A : 'M_(m, n)), (addsmx_nop A :=: A)%MS.
Proof.
move=> m n A; case: (eqmx_conform <<A>>%MS A) => // eq_id_gen.
exact: eqmx_trans (genmxE A).
Qed.

Section AddsmxSub.

Variable (m1 m2 n : nat) (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)).

Lemma col_mx_sub : forall m3 (C : 'M_(m3, n)),
  (col_mx A B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
Proof.
move=> m3 C; rewrite !submxE mul_col_mx -col_mx0.
by apply/eqP/andP; [case/eq_col_mx=> -> -> | case; do 2!move/eqP->].
Qed.

Lemma addsmxE : (A + B :=: col_mx A B)%MS.
Proof.
have:= submx_refl (col_mx A B); rewrite col_mx_sub; case/andP=> sAS sBS.
rewrite mxopE; do 2?case: eqP => [AB0 | _]; last exact: genmxE.
  by apply/eqmxP; rewrite !eqmx_sum_nop sBS col_mx_sub AB0 sub0mx /=.
by apply/eqmxP; rewrite !eqmx_sum_nop sAS col_mx_sub AB0 sub0mx andbT /=.
Qed.

Lemma addsmx_sub : forall m3 (C : 'M_(m3, n)),
  (A + B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
Proof. by move=> m3 C; rewrite addsmxE col_mx_sub. Qed.

Lemma addsmxSl : (A <= A + B)%MS.
Proof. by have:= submx_refl (A + B)%MS; rewrite addsmx_sub; case/andP. Qed.

Lemma addsmxSr : (B <= A + B)%MS.
Proof. by have:= submx_refl (A + B)%MS; rewrite addsmx_sub; case/andP. Qed.

Lemma addsmx_idPr : reflect (A + B :=: B)%MS (A <= B)%MS.
Proof.
have:= @eqmxP _ _ _ (A + B)%MS B.
by rewrite addsmxSr addsmx_sub submx_refl !andbT.
Qed.

Lemma addsmx_idPl : reflect (A + B :=: A)%MS (B <= A)%MS.
Proof.
have:= @eqmxP _ _ _ (A + B)%MS A.
by rewrite addsmxSl addsmx_sub submx_refl !andbT.
Qed.

End AddsmxSub.

Lemma adds0mx: forall m1 m2 n (B : 'M_(m2, n)),
  ((0 : 'M_(m1, n)) + B :=: B)%MS.
Proof.
by move=> *; apply/eqmxP; rewrite addsmx_sub sub0mx addsmxSr /= andbT.
Qed.

Lemma addsmx0: forall m1 m2 n (A : 'M_(m1, n)),
  (A + (0 : 'M_(m2, n)) :=: A)%MS.
Proof.
by move=> *; apply/eqmxP; rewrite addsmx_sub sub0mx addsmxSl /= !andbT.
Qed.

Let addsmx_nop_eq0 : forall m n (A : 'M_(m, n)), (addsmx_nop A == 0) = (A == 0).
Proof. by move=> m n A; rewrite -!submx0 eqmx_sum_nop. Qed.

Let addsmx_nop0 : forall m n, addsmx_nop (0 : 'M_(m, n)) = 0.
Proof. by move=> m n; apply/eqP; rewrite addsmx_nop_eq0. Qed.

Let addsmx_nop_id : forall n (A : 'M_n), addsmx_nop A = A.
Proof. by move=> n A; exact: conform_mx_id. Qed.

Lemma addsmxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A + B = B + A)%MS.
Proof.
move=> m1 m2 n A B; have: (A + B == B + A)%MS.
  by apply/andP; rewrite !addsmx_sub andbC -addsmx_sub andbC -addsmx_sub.
move/genmxP; rewrite ![@addsmx _]mxopE -!submx0 !submx0.
by do 2!case: eqP => [// -> | _]; rewrite ?genmx_id ?addsmx_nop0.
Qed.

Lemma adds0mx_id : forall m1 n (B : 'M_n), ((0 : 'M_(m1, n)) + B)%MS = B.
Proof. by move=> m2 n B; rewrite mxopE eqxx addsmx_nop_id. Qed.

Lemma addsmx0_id : forall m2 n (A : 'M_n), (A + (0 : 'M_(m2, n)))%MS = A.
Proof. by move=> m2 n A; rewrite addsmxC adds0mx_id. Qed.

Lemma addsmxA : forall m1 m2 m3 n,
                forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A + (B + C) = A + B + C)%MS.
Proof.
move=> m1 m2 m3 n A B C; have: (A + (B + C) :=: A + B + C)%MS.
  by apply/eqmxP; apply/andP; rewrite !addsmx_sub -andbA andbA -!addsmx_sub.
rewrite {1 3}[@addsmx m1]mxopE [@addsmx n]mxopE !addsmx_nop_id -!submx0.
rewrite !addsmx_sub ![@addsmx _]mxopE -!submx0; move/eq_genmx.
by do 3!case: (_ <= 0)%MS; rewrite //= !genmx_id.
Qed.

Canonical Structure addsmx_monoid n :=
  Monoid.Law (@addsmxA n n n n) (@adds0mx_id n n) (@addsmx0_id n n).
Canonical Structure addsmx_comoid n := Monoid.ComLaw (@addsmxC n n n).

Lemma addsmxMr : forall m1 m2 n p,
                forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  ((A + B)%MS *m C :=: A *m C + B *m C)%MS.
Proof.
move=> m1 m2 n p A B C; apply/eqmxP; rewrite !addsmxE -!mul_col_mx.
by rewrite !submxMr ?addsmxE.
Qed.

Lemma addsmxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> A + B <= C + D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD.
by rewrite addsmx_sub {1}addsmxC !(submx_trans _ (addsmxSr _ _)).
Qed.

Lemma addmx_sub_adds : forall m m1 m2 n,
    forall (A : 'M_(m, n)) (B : 'M_(m, n)) (C : 'M_(m1, n)) (D : 'M_(m2, n)),
  (A <= C -> B <= D -> (A + B)%R <= C + D)%MS.
Proof.
move=> m m1 m2 n A B C D sAC; move/(addsmxS sAC); apply: submx_trans.
by rewrite addmx_sub ?addsmxSl ?addsmxSr.
Qed.

Lemma addsmx_addKl : forall n m1 m2 (A : 'M_(m1, n)) (B C : 'M_(m2, n)),
  (B <= A)%MS -> (A + (B + C)%R :=: A + C)%MS.
Proof.
move=> n m1 m2 A B C sBA; apply/eqmxP; rewrite !addsmx_sub !addsmxSl.
by rewrite -{3}[C](addKr B) !addmx_sub_adds ?eqmx_opp.
Qed.

Lemma addsmx_addKr : forall n m1 m2 (A B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (B <= C)%MS -> ((A + B)%R + C :=: A + C)%MS.
Proof.
by move=> n m1 m2 A B C; rewrite -!(addsmxC C) addrC; exact: addsmx_addKl.
Qed.

Lemma adds_eqmx : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A :=: C -> B :=: D -> A + B :=: C + D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D eqAC eqBD.
by apply/eqmxP; rewrite !addsmxS ?eqAC ?eqBD.
Qed.

Lemma genmx_adds : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (<<(A + B)%MS>> = <<A>> + <<B>>)%MS.
Proof.
move=> m1 m2 n A B; rewrite -(eq_genmx (adds_eqmx (genmxE A) (genmxE B))).
by rewrite ![@addsmx _]mxopE !addsmx_nop_id !(fun_if (@genmx _ _)) !genmx_id.
Qed.

Lemma sub_addsmxP : forall m1 m2 m3 n,
                  forall (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  reflect (exists u, A = u.1 *m B + u.2 *m C) (A <= B + C)%MS.
Proof.
move=> m1 m2 m3 n A B C; apply: (iffP idP) => [|[u ->]]; last first.
  by rewrite addmx_sub_adds ?submxMl.
rewrite addsmxE; case/submxP=> u ->; exists (lsubmx u, rsubmx u).
by rewrite -mul_row_col hsubmxK.
Qed.
Implicit Arguments sub_addsmxP [m1 m2 m3 n A B C].

Variable I : finType.
Implicit Type P : pred I.

Lemma genmx_sums : forall P n (B_ : I -> 'M_n),
  <<(\sum_(i | P i) B_ i)%MS>>%MS = (\sum_(i | P i) <<B_ i>>)%MS.
Proof. move=> P n; exact: (big_morph _ (@genmx_adds n n n) (@genmx0 n n)). Qed.

Lemma sumsmx_sup : forall i0 P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  P i0 -> (A <= B_ i0)%MS -> (A <= \sum_(i | P i) B_ i)%MS.
Proof.
move=> i0 P m n A B_ Pi0 sAB; apply: submx_trans sAB _.
by rewrite (bigD1 i0) // addsmxSl.
Qed.
Implicit Arguments sumsmx_sup [P m n A B_].

Lemma sumsmx_subP : forall P m n (A_ : I -> 'M_n) (B : 'M_(m, n)),
  reflect (forall i, P i -> A_ i <= B)%MS (\sum_(i | P i) A_ i <= B)%MS.
Proof.
move=> P m n A_ B; apply: (iffP idP) => [sAB i Pi | sAB].
  by apply: submx_trans sAB; apply: sumsmx_sup Pi _.
by apply big_prop => // [|A1 A2 sA1B]; rewrite ?sub0mx // addsmx_sub sA1B.
Qed.

Lemma summx_sub_sums : forall P m n (A : I -> 'M[F]_(m, n)) B,
    (forall i, P i -> A i <= B i)%MS ->
  ((\sum_(i | P i) A i)%R <= \sum_(i | P i) B i)%MS.
Proof.
by move=> P m n A B sAB; apply: summx_sub => i Pi; rewrite (sumsmx_sup i) ?sAB.
Qed.

Lemma sumsmxS : forall P n (A B : I -> 'M[F]_n),
    (forall i, P i -> A i <= B i)%MS ->
  (\sum_(i | P i) A i <= \sum_(i | P i) B i)%MS.
Proof.
by move=> P n A B sAB; apply/sumsmx_subP=> i Pi; rewrite (sumsmx_sup i) ?sAB.
Qed.

Lemma eqmx_sums : forall P n (A B : I -> 'M[F]_n),
    (forall i, P i -> A i :=: B i)%MS ->
  (\sum_(i | P i) A i :=: \sum_(i | P i) B i)%MS.
Proof.
by move=> P n A B eqAB; apply/eqmxP; rewrite !sumsmxS // => i; move/eqAB->.
Qed.

Lemma sub_sumsmxP : forall P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  reflect (exists u_, A = \sum_(i | P i) u_ i *m B_ i)
          (A <= \sum_(i | P i) B_ i)%MS.
Proof.
move=> P m n A B_; apply: (iffP idP) => [| [u_ ->]]; last first.
  by apply: summx_sub_sums => i _; exact: submxMl. 
elim: {P}_.+1 {-2}P A (ltnSn #|P|) => // b IHb P A.
case: (pickP P) => [i Pi | P0 _]; last first.
  rewrite big_pred0 //; move/submx0null->.
  by exists (fun _ => 0); rewrite big_pred0.
rewrite (cardD1x Pi) (bigD1 i) //=; move/IHb=> {b IHb} /= IHi.
case/sub_addsmxP=> u ->; have [u_ ->] := IHi _ (submxMl u.2 _).
exists [eta u_ with i |-> u.1]; rewrite (bigD1 i Pi) /= eqxx; congr (_ + _).
by apply: eq_bigr => j; case/andP=> _; move/negPf->.
Qed.

Lemma sumsmxMr_gen : forall P m n A (B : 'M[F]_(m, n)),
  ((\sum_(i | P i) A i)%MS *m B :=: \sum_(i | P i) <<A i *m B>>)%MS.
Proof.
move=> P m n A B; apply/eqmxP; apply/andP; split; last first.
  by apply/sumsmx_subP=> i Pi; rewrite genmxE submxMr ?(sumsmx_sup i).
have [u ->] := sub_sumsmxP _ _ _ (submx_refl (\sum_(i | P i) A i)%MS).
by rewrite mulmx_suml summx_sub_sums // => i _; rewrite genmxE -mulmxA submxMl.
Qed.

Lemma sumsmxMr :  forall P n (A_ : I -> 'M[F]_n) (B : 'M_n),
  ((\sum_(i | P i) A_ i)%MS *m B :=: \sum_(i | P i) (A_ i *m B))%MS.
Proof.
move=> P n A_ B; apply: eqmx_trans (sumsmxMr_gen _ _ _) (eqmx_sums _) => i _.
exact: genmxE.
Qed.

Lemma rank_pid_mx : forall m n r,
  r <= m -> r <= n -> \rank (pid_mx r : 'M_(m, n)) = r.
Proof.
move=> m n r; do 2!move/subnKC <-; rewrite pid_mx_block block_mxEv row_mx0.
rewrite -addsmxE addsmx0 -mxrank_tr tr_row_mx trmx0 trmx1 -addsmxE addsmx0.
exact: mxrank1.
Qed.

Lemma rank_copid_mx : forall n r,
  r <= n -> \rank (copid_mx r : 'M_n) = (n - r)%N.
Proof.
move=> n r; move/subnKC <-; rewrite /copid_mx pid_mx_block scalar_mx_block.
rewrite opp_block_mx !oppr0 add_block_mx !addr0 subrr block_mxEv row_mx0.
rewrite -addsmxE adds0mx -mxrank_tr tr_row_mx trmx0 trmx1.
by rewrite -addsmxE adds0mx mxrank1 addKn.
Qed.

Lemma mxrank_compl : forall m n (A : 'M_(m, n)), \rank A^C = (n - \rank A)%N.
Proof. by move=> m n A; rewrite mxrankMfree ?row_free_unit ?rank_copid_mx. Qed.

Lemma mxrank_ker : forall m n (A : 'M_(m, n)),
  \rank (kermx A) = (m - \rank A)%N.
Proof.
by move=> m n A; rewrite mxrankMfree ?row_free_unit ?unitmx_inv ?rank_copid_mx.
Qed.

Lemma kermx_eq0 : forall n m (A : 'M_(m, n)), (kermx A == 0) = row_free A.
Proof.
by move=> n m A; rewrite -mxrank_eq0 mxrank_ker subn_eq0 row_leq_rank.
Qed.

Lemma mxrank_coker : forall m n (A : 'M_(m, n)),
  \rank (cokermx A) = (n - \rank A)%N.
Proof.
by move=> m n A; rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?rank_copid_mx.
Qed.

Lemma cokermx_eq0 : forall n m (A : 'M_(m, n)), (cokermx A == 0) = row_full A.
Proof.
by move=> n m A; rewrite -mxrank_eq0 mxrank_coker subn_eq0 col_leq_rank.
Qed.

Lemma mulmx_ker : forall m n (A : 'M_(m, n)), kermx A *m A = 0.
Proof.
move=> m n A; rewrite -{2}[A]mulmx_ebase !mulmxA mulmxKV //.
by rewrite mul_copid_mx_pid ?mul0mx.
Qed.

Lemma mulmxKV_ker : forall m n p (A : 'M_(n, p)) (B : 'M_(m, n)),
  B *m A = 0 -> B *m col_ebase A *m kermx A = B.
Proof.
move=> m n p A B; rewrite mulmxA mulmx_subr mulmx1 mulmx_subl mulmxK //.
rewrite -{1}[A]mulmx_ebase !mulmxA; move/(canRL (mulmxK (row_ebase_unit A))).
rewrite mul0mx // => BA0; apply: (canLR (addrK _)).
by rewrite -(pid_mx_id _ _ n (rank_leq_col A)) mulmxA BA0 !mul0mx addr0.
Qed.

Lemma sub_kermxP : forall p m n (A : 'M_(m, n)) (B : 'M_(p, m)),
  reflect (B *m A = 0) (B <= kermx A)%MS.
Proof.
move=> p m n A B; apply: (iffP submxP) => [[D ->]|].
  by rewrite -mulmxA mulmx_ker mulmx0.
by move/mulmxKV_ker; exists (B *m col_ebase A).
Qed.

Lemma det0P : forall n (A : 'M_n),
  reflect (exists2 v : 'rV[F]_n, v != 0 & v *m A = 0) (\det A == 0).
Proof.
move=> n A; rewrite -[_ == _]negbK -unitfE -unitmxE.
apply: (iffP idP) => [| [v n0v vA0]]; last first.
  by apply: contra n0v => uA; rewrite -(mulmxK uA v) vA0 mul0mx.
rewrite -row_free_unit /row_free eqn_leq rank_leq_row -subn_eq0.
rewrite -mxrank_ker mxrank_eq0 -submx0; case/row_subPn=> i.
by exists (row i (kermx A)); rewrite -?submx0 // -row_mul mulmx_ker row0.
Qed.

Lemma mulmx0_rank_max : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m B = 0 -> \rank A + \rank B <= n.
Proof.
move=> m n p A B AB0; rewrite -{3}(subnK (rank_leq_row B)) leq_add2r.
rewrite -mxrank_ker mxrankS //; exact/sub_kermxP.
Qed.

Lemma mxrank_Frobenius : forall m n p q (A : 'M_(m, n)) B (C : 'M_(p, q)),
  \rank (A *m B) + \rank (B *m C) <= \rank B + \rank (A *m B *m C).
Proof.
move=> m n p q A B C; rewrite -{2}(mulmx_base (A *m B)) -mulmxA.
rewrite (eqmxMfull _ (col_base_full _)); set C2 := row_base _ *m C.
rewrite -{1}(subnK (rank_leq_row C2)) -(mxrank_ker C2) addnAC leq_add2r. 
rewrite addnC -{1}(mulmx_base B) -mulmxA eqmxMfull //.
set C1 := _ *m C; rewrite -{2}(subnKC (rank_leq_row C1)) leq_add2l -mxrank_ker.
rewrite -(mxrankMfree _ (row_base_free (A *m B))).
have: (row_base (A *m B) <= row_base B)%MS by rewrite !eq_row_base submxMl.
case/submxP=> D defD; rewrite defD mulmxA mxrankMfree ?mxrankS //.
by apply/sub_kermxP; rewrite -mulmxA (mulmxA D) -defD -/C2 mulmx_ker.
Qed.

Lemma mxrank_mul_min : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank A + \rank B - n <= \rank (A *m B).
Proof.
move=> m n p A B; have:= mxrank_Frobenius A 1%:M B.
by rewrite mulmx1 mul1mx mxrank1 leq_sub_add.
Qed.

Lemma addsmx_compl_full : forall m n (A : 'M_(m, n)), row_full (A + A^C)%MS.
Proof.
move=> m n A; rewrite /row_full addsmxE; apply/row_fullP.
exists (row_mx (pinvmx A) (cokermx A)); rewrite mul_row_col.
rewrite -{2}[A]mulmx_ebase -!mulmxA mulKmx // -mulmx_addr !mulmxA.
by rewrite pid_mx_id ?copid_mx_id // -mulmx_addl addrC subrK mul1mx mulVmx.
Qed.

Lemma sub_capmx_gen : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= capmx_gen B C)%MS = (A <= B)%MS && (A <= C)%MS.
Proof.
move=> m1 m2 m3 n A B C; apply/idP/andP=> [sAI | []].
  rewrite !(submx_trans sAI) ?submxMl // /capmx_gen.
   have:= mulmx_ker (col_mx B C); set K := kermx _.
   rewrite -{1}[K]hsubmxK mul_row_col; move/(canRL (addrK _))->.
   by rewrite add0r -mulNmx submxMl.
case/submxP=> B' ->{A}; case/submxP=> C' eqBC'.
have: submx (row_mx B' (- C')) (kermx (col_mx B C)).
  by apply/sub_kermxP; rewrite mul_row_col eqBC' mulNmx subrr.
case/submxP=> D; rewrite -[kermx _]hsubmxK mul_mx_row.
by case/eq_row_mx=> -> _; rewrite -mulmxA submxMl.
Qed.

Let capmx_witnessP : forall m n (A : 'M_(m, n)),
  equivmx A (qidmx A) (capmx_witness A).
Proof.
move=> m n A; rewrite /equivmx qidmx_eq1 /qidmx /capmx_witness.
rewrite -sub1mx; case s1A: (1%:M <= A)%MS => /=; last first.
  rewrite !genmxE submx_refl /= -negb_add; apply: contra {s1A}(negbT s1A).
  case: eqP => [<- _| _]; first by rewrite genmxE.
  by case: eqP A => //= -> A; move/eqP->; rewrite pid_mx_1.
case: (m =P n) => [-> | ne_mn] in A s1A *.
  by rewrite conform_mx_id submx_refl pid_mx_1 eqxx.
by rewrite nonconform_mx ?submx1 ?s1A ?eqxx //; case: eqP.
Qed.

Let capmx_normP: forall m n (A : 'M_(m, n)),
  equivmx_spec A (qidmx A) (capmx_norm A).
Proof.
move=> m n A; case/andP: (chooseP (capmx_witnessP A)).
by move/eqmxP=> defN; move/eqP.
Qed.

Let capmx_norm_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  qidmx A = qidmx B -> (A == B)%MS -> capmx_norm A = capmx_norm B.
Proof.
move=> m1 m2 n A B eqABid; move/eqmxP=> eqAB.
have{eqABid eqAB} eqAB: equivmx A (qidmx A) =1 equivmx B (qidmx B).
  by move=> C; rewrite /equivmx eqABid !eqAB.
rewrite {1}/capmx_norm (eq_choose eqAB).
by apply: choose_id; first rewrite -eqAB; exact: capmx_witnessP.
Qed.

Let capmx_nopP : forall m n (A : 'M_(m, n)),
  equivmx_spec A (qidmx A) (capmx_nop A).
Proof.
rewrite /capmx_nop => m n; case: (eqVneq m n) => [-> | ne_mn] A.
  by rewrite conform_mx_id.
rewrite nonconform_mx ?ne_mn //; exact: capmx_normP.
Qed.

Let sub_qidmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  qidmx B -> (A <= B)%MS.
Proof.
rewrite /qidmx => m1 m2 n A B idB; apply: {A}submx_trans (submx1 A) _.
case: eqP B idB => [-> | _] B; first by move/eqP->; rewrite pid_mx_1.
by rewrite sub1mx.
Qed.

Let qidmx_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  qidmx (A :&: B)%MS = qidmx A && qidmx B.
Proof.
move=> m1 m2 n A B; rewrite mxopE -sub1mx.
case idA: (qidmx A); case idB: (qidmx B); try by rewrite capmx_nopP.
case s1B: (_ <= B)%MS; first by rewrite capmx_normP.
apply/idP; move/(sub_qidmx 1%:M).
by rewrite capmx_normP sub_capmx_gen s1B andbF.
Qed.

Let capmx_eq_norm : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  qidmx A = qidmx B -> (A :&: B)%MS = capmx_norm (A :&: B)%MS.
Proof.
move=> m1 m2 n A B eqABid; rewrite mxopE -sub1mx {}eqABid.
have norm_id: forall m (C : 'M_(m, n)) (N := capmx_norm C), capmx_norm N = N.
  by move=> m C; apply: capmx_norm_eq; rewrite ?capmx_normP ?andbb.
case idB: (qidmx B); last by case: ifP; rewrite norm_id.
rewrite /capmx_nop; case: (eqVneq m2 n) => [-> | neqm2n] in B idB *.
  have idN := idB; rewrite -{1}capmx_normP !qidmx_eq1 in idN idB.
  by rewrite conform_mx_id (eqP idN) (eqP idB).
by rewrite nonconform_mx ?neqm2n ?norm_id.
Qed.

Lemma capmxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B :=: capmx_gen A B)%MS.
Proof.
move=> m1 m2 n A B; rewrite mxopE -sub1mx; apply/eqmxP.
have:= submx_refl (capmx_gen A B).
rewrite !sub_capmx_gen; case/andP=> sIA sIB.
case idA: (qidmx A); first by rewrite !capmx_nopP submx_refl sub_qidmx.
case idB: (qidmx B); first by rewrite !capmx_nopP submx_refl sub_qidmx.
case s1B: (1%:M <= B)%MS; rewrite !capmx_normP ?sub_capmx_gen sIA ?sIB //=.
by rewrite submx_refl (submx_trans (submx1 _)).
Qed.

Lemma capmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= A)%MS.
Proof. by move=> m1 m2 n A B; rewrite capmxE submxMl. Qed.

Lemma sub_capmx : forall m m1 m2 n,
    forall (A : 'M_(m, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (A <= B :&: C)%MS = (A <= B)%MS && (A <= C)%MS.
Proof. by move=> m m1 m2 n A B C; rewrite capmxE sub_capmx_gen. Qed.

Lemma capmxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B = B :&: A)%MS.
Proof.
move=> m1 m2 n A B; case: (eqVneq (qidmx A) (qidmx B)) => [eqAB|].
  rewrite (capmx_eq_norm eqAB) (capmx_eq_norm (esym eqAB)).
  apply: capmx_norm_eq; first by rewrite !qidmx_cap andbC.
  by apply/andP; split; rewrite !sub_capmx andbC -sub_capmx.
by rewrite negb_eqb !mxopE; move/addbP <-; case: (qidmx A).
Qed.

Lemma capmxSr : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= B)%MS.
Proof. by move=> m1 m2 n A B; rewrite capmxC capmxSl. Qed.

Lemma capmx_idPr : forall n m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B :=: B)%MS (B <= A)%MS.
Proof.
move=> n m1 m2 A B; have:= @eqmxP _ _ _ (A :&: B)%MS B.
by rewrite capmxSr sub_capmx submx_refl !andbT.
Qed.

Lemma capmx_idPl : forall n m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B :=: A)%MS (A <= B)%MS.
Proof. by move=> n m1 m2 A B; rewrite capmxC; exact: capmx_idPr. Qed.

Lemma capmxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> A :&: B <= C :&: D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD; rewrite sub_capmx.
by rewrite {1}capmxC !(submx_trans (capmxSr _ _)).
Qed.

Lemma cap_eqmx : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A :=: C -> B :=: D -> A :&: B :=: C :&: D)%MS.
Proof.
by move=> m1 m2 m3 m4 n A B C D sAC sBD; apply/eqmxP; rewrite !capmxS ?sAC ?sBD.
Qed.

Lemma capmxMr : forall m1 m2 n p,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  ((A :&: B) *m C <= A *m C :&: B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C; rewrite sub_capmx !submxMr ?capmxSl ?capmxSr.
Qed.

Lemma cap0mx : forall m1 m2 n (A : 'M_(m2, n)), ((0 : 'M_(m1, n)) :&: A)%MS = 0.
Proof. by move=> m1 m2 n A; exact: submx0null (capmxSl _ _). Qed.

Lemma capmx0 : forall m1 m2 n (A : 'M_(m1, n)), (A :&: (0 : 'M_(m2, n)))%MS = 0.
Proof. by move=> m1 m2 n A; exact: submx0null (capmxSr _ _). Qed.

Lemma capmxT : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full B -> (A :&: B :=: A)%MS.
Proof.
move=> m1 m2 n A B; rewrite -sub1mx => s1B; apply/eqmxP.
by rewrite capmxSl sub_capmx submx_refl (submx_trans (submx1 A)).
Qed.

Lemma capTmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full A -> (A :&: B :=: B)%MS.
Proof.
by move=> m1 m2 n A B Afull; apply/eqmxP; rewrite capmxC !capmxT ?andbb.
Qed.

Let capmx_nop_id : forall n (A : 'M_n), capmx_nop A = A.
Proof. by move=> n A; rewrite /capmx_nop conform_mx_id. Qed.

Lemma cap1mx : forall n (A : 'M_n), (1%:M :&: A = A)%MS.
Proof. by move=> n A; rewrite mxopE qidmx_eq1 eqxx capmx_nop_id. Qed.

Lemma capmx1 : forall n (A : 'M_n), (A :&: 1%:M = A)%MS.
Proof. by move=> n A; rewrite capmxC cap1mx. Qed.

Lemma genmx_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  <<A :&: B>>%MS = (<<A>> :&: <<B>>)%MS.
Proof.
move=> m1 m2 n A B; rewrite -(eq_genmx (cap_eqmx (genmxE A) (genmxE B))).
case idAB: (qidmx <<A>> || qidmx <<B>>)%MS.
  rewrite [@capmx _]mxopE !capmx_nop_id !(fun_if (@genmx _ _)) !genmx_id.
  by case: (qidmx _) idAB => //= ->.
case idA: (qidmx _) idAB => //= idB; rewrite {2}capmx_eq_norm ?idA //.
set C := (_ :&: _)%MS; have eq_idC: row_full C = qidmx C.
  rewrite qidmx_cap idA -sub1mx sub_capmx genmxE; apply/andP=> [[s1A]].
  by case/idP: idA; rewrite qidmx_eq1 -genmx1 (sameP eqP genmxP) submx1.
rewrite [@genmx _]mxopE /capmx_norm eq_idC.
by apply: choose_id (capmx_witnessP _); rewrite -eq_idC genmx_witnessP.
Qed.

Lemma capmxA : forall m1 m2 m3 n,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A :&: (B :&: C) = A :&: B :&: C)%MS.
Proof.
move=> m1 m2 m3 n A B C; rewrite (capmxC A B) capmxC.
wlog idA: m1 m3 A C / (qidmx A).
  move=> IH; case idA: (qidmx A); first exact: IH.
  case idC: (qidmx C); first by rewrite -IH.
  rewrite (@capmx_eq_norm n m3) ?qidmx_cap ?idA ?idC ?andbF //.
  rewrite capmx_eq_norm ?qidmx_cap ?idA ?idC ?andbF //.
  apply: capmx_norm_eq; first by rewrite !qidmx_cap andbAC.
  by apply/andP; split; rewrite !sub_capmx andbAC -!sub_capmx.
rewrite -!(capmxC A) ![@capmx m1]mxopE idA capmx_nop_id.
case: (eqVneq (qidmx B) (qidmx C)) => [eqBC |].
  rewrite (@capmx_eq_norm n) ?capmx_nopP // capmx_eq_norm //.
  by apply: capmx_norm_eq; rewrite ?qidmx_cap ?capmxS ?capmx_nopP.
by rewrite !mxopE capmx_nopP capmx_nop_id; do 2?case: (qidmx _) => //.
Qed.

Canonical Structure capmx_monoid n :=
  Monoid.Law (@capmxA n n n n) (@cap1mx n) (@capmx1 n).
Canonical Structure capmx_comoid n := Monoid.ComLaw (@capmxC n n n).

Lemma bigcapmx_inf : forall i0 P m n (A_ : I -> 'M_n) (B : 'M_(m, n)),
  P i0 -> (A_ i0 <= B -> \bigcap_(i | P i) A_ i <= B)%MS.
Proof.
move=> i0 P m n A_ B Pi0; apply: submx_trans.
by rewrite (bigD1 i0) // capmxSl.
Qed.

Lemma sub_bigcapmxP : forall P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  reflect (forall i, P i -> A <= B_ i)%MS (A <= \bigcap_(i | P i) B_ i)%MS.
Proof.
move=> P m n A B_; apply: (iffP idP) => [sAB i Pi | sAB].
  by apply: (submx_trans sAB); rewrite (bigcapmx_inf Pi).
by apply big_prop => // [|B C sAC]; rewrite ?submx1 // sub_capmx sAC.
Qed.

Lemma genmx_bigcap :  forall P n (A_ : I -> 'M_n),
  (<<\bigcap_(i | P i) A_ i>> = \bigcap_(i | P i) <<A_ i>>)%MS.
Proof. move=> P n; exact: (big_morph _ (@genmx_cap n n n) (@genmx1 n)). Qed.

Lemma matrix_modl : forall m1 m2 m3 n,
                    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= C -> A + (B :&: C) :=: (A + B) :&: C)%MS.
Proof.
move=> m1 m2 m3 n A B C sAC; set D := ((A + B) :&: C)%MS; apply/eqmxP.
rewrite sub_capmx addsmxS ?capmxSl // addsmx_sub sAC capmxSr /=.
have: (D <= B + A)%MS by rewrite addsmxC capmxSl.
case/sub_addsmxP=> u defD; rewrite defD addrC addmx_sub_adds ?submxMl //.
rewrite sub_capmx submxMl -[_ *m B](addrK (u.2 *m A)) -defD.
by rewrite addmx_sub ?capmxSr // eqmx_opp mulmx_sub.
Qed.

Lemma matrix_modr : forall m1 m2 m3 n,
                    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (C <= A -> (A :&: B) + C :=: A :&: (B + C))%MS.
Proof.
move=> m1 m2 m3 n A B C; rewrite !(capmxC A) -!(addsmxC C); exact: matrix_modl.
Qed.

Lemma capmx_compl : forall m n (A : 'M_(m, n)), (A :&: A^C)%MS = 0.
Proof.
move=> m n A; set D := (A :&: A^C)%MS; have: (D <= D)%MS by [].
rewrite sub_capmx andbC; case/andP; case/submxP=> B defB.
rewrite submxE; move/eqP; rewrite defB -!mulmxA mulKVmx ?copid_mx_id //.
by rewrite mulmxA => ->; rewrite mul0mx.
Qed.

Lemma mxrank_mul_ker : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  (\rank (A *m B) + \rank (A :&: kermx B))%N = \rank A.
Proof.
move=> m n p A B; apply/eqP; set K := kermx B; set C := (A :&: K)%MS.
rewrite -(eqmxMr B (eq_row_base A)); set K' := _ *m B.
rewrite -{2}(subnKC (rank_leq_row K')) -mxrank_ker eqn_addl.
rewrite -(mxrankMfree _ (row_base_free A)) mxrank_leqif_sup.
  rewrite sub_capmx -(eq_row_base A) submxMl. 
  by apply/sub_kermxP; rewrite -mulmxA mulmx_ker.
have: (C <= row_base A)%MS by rewrite eq_row_base capmxSl.
case/submxP=> C' defC; rewrite defC submxMr //; apply/sub_kermxP.
by rewrite mulmxA -defC; apply/sub_kermxP; rewrite capmxSr.
Qed.

Lemma mxrank_injP : forall m n p (A : 'M_(m, n)) (f : 'M_(n, p)),
  reflect (\rank (A *m f) = \rank A) ((A :&: kermx f)%MS == 0).
Proof.
move=> m n p A f; rewrite -mxrank_eq0 -(eqn_addl (\rank (A *m f))).
by rewrite mxrank_mul_ker addn0 eq_sym; exact: eqP.
Qed.

Lemma mxrank_disjoint_sum : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B)%MS = 0 -> \rank (A + B)%MS = (\rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B AB0; pose Ar := row_base A; pose Br := row_base B.
have [Afree Bfree]: row_free Ar /\ row_free Br by rewrite !row_base_free.
have: (Ar :&: Br <= A :&: B)%MS by rewrite capmxS ?eq_row_base.
rewrite {}AB0 submx0 -mxrank_eq0 capmxE mxrankMfree //.
set Cr := col_mx Ar Br; set Crl := lsubmx _; rewrite mxrank_eq0 => Crl0.
rewrite -(adds_eqmx (eq_row_base _) (eq_row_base _)) addsmxE -/Cr.
suffices K0: kermx Cr = 0.
  by apply/eqP; rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker K0 mxrank0.
move/eqP: (mulmx_ker Cr); rewrite -[kermx Cr]hsubmxK mul_row_col -/Crl.
rewrite (eqP Crl0) mul0mx add0r -mxrank_eq0 mxrankMfree // mxrank_eq0.
by move/eqP->; rewrite row_mx0.
Qed.

Lemma diffmxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B :=: A :&: (capmx_gen A B)^C)%MS.
Proof.
move=> m1 m2 n A B; rewrite mxopE; apply/eqmxP.
by rewrite !genmxE !capmxE andbb.
Qed.

Lemma genmx_diff : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (<<A :\: B>> = A :\: B)%MS.
Proof. by move=> m1 m2 n A B; rewrite [@diffmx _]mxopE genmx_id. Qed.
 
Lemma diffmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B <= A)%MS.
Proof. by move=> m1 m2 n A B; rewrite diffmxE capmxSl. Qed.

Lemma capmx_diff : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :\: B) :&: B)%MS = 0.
Proof.
move=> m1 m2 n A B; apply/eqP; pose C := capmx_gen A B.
rewrite -submx0 -(capmx_compl C) sub_capmx -capmxE sub_capmx andbAC.
by rewrite -sub_capmx -diffmxE -sub_capmx.
Qed.

Lemma addsmx_diff_cap_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B + A :&: B :=: A)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite addsmx_sub capmxSl diffmxSl /=.
set C := (A :\: B)%MS; set D := capmx_gen A B.
suffices sACD: (A <= C + D)%MS.
  by rewrite (submx_trans sACD) ?addsmxS ?capmxE.
have:= addsmx_compl_full D; rewrite /row_full addsmxE.
case/row_fullP=> U; move/(congr1 (mulmx A)); rewrite mulmx1.
rewrite -[U]hsubmxK mul_row_col mulmx_addr addrC 2!mulmxA.
set V := _ *m _ => defA; rewrite -defA; move/(canRL (addrK _)): defA => defV.
have: (V <= C)%MS.
  rewrite diffmxE sub_capmx {1}defV -mulNmx addmx_sub 1?mulmx_sub //.
  by rewrite -capmxE capmxSl.
by case/submxP=> W ->; rewrite -mul_row_col addsmxE submxMl.
Qed.

Lemma mxrank_cap_compl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A :&: B) + \rank (A :\: B))%N = \rank A.
Proof.
move=> m1 m2 n A B; rewrite addnC -mxrank_disjoint_sum ?addsmx_diff_cap_eq //.
by rewrite (capmxC A) capmxA capmx_diff cap0mx.
Qed.

Lemma mxrank_sum_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A + B) + \rank (A :&: B) = \rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B; set C := (A :&: B)%MS; set D := (A :\: B)%MS.
have rDB: \rank (A + B)%MS = \rank (D + B)%MS.
  apply/eqP; rewrite mxrank_leqif_sup; first by rewrite addsmxS ?diffmxSl.
  by rewrite addsmx_sub addsmxSr -(addsmx_diff_cap_eq A B) addsmxS ?capmxSr.
rewrite {1}rDB mxrank_disjoint_sum ?capmx_diff //.
by rewrite addnC addnA mxrank_cap_compl.
Qed.

Lemma mxrank_adds_leqif : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  \rank (A + B) <= \rank A + \rank B ?= iff (A :&: B <= (0 : 'M_n))%MS.
Proof.
move=> m1 m2 n A B; rewrite -mxrank_sum_cap; split; first exact: leq_addr.
by rewrite addnC (@eqn_addr _ 0) eq_sym mxrank_eq0 -submx0.
Qed.

(* Subspace projection matrix *)

Lemma proj_mx_sub : forall m n U V (W : 'M_(m, n)), (W *m proj_mx U V <= U)%MS.
Proof. by move=> m n U V W; rewrite !mulmx_sub // -addsmxE addsmx0. Qed.

Lemma proj_mx_compl_sub : forall m n U V (W : 'M_(m, n)),
  (W <= U + V -> W - W *m proj_mx U V <= V)%MS.
Proof.
move=> m n U V W; rewrite addsmxE => sWUV.
rewrite mulmxA -{1}(mulmxKpV sWUV) -mulmx_subr mulmx_sub //.
by rewrite opp_col_mx add_col_mx subrr subr0 -addsmxE adds0mx.
Qed.

Lemma proj_mx_id : forall m n U V (W : 'M_(m, n)),
  (U :&: V = 0)%MS -> (W <= U)%MS -> W *m proj_mx U V = W.
Proof.
move=> m n U V W dxUV sWU; apply/eqP; rewrite -subr_eq0 -submx0 -dxUV.
rewrite sub_capmx addmx_sub ?eqmx_opp ?proj_mx_sub //= -eqmx_opp oppr_sub.
by rewrite proj_mx_compl_sub // (submx_trans sWU) ?addsmxSl.
Qed. 

Lemma proj_mx_0 : forall m n U V (W : 'M_(m, n)),
  (U :&: V = 0)%MS -> (W <= V)%MS -> W *m proj_mx U V = 0.
Proof.
move=> m n U V W dxUV sWV; apply/eqP; rewrite -submx0 -dxUV.
rewrite sub_capmx proj_mx_sub /= -[_ *m _](subrK W) addmx_sub // -eqmx_opp.
by rewrite oppr_sub proj_mx_compl_sub // (submx_trans sWV) ?addsmxSr.
Qed.

Lemma add_proj_mx : forall m n U V (W : 'M_(m, n)),
    (U :&: V = 0)%MS -> (W <= U + V)%MS ->
  W *m proj_mx U V + W *m proj_mx V U = W.
Proof.
move=> m n U V W dxUV sWUV; apply/eqP; rewrite -subr_eq0 -submx0 -dxUV.
rewrite -addrA sub_capmx {2}addrCA -!(oppr_sub W).
(* 2min: *) 
(* rewrite !{1}addmx_sub ?proj_mx_sub ?eqmx_opp ?proj_mx_compl_sub //. *)
(* 1s:   *)
apply/andP; split; (apply: addmx_sub; 
  [exact: proj_mx_sub | rewrite eqmx_opp; apply proj_mx_compl_sub=> //]).
by rewrite addsmxC.
Qed.

Lemma proj_mx_proj : forall n (U V : 'M_n),
  (U :&: V = 0)%MS -> let P := proj_mx U V in P *m P = P.
Proof.
by move=> n U V dxUV P; rewrite -{-2}[P]mul1mx proj_mx_id ?proj_mx_sub.
Qed.

(* Completing a partially injective matrix to get a unit matrix. *)

Lemma complete_unitmx : forall m n (U : 'M_(m, n)) (f : 'M_n),
  \rank (U *m f) = \rank U -> {g : 'M_n | g \in unitmx & U *m f = U *m g}.
Proof.
move=> m n U f injfU; pose V := <<U>>%MS; pose W := V *m f.
pose g := proj_mx V (V^C)%MS *m f + cokermx V *m row_ebase W.
have defW: V *m g = W.
  rewrite mulmx_addr mulmxA proj_mx_id ?genmxE ?capmx_compl //.
  by rewrite mulmxA mulmx_coker mul0mx addr0.
exists g; last first.
  have: (U <= V)%MS by rewrite genmxE.
  by case/submxP=> u ->; rewrite -!mulmxA defW.
rewrite -row_full_unit -sub1mx; apply/submxP.
have: (invmx (col_ebase W) *m W <= V *m g)%MS by rewrite defW submxMl.
case/submxP=> v def_v; exists (invmx (row_ebase W) *m (v *m V + (V^C)%MS)).
rewrite -mulmxA mulmx_addl -mulmxA -def_v -{3}[W]mulmx_ebase -mulmxA.
rewrite mulKmx ?col_ebase_unit // [_ *m g]mulmx_addr mulmxA.
rewrite (proj_mx_0 (capmx_compl _)) // mul0mx add0r 2!mulmxA.
rewrite mulmxK ?row_ebase_unit // copid_mx_id ?rank_leq_row //.
rewrite (eqmxMr _ (genmxE U)) injfU genmxE addrC -mulmx_addl subrK.
by rewrite mul1mx mulVmx ?row_ebase_unit.
Qed.

(* Mapping between two subspaces with the same dimension. *)

Lemma eq_rank_unitmx : forall m1 m2 n (U : 'M_(m1, n)) (V : 'M_(m2, n)),
  \rank U = \rank V -> {f : 'M_n | f \in unitmx & V :=: U *m f}%MS.
Proof.
move=> m1 m2 n U V eqrUV.
pose f := invmx (row_ebase <<U>>%MS) *m row_ebase <<V>>%MS.
have defUf: (<<U>> *m f :=: <<V>>)%MS.
  rewrite -[<<U>>%MS]mulmx_ebase mulmxA mulmxK ?row_ebase_unit // -mulmxA.
  rewrite genmxE eqrUV -genmxE -{3}[<<V>>%MS]mulmx_ebase -mulmxA.
  move: (pid_mx _ *m _) => W; apply/eqmxP.
  by rewrite !eqmxMfull ?andbb // row_full_unit col_ebase_unit.
have{defUf} defV: (V :=: U *m f)%MS.
  by apply/eqmxP; rewrite -!(eqmxMr f (genmxE U)) !defUf !genmxE andbb.
have injfU: \rank (U *m f) = \rank U by rewrite -defV eqrUV.
by have [g injg defUg] := complete_unitmx injfU; exists g; rewrite -?defUg.
Qed.

Section SumExpr.

(* This is the infrastructure to support the mxdirect predicate. We use a     *)
(* bespoke canonical structure to decompose a matrix expression into binary   *)
(* and n-ary products, using some of the "quote" technology. This lets us     *)
(* characterize direct sums as set sums whose rank is equal to the sum of the *)
(* ranks of the individual terms. The mxsum_expr/proper_mxsum_expr structures *)
(* below supply both the decomposition and the calculation of the rank sum.   *)
(* The mxsum_spec dependent predicate family expresses the consistency of     *)
(* these two decompositions.                                                  *)
(*   The main technical difficulty we need to overcome is the fact that       *)
(* the "catch-all" case of canonical structures has a priority lower than     *)
(* constant expansion. However, it is undesireable that local abbreviations   *)
(* be opaque for the direct-sum predicate, e.g., not be able to handle        *)
(* let S := (\sum_(i | P i) LargeExpression i)%MS in mxdirect S -> ...).      *)
(*   As in "quote", we use the interleaving of constant expansion and         *)
(* canonical projection matching to achieve our goal: we use a "wrapper" type *)
(* (indeed, the wrapped T type defined in ssrfun.v) with a self-inserting     *)
(* non-primitive constructor to gain finer control over the type and          *)
(* structure inference process. The innermost, primitive, constructor flags   *)
(* trivial sums; it is initially hidden by an eta-expansion, which has been   *)
(* made into a (default) canonical structure -- this lets type inference      *)
(* automatically insert this outer tag.                                       *)
(*   In detail, we define three types                                         *)
(*  mxsum_spec S r <-> There exists a finite list of matrices A1, ..., Ak     *)
(*                     such that S is the set sum of the Ai, and r is the sum *)
(*                     of the ranks of the Ai, i.e., S = (A1 + ... + Ak)%MS   *)
(*                     and r = \rank A1 + ... + \rank Ak. Note that           *)
(*                     mxsum_spec is a recursive dependent predicate family   *)
(*                     whose elimination rewrites simultaneaously S, r and    *)
(*                     the height of S.                                       *)
(*   proper_mxsum_expr n == The interface for proper sum expressions; this is *)
(*                     a double-entry interface, keyed on both the matrix sum *)
(*                     value and the rank sum. The matrix value is restricted *)
(*                     to square matrices, as the "+"%MS operator always      *)
(*                     returns a square matrix. This interface has two        *)
(*                     canonical insances, for binary and n-ary sums.         *)
(*   mxsum_expr m n == The interface for general sum expressions, comprising  *)
(*                     both proper sums and trivial sums consisting of a      *)
(*                     single matrix. The key values are WRAPPED as this lets *)
(*                     us give priority to the "proper sum" interpretation    *)
(*                     (see below). To allow for trivial sums, the matrix key *)
(*                     can have any dimension. The mxsum_expr interface has   *)
(*                     two canonical instances, for trivial and proper sums,  *)
(*                     keyed to the Wrap and wrap constructors, respectively. *)
(* The projections for the two interfaces above are                           *)
(*   proper_mxsum_val, mxsum_val : these are respectively coercions to 'M_n   *)
(*                     and wrapped 'M_(m, n); thus, the matrix sum for an     *)
(*                     S : mxsum_expr m n can be written unwrap S.            *)
(*   proper_mxsum_rank, mxsum_rank : projections to the nat and wrapped nat,  *)
(*                     respectively; the rank sum for S : mxsum_expr m n is   *)
(*                     thus written unwrap (mxsum_rank S).                    *)
(* The mxdirect A predicate actually gets A in a phantom argument, which is   *)
(* used to infer an (implicit) S : mxsum_expr such that unwrap S = A; the     *)
(* actual definition is \rank (unwrap S) == unwrap (mxsum_rank S).            *)
(*   Note that the inference of S is inherently ambiguous: ANY matrix can be  *)
(* viewed as a trivial sum, including one whose description is manifestly a   *)
(* proper sum. We use the wrapped type and the interaction between delta      *)
(* reduction and canonical structure inference to resolve this ambiguity in   *)
(* favor of proper sums, as follows:                                          *)
(*    - The phantom type sets up a unification problem of the form            *)
(*         unwrap (mxsum_val ?S) = A                                          *)
(*      with unknown evar ?S : mxsum_expr m n.                                *)
(*    - As the constructor wrap is also a default Canonical Structure for the *)
(*      wrapped type, so A is immediately replaced with unwrap (wrap A) and   *)
(*      we get the residual unification problem                               *)
(*         mxsum_val ?S = wrap A                                              *)
(*    - Now Coq tries to apply the proper sum Canonical Structure, which has  *)
(*      key projection wrap (proper_mxsum_val ?PS) where ?PS is a fresh evar  *)
(*      (of type proper_mxsum_expr n). This can only succeed if m = n, and if *)
(*      a solution can be found to the recursive unification problem          *)
(*         proper_mxsum_val ?PS = A                                           *)
(*      This causes Coq to look for one of the two canonical constants for    *)
(*      proper_mxsum_val (addsmx or bigop) at the head of A, delta-expanding  *)
(*      A as needed, and then inferring recursively mxsum_expr structures for *)
(*      the last argument(s) of that constant.                                *)
(*    - If the above step fails then the wrap constant is expanded, revealing *)
(*      the primitive Wrap constructor; the unification problem now becomes   *)
(*         mxsum_val ?S = Wrap A                                              *)
(*      which fits perfectly the trivial sum canonical structure, whose key   *)
(*      projection is Wrap ?B where ?B is a fresh evar. Thus the inference    *)
(*      succeeds, and returns the trivial sum.                                *)
(* Note that the rank projections also register canonical values, so that the *)
(* same process can be used to infer a sum structure from the rank sum. In    *)
(* that case, however, there is no ambiguity and the inference can fail,      *)
(* because the rank sum for a trivial sum is not an arbitrary integer -- it   *)
(* must be of the form \rank ?B. It is nevertheless necessary to use the      *)
(* wrapped nat type for the rank sums, because in the non-trivial case the    *)
(* head constant of the nat expression is determined by the proper_mxsum_expr *)
(* canonical structure, so the mxsum_expr structure must use a generic        *)
(* constant, namely wrap.                                                     *)

Inductive mxsum_spec n : forall m, 'M[F]_(m, n) -> nat -> Prop :=
 | TrivialMxsum m A
    : @mxsum_spec n m A (\rank A)
 | ProperMxsum m1 m2 T1 T2 r1 r2 of
      @mxsum_spec n m1 T1 r1 & @mxsum_spec n m2 T2 r2
    : mxsum_spec (T1 + T2)%MS (r1 + r2)%N.
Arguments Scope mxsum_spec [nat_scope nat_scope matrix_set_scope nat_scope].

Structure mxsum_expr m n := Mxsum {
  mxsum_val :> wrapped 'M_(m, n);
  mxsum_rank : wrapped nat;
  _ : mxsum_spec (unwrap mxsum_val) (unwrap mxsum_rank)
}.

Canonical Structure trivial_mxsum m n A :=
  @Mxsum m n (Wrap A) (Wrap (\rank A)) (TrivialMxsum A).

Structure proper_mxsum_expr n := ProperMxsumExpr {
  proper_mxsum_val :> 'M_n;
  proper_mxsum_rank : nat;
  _ : mxsum_spec proper_mxsum_val proper_mxsum_rank
}.

Definition proper_mxsumP n (S : proper_mxsum_expr n) :=
  let: ProperMxsumExpr _ _ termS := S return mxsum_spec S (proper_mxsum_rank S)
  in termS.

Canonical Structure sum_mxsum n (S : proper_mxsum_expr n) :=
  @Mxsum n n (wrap (S : 'M_n)) (wrap (proper_mxsum_rank S)) (proper_mxsumP S).

Section Binary.
Variable (m1 m2 n : nat) (S1 : mxsum_expr m1 n) (S2 : mxsum_expr m2 n).
Fact binary_mxsum_proof :
  mxsum_spec (unwrap S1 + unwrap S2)
             (unwrap (mxsum_rank S1) + unwrap (mxsum_rank S2)).
Proof. by case: S1 S2 => [A1 r1 A1P] [A2 r2 A2P]; right. Qed.
Canonical Structure binary_mxsum_expr := ProperMxsumExpr binary_mxsum_proof.
End Binary.

Section Nary.
Variables (P : pred I) (n : nat) (S_ : I -> mxsum_expr n n).
Fact nary_mxsum_proof :
  mxsum_spec (\sum_(i | P i) unwrap (S_ i))
             (\sum_(i | P i) unwrap (mxsum_rank (S_ i))).
Proof.
rewrite -!(big_filter _ P) !unlock.
elim: filter => /= [|i e IHe]; first by rewrite -(mxrank0 n n); left.
by right=> //; case: (S_ i) => A r; exact.
Qed.
Canonical Structure nary_mxsum_expr := ProperMxsumExpr nary_mxsum_proof.
End Nary.

Definition mxdirect_def m n T of phantom 'M_(m, n) (unwrap (mxsum_val T)) :=
  \rank (unwrap T) == unwrap (mxsum_rank T).

End SumExpr.

Notation mxdirect A := (mxdirect_def (Phantom 'M_(_,_) A%MS)).

Lemma mxdirectP : forall n (S : proper_mxsum_expr n),
  reflect (\rank S = proper_mxsum_rank S) (mxdirect S).
Proof. move=> n S; exact: eqnP. Qed.
Implicit Arguments mxdirectP [n S].

Lemma mxdirect_trivial : forall m n A,
  mxdirect (unwrap (@trivial_mxsum m n A)).
Proof. move=> m n A; exact: eqxx. Qed.

Lemma mxrank_sum_leqif : forall m n (S : mxsum_expr m n),
  \rank (unwrap S) <= unwrap (mxsum_rank S) ?= iff mxdirect (unwrap S).
Proof.
rewrite /mxdirect_def => m n [[A] [r] /= defAr]; split=> //=.
elim: m A r / defAr => // m1 m2 A1 A2 r1 r2 _ leAr1 _ leAr2.
by apply: leq_trans (leq_add leAr1 leAr2); rewrite mxrank_adds_leqif.
Qed.

Lemma mxdirectE : forall m n (S : mxsum_expr m n),
  mxdirect (unwrap S) = (\rank (unwrap S) == unwrap (mxsum_rank S)).
Proof. by []. Qed.

Lemma mxdirectEgeq : forall m n (S : mxsum_expr m n),
  mxdirect (unwrap S) = (\rank (unwrap S) >= unwrap (mxsum_rank S)).
Proof. by move=> m n S; rewrite (geq_leqif (mxrank_sum_leqif S)). Qed.

Section BinaryDirect.

Variables m1 m2 n : nat.

Lemma mxdirect_addsE : forall (S1 : mxsum_expr m1 n) (S2 : mxsum_expr m2 n),
   mxdirect (unwrap S1 + unwrap S2)
    = [&& mxdirect (unwrap S1), mxdirect (unwrap S2)
        & unwrap S1 :&: unwrap S2 == 0]%MS.
Proof.
move=> S1 S2; rewrite (@mxdirectE n) /=.
have:= leqif_add (mxrank_sum_leqif S1) (mxrank_sum_leqif S2).
move/(leqif_trans (mxrank_adds_leqif (unwrap S1) (unwrap S2)))=> ->.
by rewrite andbC -andbA submx0.
Qed.

Lemma mxdirect_addsP : forall (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B = 0)%MS (mxdirect (A + B)).
Proof. move=> A B; rewrite mxdirect_addsE !mxdirect_trivial; exact: eqP. Qed.

End BinaryDirect.

Section NaryDirect.

Variables (P : pred I) (n : nat).

Let TIsum A_ i := (A_ i :&: (\sum_(j | P j && (j != i)) A_ j) = 0 :> 'M_n)%MS.

Let mxdirect_sums_recP : forall S_ : I -> mxsum_expr n n,
  reflect (forall i, P i -> mxdirect (unwrap (S_ i)) /\ TIsum (unwrap \o S_) i)
          (mxdirect (\sum_(i | P i) (unwrap (S_ i)))).
Proof.
rewrite /TIsum => S_; apply: (iffP eqnP) => /= [dxS i Pi | dxS].
  set Si' := (\sum_(j | _) unwrap (S_ j))%MS.
  suffices: mxdirect (unwrap (S_ i) + Si').
    by rewrite mxdirect_addsE; case/and3P=> -> _; move/eqP.
  by apply/eqnP; rewrite /= -!(bigD1 i).
elim: _.+1 {-2 4}P (subxx P) (ltnSn #|P|) => // m IHm Q; move/subsetP=> sQP.
case: (pickP Q) => [i Qi | Q0]; last by rewrite !big_pred0 ?mxrank0.
rewrite (cardD1x Qi) !((bigD1 i) Q) //=.
move/IHm=> <- {IHm}/=; last by apply/subsetP=> j; case/andP; move/sQP.
case: (dxS i (sQP i Qi)); move/eqnP=> <- TiQ_0; rewrite mxrank_disjoint_sum //.
apply/eqP; rewrite -submx0 -{2}TiQ_0 capmxS //=; apply/sumsmx_subP=> j /=.
by case/andP=> Qj i'j; rewrite (sumsmx_sup j) ?[P j]sQP.
Qed.

Lemma mxdirect_sumsP : forall A_ : I -> 'M_n,
  reflect (forall i, P i -> A_ i :&: (\sum_(j | P j && (j != i)) A_ j) = 0)%MS
          (mxdirect (\sum_(i | P i) A_ i)).
Proof.
move=> A_; apply: (iffP (mxdirect_sums_recP _)) => dxA i; case/dxA=> //.
by rewrite mxdirect_trivial.
Qed.

Lemma mxdirect_sumsE : forall (S_ : I -> mxsum_expr n n) (xunwrap := unwrap),
  reflect (and (forall i, P i -> mxdirect (unwrap (S_ i)))
               (mxdirect (\sum_(i | P i) (xunwrap (S_ i)))))
          (mxdirect (\sum_(i | P i) (unwrap (S_ i)))).
Proof.
move=> S_; apply: (iffP (mxdirect_sums_recP _)) => [dxS | [dxS_ dxS] i Pi].
  by do [split; last apply/mxdirect_sumsP] => i; case/dxS.
by split; [exact: dxS_ | exact: mxdirect_sumsP Pi].
Qed.

End NaryDirect.

Section SubDaddsmx.

Variables m m1 m2 n : nat.
Variables (A : 'M[F]_(m, n)) (B1 : 'M[F]_(m1, n)) (B2 : 'M[F]_(m2, n)).

CoInductive sub_daddsmx_spec : Prop :=
  SubDaddsmxSpec A1 A2 of (A1 <= B1)%MS & (A2 <= B2)%MS & A = A1 + A2
                        & forall C1 C2, (C1 <= B1)%MS -> (C2 <= B2)%MS ->
                          A = C1 + C2 -> C1 = A1 /\ C2 = A2.

Lemma sub_daddsmx : (B1 :&: B2 = 0)%MS -> (A <= B1 + B2)%MS -> sub_daddsmx_spec.
Proof.
move=> dxB; case/sub_addsmxP=> u defA.
exists (u.1 *m B1) (u.2 *m B2); rewrite ?submxMl // => C1 C2 sCB1 sCB2.
move/(canLR (addrK _)) => defC1.
suffices: (C2 - u.2 *m B2 <= B1 :&: B2)%MS.
  by rewrite dxB submx0 subr_eq0 -defC1 defA; move/eqP->; rewrite addrK.
rewrite sub_capmx -oppr_sub -{1}(canLR (addKr _) defA) -addrA defC1.
by rewrite !(eqmx_opp, addmx_sub) ?submxMl.
Qed.

End SubDaddsmx.

Section SubDsumsmx.

Variables (P : pred I) (m n : nat) (A : 'M[F]_(m, n)) (B : I -> 'M[F]_n).

CoInductive sub_dsumsmx_spec : Prop :=
  SubDsumsmxSpec A_ of forall i, P i -> (A_ i <= B i)%MS
                        & A = \sum_(i | P i) A_ i
                        & forall C, (forall i, P i -> C i <= B i)%MS ->
                          A = \sum_(i | P i) C i -> {in SimplPred P, C =1 A_}.

Lemma sub_dsumsmx :
    mxdirect (\sum_(i | P i) B i) -> (A <= \sum_(i | P i) B i)%MS ->
  sub_dsumsmx_spec.
Proof.
move/mxdirect_sumsP=> dxB; case/sub_sumsmxP=> u defA.
pose A_ i := u i *m B i.
exists A_ => //= [i _ | C sCB defAC i Pi]; first exact: submxMl.
apply/eqP; rewrite -subr_eq0 -submx0 -{dxB}(dxB i Pi) /=.
rewrite sub_capmx addmx_sub ?eqmx_opp ?submxMl ?sCB //=.
rewrite -(subrK A (C i)) -addrA -oppr_sub addmx_sub ?eqmx_opp //.
  rewrite addrC defAC (bigD1 i) // addKr /= summx_sub // => j Pi'j.
  by rewrite (sumsmx_sup j) ?sCB //; case/andP: Pi'j.
rewrite addrC defA (bigD1 i) // addKr /= summx_sub // => j Pi'j.
by rewrite (sumsmx_sup j) ?submxMl.
Qed.

End SubDsumsmx.

Section Eigenspace.

Variables (n : nat) (g : 'M_n).

Definition eigenspace a := kermx (g - a%:M).
Definition eigenvalue : pred F := fun a => eigenspace a != 0.

Lemma eigenspaceP : forall a m (W : 'M_(m, n)),
  reflect (W *m g = a *: W) (W <= eigenspace a)%MS.
Proof.
move=> a m W; rewrite (sameP (sub_kermxP _ _) eqP).
by rewrite mulmx_subr subr_eq0 mul_mx_scalar; exact: eqP.
Qed.

Lemma eigenvalueP : forall a,
  reflect (exists2 v : 'rV_n, v *m g = a *: v & v != 0) (eigenvalue a).
Proof.
by move=> a; apply: (iffP (rowV0Pn _)) => [] [v]; move/eigenspaceP; exists v.
Qed.

Lemma mxdirect_sum_eigenspace : forall (P : pred I) a_,
  {in P &, injective a_} -> mxdirect (\sum_(i | P i) eigenspace (a_ i)).
Proof.
move=> P a_; elim: {P}_.+1 {-2}P (ltnSn #|P|) => // m IHm P lePm inj_a.
apply/mxdirect_sumsP=> i Pi; apply/eqP; apply/rowV0P => v.
rewrite sub_capmx; case/andP; case/eigenspaceP=> def_vg.
set Vi' := (\sum_(i | _) _)%MS => Vi'v.
have dxVi': mxdirect Vi'.
  rewrite (cardD1x Pi) in lePm; apply: IHm => //.
  by apply: sub_in2 inj_a => j; case/andP.
case/sub_dsumsmx: Vi'v => // u Vi'u def_v _.
rewrite def_v big1 // => j Pi'j; apply/eqP.
have nz_aij: a_ i - a_ j != 0.
  by case/andP: Pi'j => Pj ne_ji; rewrite subr_eq0 eq_sym (inj_in_eq inj_a).
case: (sub_dsumsmx dxVi' (sub0mx 1 _)) => C _ _ uniqC.
rewrite -(eqmx_eq0 (eqmx_scale _ nz_aij)).
rewrite (uniqC (fun k => (a_ i - a_ k) *: u k)) => // [|k Pi'k|].
- by rewrite -(uniqC (fun _ => 0)) ?big1 // => k Pi'k; exact: sub0mx.
- by rewrite scalemx_sub ?Vi'u.
rewrite -{1}(subrr (v *m g)) {1}def_vg def_v scaler_sumr mulmx_suml -sumr_sub.
by apply: eq_bigr => k; move/Vi'u; move/eigenspaceP->; rewrite scaler_subl.
Qed.

End Eigenspace.

End RowSpaceTheory.

Hint Resolve submx_refl.
Implicit Arguments submxP [F m1 m2 n A B].
Implicit Arguments eq_row_sub [F m n v A].
Implicit Arguments row_subP [F m1 m2 n A B].
Implicit Arguments rV_subP [F m1 m2 n A B].
Implicit Arguments row_subPn [F m1 m2 n A B].
Implicit Arguments sub_rVP [F n u v].
Implicit Arguments rV_eqP [F m1 m2 n A B].
Implicit Arguments rowV0Pn [F m n A].
Implicit Arguments rowV0P [F m n A].
Implicit Arguments eqmx0P [F m n A].
Implicit Arguments row_fullP [F m n A].
Implicit Arguments row_freeP [F m n A].
Implicit Arguments eqmxP [F m1 m2 n A B].
Implicit Arguments genmxP [F m1 m2 n A B].
Implicit Arguments addsmx_idPr [F m1 m2 n A B].
Implicit Arguments addsmx_idPl [F m1 m2 n A B].
Implicit Arguments sub_addsmxP [F m1 m2 m3 n A B C].
Implicit Arguments sumsmx_sup [F I P m n A B_].
Implicit Arguments sumsmx_subP [F I P m n A_ B].
Implicit Arguments sub_sumsmxP [F I P m n A B_].
Implicit Arguments sub_kermxP [F p m n A B].
Implicit Arguments det0P [F n A].
Implicit Arguments capmx_idPr [F m1 m2 n A B].
Implicit Arguments capmx_idPl [F m1 m2 n A B].
Implicit Arguments bigcapmx_inf [F I P m n A_ B].
Implicit Arguments sub_bigcapmxP [F I P m n A B_].
Implicit Arguments mxrank_injP [F m n A f].
Implicit Arguments mxdirectP [F n S].
Implicit Arguments mxdirect_addsP [F m1 m2 n A B].
Implicit Arguments mxdirect_sumsP [F I P n A_].
Implicit Arguments mxdirect_sumsE [F I P n S_].
Implicit Arguments eigenspaceP [F n g a m W].
Implicit Arguments eigenvalueP [F n g a].

Arguments Scope mxrank [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope complmx [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope row_full [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope submx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope ltmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope eqmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope addsmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope capmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope diffmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits mxrank genmx complmx submx ltmx addsmx capmx.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "<< A >>" := (genmx A) : matrix_set_scope.
Notation "A ^C" := (complmx A) : matrix_set_scope.
Notation "A <= B" := (submx A B) : matrix_set_scope.
Notation "A < B" := (ltmx A B) : matrix_set_scope.
Notation "A <= B <= C" := ((submx A B) && (submx B C)) : matrix_set_scope.
Notation "A < B <= C" := (ltmx A B && submx B C) : matrix_set_scope.
Notation "A <= B < C" := (submx A B && ltmx B C) : matrix_set_scope.
Notation "A < B < C" := (ltmx A B && ltmx B C) : matrix_set_scope.
Notation "A == B" := ((submx A B) && (submx B A)) : matrix_set_scope.
Notation "A :=: B" := (eqmx A B) : matrix_set_scope.
Notation "A + B" := (addsmx A B) : matrix_set_scope.
Notation "A :&: B" := (capmx A B) : matrix_set_scope.
Notation "A :\: B" := (diffmx A B) : matrix_set_scope.
Notation mxdirect S := (mxdirect_def (Phantom 'M_(_,_) S%MS)).

Notation "\sum_ ( <- r | P ) B" :=
  (\big[addsmx/0%R]_(<- r | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i <- r | P ) B" :=
  (\big[addsmx/0%R]_(i <- r | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i <- r ) B" :=
  (\big[addsmx/0%R]_(i <- r) B%MS) : matrix_set_scope.
Notation "\sum_ ( m <= i < n | P ) B" :=
  (\big[addsmx/0%R]_(m <= i < n | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( m <= i < n ) B" :=
  (\big[addsmx/0%R]_(m <= i < n) B%MS) : matrix_set_scope.
Notation "\sum_ ( i | P ) B" :=
  (\big[addsmx/0%R]_(i | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ i B" :=
  (\big[addsmx/0%R]_i B%MS) : matrix_set_scope.
Notation "\sum_ ( i : t | P ) B" :=
  (\big[addsmx/0%R]_(i : t | P%B) B%MS) (only parsing) : matrix_set_scope.
Notation "\sum_ ( i : t ) B" :=
  (\big[addsmx/0%R]_(i : t) B%MS) (only parsing) : matrix_set_scope.
Notation "\sum_ ( i < n | P ) B" :=
  (\big[addsmx/0%R]_(i < n | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i < n ) B" :=
  (\big[addsmx/0%R]_(i < n) B%MS) : matrix_set_scope.
Notation "\sum_ ( i \in A | P ) B" :=
  (\big[addsmx/0%R]_(i \in A | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i \in A ) B" :=
  (\big[addsmx/0%R]_(i \in A) B%MS) : matrix_set_scope.

Notation "\bigcap_ ( <- r | P ) B" :=
  (\big[capmx/1%:M]_(<- r | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i <- r | P ) B" :=
  (\big[capmx/1%:M]_(i <- r | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i <- r ) B" :=
  (\big[capmx/1%:M]_(i <- r) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( m <= i < n | P ) B" :=
  (\big[capmx/1%:M]_(m <= i < n | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( m <= i < n ) B" :=
  (\big[capmx/1%:M]_(m <= i < n) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i | P ) B" :=
  (\big[capmx/1%:M]_(i | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ i B" :=
  (\big[capmx/1%:M]_i B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i : t | P ) B" :=
  (\big[capmx/1%:M]_(i : t | P%B) B%MS) (only parsing) : matrix_set_scope.
Notation "\bigcap_ ( i : t ) B" :=
  (\big[capmx/1%:M]_(i : t) B%MS) (only parsing) : matrix_set_scope.
Notation "\bigcap_ ( i < n | P ) B" :=
  (\big[capmx/1%:M]_(i < n | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i < n ) B" :=
  (\big[capmx/1%:M]_(i < n) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i \in A | P ) B" :=
  (\big[capmx/1%:M]_(i \in A | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i \in A ) B" :=
  (\big[capmx/1%:M]_(i \in A) B%MS) : matrix_set_scope.

Section CardGL.

Variable F : finFieldType.

Lemma card_GL : forall n, n > 0 ->
  #|'GL_n[F]| = (#|F| ^ 'C(n, 2) * \prod_(1 <= i < n.+1) (#|F| ^ i - 1))%N.
Proof.
case=> // n' _; set n := n'.+1; set p := #|F|.
rewrite big_nat_rev big_add1 -triangular_sum expn_sum -big_split /=.
pose fr m := [pred A : 'M[F]_(m, n) | \rank A == m].
set m := {-7}n; transitivity #|fr m|.
  by rewrite cardsT /= card_sub; apply: eq_card => A; rewrite -row_free_unit.
elim: m (leqnn m : m <= n) => [_|m IHm]; last move/ltnW=> le_mn.
  rewrite (@eq_card1 _ (0 : 'M_(0, n))) ?big_geq //= => A.
  by rewrite [A]flatmx0 !inE !eqxx.
rewrite big_nat_recr -{}IHm //= !subSS muln_subr muln1 -expn_add subnKC //.
rewrite -sum_nat_const /= -sum1_card -add1n.
rewrite (partition_big dsubmx (fr m)) /= => [|A]; last first.
  rewrite !inE -{1}(vsubmxK A); move: {A}(_ A) (_ A) => Ad Au Afull.
  rewrite eqn_leq rank_leq_row -(leq_add2l (\rank Au)) -mxrank_sum_cap.
  rewrite {1 3}[@mxrank]lock addsmxE (eqnP Afull) -lock -addnA.
  by rewrite leq_add ?rank_leq_row ?leq_addr.
apply: eq_bigr => A rAm; rewrite (reindex (col_mx^~ A)) /=; last first.
  exists usubmx => [v _ | vA]; first by rewrite col_mxKu.
  by case/andP=> _; move/eqP <-; rewrite vsubmxK.
transitivity #|~: [set v *m A | v <- 'rV_m]|; last first.
  rewrite cardsCs setCK card_imset ?card_matrix ?card_ord ?mul1n //.
  have [B AB1] := row_freeP rAm; apply: can_inj (mulmx^~ B) _ => v.
  by rewrite -mulmxA AB1 mulmx1.
rewrite -sum1_card; apply: eq_bigl => v; rewrite !inE col_mxKd eqxx.
rewrite andbT eqn_leq rank_leq_row /= -(leq_add2r (\rank (v :&: A)%MS)).
rewrite -addsmxE mxrank_sum_cap (eqnP rAm) addnAC leq_add2r.
rewrite (ltn_leqif (mxrank_leqif_sup _)) ?capmxSl // sub_capmx submx_refl.
by congr (~~ _); apply/submxP/imsetP=> [] [u]; exists u.
Qed.

(* An alternate, somewhat more elementary proof, that does not rely on the *)
(* row-space theory, but directly performs the LUP decomposition.          *)
Lemma LUP_card_GL : forall n, n > 0 ->
  #|'GL_n[F]| = (#|F| ^ 'C(n, 2) * \prod_(1 <= i < n.+1) (#|F| ^ i - 1))%N.
Proof.
case=> // n' _; set n := n'.+1; set p := #|F|.
rewrite cardsT /= card_sub /GRing.unit /= big_add1 /= -triangular_sum -/n.
elim: {n'}n => [|n IHn].
  rewrite !big_geq // mul1n (@eq_card _ _ predT) ?card_matrix //= => M.
  by rewrite {1}[M]flatmx0 -(flatmx0 1%:M) unitmx1.
rewrite !big_nat_recr /= expn_add mulnAC mulnA -{}IHn -mulnA mulnC.
set LHS := #|_|; rewrite -[n.+1]muln1 -{2}[n]mul1n {}/LHS.
rewrite -!card_matrix subn1 -(cardC1 0) -mulnA; set nzC := predC1 _.
rewrite -sum1_card (partition_big lsubmx nzC) => [|A]; last first.
  rewrite unitmxE unitfE; apply: contra; move/eqP=> v0.
  rewrite -[A]hsubmxK v0 -[n.+1]/(1 + n)%N -col_mx0.
  rewrite -[rsubmx _]vsubmxK -det_tr tr_row_mx !tr_col_mx !trmx0.
  by rewrite det_lblock [0]mx11_scalar det_scalar1 mxE mul0r.
rewrite -sum_nat_const; apply: eq_bigr; rewrite /= -[n.+1]/(1 + n)%N => v nzv.
case: (pickP (fun i => v i 0 != 0)) => [k nza | v0]; last first.
  by case/eqP: nzv; apply/colP=> i; move/eqP: (v0 i); rewrite mxE.
have xrkK: involutive (@xrow F _ _ 0 k).
  by move=> m A /=; rewrite /xrow -row_permM tperm2 row_perm1.
rewrite (reindex_inj (inv_inj (xrkK (1 + n)%N))) /= -[n.+1]/(1 + n)%N.
rewrite (partition_big ursubmx xpredT) //= -sum_nat_const.
apply: eq_bigr => u _; set a : F := v _ _ in nza.
set v1 : 'cV_(1 + n) := xrow 0 k v.
have def_a: usubmx v1 = a%:M.
  by rewrite [_ v1]mx11_scalar mxE lshift0 mxE tpermL.
pose Schur := dsubmx v1 *m (a^-1 *: u).
pose L : 'M_(1 + n) := block_mx a%:M 0 (dsubmx v1) 1%:M.
pose U B : 'M_(1 + n) := block_mx 1 (a^-1 *: u) 0 B.
rewrite (reindex (fun B => L *m U B)); last first.
  exists (fun A1 => drsubmx A1 - Schur) => [B _ | A1].
    by rewrite mulmx_block block_mxKdr mul1mx addrC addKr.
  rewrite !inE mulmx_block !mulmx0 mul0mx !mulmx1 !addr0 mul1mx addrC subrK.
  rewrite mul_scalar_mx scalerA divff // scale1r andbC; case/and3P.
  move/eqP=> <- _; rewrite -{1}(hsubmxK A1) xrowE mul_mx_row row_mxKl -xrowE.
  move/eqP=> def_v; rewrite -def_a block_mxEh vsubmxK /v1 -def_v xrkK.
  apply: trmx_inj; rewrite tr_row_mx tr_col_mx trmx_ursub trmx_drsub trmx_lsub.
  by rewrite hsubmxK vsubmxK.
rewrite -sum1_card; apply: eq_bigl => B; rewrite xrowE unitmxE.
rewrite !det_mulmx unitr_mul -unitmxE unitmx_perm det_lblock det_ublock.
rewrite !det_scalar1 det1 mulr1 mul1r unitr_mul unitfE nza -unitmxE.
rewrite mulmx_block !mulmx0 mul0mx !addr0 !mulmx1 mul1mx block_mxKur.
rewrite mul_scalar_mx scalerA divff // scale1r eqxx andbT.
by rewrite block_mxEh mul_mx_row row_mxKl -def_a vsubmxK -xrowE xrkK eqxx andbT.
Qed.

Lemma card_GL_1 : #|'GL_1[F]| = #|F|.-1.
Proof. by rewrite card_GL // mul1n big_nat1 expn1 subn1. Qed.

Lemma card_GL_2 : #|'GL_2[F]| = (#|F| * #|F|.-1 ^ 2 * #|F|.+1)%N.
Proof.
rewrite card_GL // big_ltn // big_nat1 expn1 -(addn1 #|F|) -subn1 -!mulnA.
by rewrite -subn_sqr.
Qed.

End CardGL.

Lemma logn_card_GL_p : forall n p, prime p -> logn p #|'GL_n(p)| = 'C(n, 2).
Proof.
move=> n p p_pr; have p_gt1 := prime_gt1 p_pr.
have p_i_gt0: p ^ _ > 0 by move=> i; rewrite expn_gt0 ltnW.
rewrite (card_GL _ (ltn0Sn n.-1)) card_ord Fp_cast // big_add1 /=.
pose p'gt0 m := m > 0 /\ logn p m = 0%N.
suffices [Pgt0 p'P]: p'gt0 (\prod_(0 <= i < n.-1.+1) (p ^ i.+1 - 1))%N.
  by rewrite logn_mul // p'P pfactorK //; case n.
apply big_prop => [|m1 m2 [m10 p'm1] [m20]|i _]; rewrite {}/p'gt0 ?logn1 //.
  by rewrite muln_gt0 m10 logn_mul ?p'm1.
rewrite lognE -if_neg subn_gt0 p_pr /= -{1 2}(exp1n i.+1) ltn_exp2r // p_gt1.
by rewrite dvdn_subr ?dvdn_exp // gtnNdvd.
Qed.

Section MatrixAlgebra.

Variables F : fieldType.

Local Notation "A \in R" := (@submx F _ _ _ (mxvec A) R).

Lemma mem0mx : forall m n (R : 'A_(m, n)), 0 \in R.
Proof. by move=> m n R; rewrite linear0 sub0mx. Qed.

Lemma memmx0 : forall n A, (A \in (0 : 'A_n)) -> A = 0.
Proof. by move=> m A; rewrite submx0 mxvec_eq0; move/eqP. Qed.

Lemma memmx1 : forall n (A : 'M_n), (A \in mxvec 1%:M) = is_scalar_mx A.
Proof.
move=> n A; apply/sub_rVP/is_scalar_mxP=> [[a] | [a ->]].
  by rewrite -linearZ scale_scalar_mx mulr1; move/(can_inj mxvecK); exists a.
by exists a; rewrite -linearZ scale_scalar_mx mulr1.
Qed.

Lemma memmx_subP : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (forall A, A \in R1 -> A \in R2) (R1 <= R2)%MS.
Proof.
move=> m1 m2 n R1 R2.
apply: (iffP idP) => [sR12 A R1_A | sR12]; first exact: submx_trans sR12.
by apply/rV_subP=> vA; rewrite -(vec_mxK vA); exact: sR12.
Qed.
Implicit Arguments memmx_subP [m1 m2 n R1 R2].

Lemma memmx_eqP : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (forall A, (A \in R1) = (A \in R2)) (R1 == R2)%MS.
Proof.
move=> m1 m2 n R1 R2.
apply: (iffP eqmxP) => [eqR12 A | eqR12]; first by rewrite eqR12.
by apply/eqmxP; apply/rV_eqP=> vA; rewrite -(vec_mxK vA) eqR12.
Qed.
Implicit Arguments memmx_eqP [m1 m2 n R1 R2].

Lemma memmx_addsP : forall m1 m2 n A (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (exists D, [/\ D.1 \in R1, D.2 \in R2 & A = D.1 + D.2])
          (A \in R1 + R2)%MS.
Proof.
move=> m1 m2 n A R1 R2; apply: (iffP sub_addsmxP) => [[u] | [D []]].
  move/(canRL mxvecK)->; exists (vec_mx (u.1 *m R1), vec_mx (u.2 *m R2)).
  by rewrite /= linearD !vec_mxK !submxMl.
case/submxP=> u1 defD1; case/submxP=> u2 defD2 ->.
by exists (u1, u2); rewrite linearD /= defD1 defD2.
Qed.
Implicit Arguments memmx_addsP [m1 m2 n A R1 R2].

Lemma memmx_sumsP : forall (I : finType) (P : pred I) n (A : 'M_n) R_,
  reflect (exists2 A_, A = \sum_(i | P i) A_ i & forall i, A_ i \in R_ i)
          (A \in \sum_(i | P i) R_ i)%MS.
Proof.
move=> I P n A R_.
apply: (iffP sub_sumsmxP) => [[C defA] | [A_ -> R_A] {A}].
  exists (fun i => vec_mx (C i *m R_ i)) => [|i].
    by rewrite -linear_sum -defA /= mxvecK.
  by rewrite vec_mxK submxMl.
exists (fun i => mxvec (A_ i) *m pinvmx (R_ i)).
by rewrite linear_sum; apply: eq_bigr => i _; rewrite mulmxKpV.
Qed.
Implicit Arguments memmx_sumsP [I P n A R_].

Lemma has_non_scalar_mxP : forall m n (R : 'A_(m, n)), 
    (1%:M \in R)%MS ->
  reflect (exists2 A, A \in R & ~~ is_scalar_mx A)%MS (1 < \rank R).
Proof.
move=> m n; case: (posnP n) => [-> | n_gt0] R; set S := mxvec _ => sSR.
  by rewrite [R]thinmx0 mxrank0; right; case; rewrite /is_scalar_mx ?insubF.
have rankS: \rank S = 1%N.
  apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0 mxvec_eq0.
  by rewrite -mxrank_eq0 mxrank1 -lt0n.
rewrite -{2}rankS (ltn_leqif (mxrank_leqif_sup sSR)).
apply: (iffP idP) => [|[A sAR]].
  case/row_subPn=> i; rewrite -[row i R]vec_mxK memmx1.
  by set A := vec_mx _ => nsA; exists A; rewrite // vec_mxK row_sub.
by rewrite -memmx1; apply: contra; exact: submx_trans.
Qed.

Definition mulsmx m1 m2 n (R1 : 'A[F]_(m1, n)) (R2 : 'A_(m2, n)) :=
  (\sum_i <<R1 *m lin_mx (mulmxr (vec_mx (row i R2)))>>)%MS.

Arguments Scope mulsmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].

Local Notation "R1 * R2" := (mulsmx R1 R2) : matrix_set_scope.

Lemma genmx_muls : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  <<(R1 * R2)%MS>>%MS = (R1 * R2)%MS.
Proof.
by move=> *; rewrite genmx_sums; apply: eq_bigr => i; rewrite genmx_id.
Qed.

Lemma mem_mulsmx : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) A1 A2,
  (A1 \in R1 -> A2 \in R2 -> A1 *m A2 \in R1 * R2)%MS.
Proof.
move=> m1 m2 n R1 R2 A1 A2 R_A1 R_A2.
rewrite -[A2]mxvecK; case/submxP: R_A2 => a ->{A2}.
rewrite mulmx_sum_row !linear_sum summx_sub // => i _.
rewrite !linearZ scalemx_sub {a}//= (sumsmx_sup i) // genmxE.
rewrite -[A1]mxvecK; case/submxP: R_A1 => a ->{A1}.
by apply/submxP; exists a; rewrite mulmxA mul_rV_lin.
Qed.

Lemma mulsmx_subP : forall m1 m2 m n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                    forall (R : 'A_(m, n)),
  reflect (forall A1 A2, A1 \in R1 -> A2 \in R2 -> A1 *m A2 \in R)
          (R1 * R2 <= R)%MS.
Proof.
move=> m1 m2 m n R1 R2 R; apply: (iffP memmx_subP) => [sR12R * | sR12R A].
  by rewrite sR12R ?mem_mulsmx.
case/memmx_sumsP=> A_ -> R_A; rewrite linear_sum summx_sub //= => j _.
rewrite (submx_trans (R_A _)) // genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin sR12R ?vec_mxK ?row_sub.
Qed.
Implicit Arguments mulsmx_subP [m1 m2 m n R1 R2 R].

Lemma mulsmxS : forall m1 m2 m3 m4 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                forall (R3 : 'A_(m3, n)) (R4 : 'A_(m4, n)),
  (R1 <= R3 -> R2 <= R4 -> R1 * R2 <= R3 * R4)%MS.
Proof.
move=> m1 m2 m3 m4 n R1 R2 R3 R4 sR13 sR24.
apply/mulsmx_subP=> A1 A2 R_A1 R_A2.
by apply: mem_mulsmx; [exact: submx_trans sR13 | exact: submx_trans sR24].
Qed.

Lemma muls_eqmx : forall m1 m2 m3 m4 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                  forall (R3 : 'A_(m3, n)) (R4 : 'A_(m4, n)),
  (R1 :=: R3 -> R2 :=: R4 -> R1 * R2 = R3 * R4)%MS.
Proof.
move=> m1 m2 m3 m4 n R1 R2 R3 R4 eqR13 eqR24.
rewrite -(genmx_muls R1 R2) -(genmx_muls R3 R4); apply/genmxP.
by rewrite !mulsmxS ?eqR13 ?eqR24.
Qed.

Lemma mulsmxP : forall m1 m2 n A (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (exists2 A1, forall i, A1 i \in R1 & exists2 A2, forall i, A2 i \in R2
           & A = \sum_(i < n ^ 2) A1 i *m A2 i)
          (A \in R1 * R2)%MS.
Proof.
move=> m1 m2 n A R1 R2.
apply: (iffP idP) => [R_A|[A1 R_A1 [A2 R_A2 ->{A}]]]; last first.
  by rewrite linear_sum summx_sub // => i _; rewrite mem_mulsmx.
have{R_A}: (A \in R1 * <<R2>>)%MS.
  by apply: memmx_subP R_A; rewrite mulsmxS ?genmxE.
case/memmx_sumsP=> A_ -> R_A; pose A2_ i := vec_mx (row i <<R2>>%MS).
pose A1_ i := mxvec (A_ i) *m pinvmx (R1 *m lin_mx (mulmxr (A2_ i))) *m R1.
exists (vec_mx \o A1_) => [i|]; first by rewrite vec_mxK submxMl.
exists A2_ => [i|]; first by rewrite vec_mxK -(genmxE R2) row_sub.
apply: eq_bigr => i _; rewrite -[_ *m _](mx_rV_lin (mulmxr_linear _ _)).
by rewrite -mulmxA mulmxKpV ?mxvecK // -(genmxE (_ *m _)) R_A.
Qed.
Implicit Arguments mulsmxP [m1 m2 n A R1 R2].

Lemma mulsmxA : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  (R1 * (R2 * R3) = R1 * R2 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3; rewrite -(genmx_muls (_ * _)%MS) -genmx_muls.
apply/genmxP; apply/andP; split.
  apply/mulsmx_subP=> A1 A23 R_A1; case/mulsmxP=> A2 R_A2 [A3 R_A3 ->{A23}].
  by rewrite !linear_sum summx_sub //= => i _; rewrite mulmxA !mem_mulsmx.
apply/mulsmx_subP=> A12 A3; case/mulsmxP=> A1 R_A1 [A2 R_A2 ->{A12}] R_A3.
rewrite mulmx_suml linear_sum summx_sub //= => i _.
by rewrite -mulmxA !mem_mulsmx.
Qed.

Lemma mulsmx_addl : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                    forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  ((R1 + R2) * R3 = R1 * R3 + R2 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3.
rewrite -(genmx_muls R2 R3) -(genmx_muls R1 R3) -genmx_muls -genmx_adds.
apply/genmxP; rewrite andbC addsmx_sub !mulsmxS ?addsmxSl ?addsmxSr //=.
apply/mulsmx_subP=> A12 A3; case/memmx_addsP=> A [R_A1 R_A2 ->] R_A3.
by rewrite mulmx_addl linearD addmx_sub_adds ?mem_mulsmx.
Qed.

Lemma mulsmx_addr : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                    forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  (R1 * (R2 + R3) = R1 * R2 + R1 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3.
rewrite -(genmx_muls R1 R3) -(genmx_muls R1 R2) -genmx_muls -genmx_adds.
apply/genmxP; rewrite andbC addsmx_sub !mulsmxS ?addsmxSl ?addsmxSr //=.
apply/mulsmx_subP=> A1 A23 R_A1; case/memmx_addsP=> A [R_A2 R_A3 ->].
by rewrite mulmx_addr linearD addmx_sub_adds ?mem_mulsmx.
Qed.

Lemma mulsmx0 : forall m1 m2 n (R1 : 'A_(m1, n)),
  (R1 * (0 : 'A_(m2, n)) = 0)%MS.
Proof.
move=> m1 m2 n R1; apply/eqP; rewrite -submx0; apply/mulsmx_subP=> A1 A0 _.
by rewrite [A0 \in 0]eqmx0; move/memmx0->; rewrite mulmx0 mem0mx.
Qed.

Lemma muls0mx : forall m1 m2 n (R2 : 'A_(m2, n)),
  ((0 : 'A_(m1, n)) * R2 = 0)%MS.
Proof.
move=> m1 m2 n R1; apply/eqP; rewrite -submx0; apply/mulsmx_subP=> A0 A2.
by rewrite [A0 \in 0]eqmx0; move/memmx0->; rewrite mul0mx mem0mx.
Qed.

Definition left_mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  (R1 * R2 <= R2)%MS.

Definition right_mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  (R2 * R1 <= R2)%MS.

Definition mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  left_mx_ideal R1 R2 && right_mx_ideal R1 R2.

Definition mxring_id m n (R : 'A_(m, n)) e :=
  [/\ e != 0,
      e \in R,
      forall A, A \in R -> e *m A = A
    & forall A, A \in R -> A *m e = A]%MS.

Definition has_mxring_id m n (R : 'A[F]_(m , n)) :=
  (R != 0) &&
  (row_mx 0 (row_mx (mxvec R) (mxvec R))
    <= row_mx (cokermx R) (row_mx (lin_mx (mulmx R \o lin_mulmx))
                                  (lin_mx (mulmx R \o lin_mulmxr))))%MS.

Definition mxring m n (R : 'A_(m, n)) :=
  left_mx_ideal R R && has_mxring_id R.

Lemma mxring_idP : forall m n (R : 'A_(m, n)),
  reflect (exists e, mxring_id R e) (has_mxring_id R).
Proof.
move=> m n R; apply: (iffP andP) => [[nzR] | [e [nz_e Re ideR idRe]]].
  case/submxP=> v; rewrite -[v]vec_mxK; move/vec_mx: v => e.
  rewrite !mul_mx_row; case/eq_row_mx; move/eqP.
  rewrite eq_sym -submxE => Re.
  case/eq_row_mx; rewrite !{1}mul_rV_lin1 /= mxvecK.
  set u := (_ *m _).
  move/(can_inj mxvecK) => idRe; move/(can_inj mxvecK) => ideR.
  exists e; split=> // [|A|A].
  - by apply: contra nzR; rewrite ideR; move/eqP->; rewrite !linear0.
  - case/submxP=> a defA; rewrite -{2}[A]mxvecK defA idRe.
    by rewrite mulmxA mx_rV_lin -defA /= mxvecK.
  case/submxP=> a defA; rewrite -{2}[A]mxvecK defA ideR.
  by rewrite mulmxA mx_rV_lin -defA /= mxvecK.
split.
  apply: contra nz_e; move/eqP=> R0; rewrite R0 eqmx0 in Re.
  by rewrite (memmx0 Re).
apply/submxP; exists (mxvec e); rewrite !mul_mx_row !{1}mul_rV_lin1.
rewrite submxE in Re; rewrite {Re}(eqP Re).
congr (row_mx 0 (row_mx (mxvec _) (mxvec _))); apply/row_matrixP=> i.
  by rewrite !row_mul !mul_rV_lin1 /= mxvecK ideR vec_mxK ?row_sub.
by rewrite !row_mul !mul_rV_lin1 /= mxvecK idRe vec_mxK ?row_sub.
Qed.
Implicit Arguments mxring_idP [m n R].

Section CentMxDef.

Variables (m n : nat) (R : 'A[F]_(m, n)).

Definition cent_mx_fun (B : 'M[F]_n) := R *m lin_mx (mulmxr B \- mulmx B).

Lemma cent_mx_fun_is_linear : linear cent_mx_fun.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP row_mul mul_rV_lin.
rewrite /= {-3}[row]lock row_mul mul_rV_lin -lock row_mul mul_rV_lin.
by rewrite -linearP -(linearP [linear of mulmx _ \- mulmxr _]).
Qed.
Canonical Structure cent_mx_fun_additive := Additive cent_mx_fun_is_linear.
Canonical Structure cent_mx_fun_linear := Linear cent_mx_fun_is_linear.


Definition cent_mx := kermx (lin_mx cent_mx_fun).

Definition center_mx := (R :&: cent_mx)%MS.

End CentMxDef.

Local Notation "''C' ( R )" := (cent_mx R) : matrix_set_scope.
Local Notation "''Z' ( R )" := (center_mx R) : matrix_set_scope.

Lemma cent_rowP : forall m n B (R : 'A_(m, n)),
  reflect (forall i (A := vec_mx (row i R)), A *m B = B *m A) (B \in 'C(R))%MS.
Proof.
move=> m n R B; apply: (iffP sub_kermxP); rewrite mul_vec_lin => cBE.
  move/(canRL mxvecK): cBE => cBE i A /=; move/(congr1 (row i)): cBE.
  rewrite row_mul mul_rV_lin -/A; move/(canRL mxvecK).
  by move/(canRL (subrK _)); rewrite !linear0 add0r.
apply: (canLR vec_mxK); apply/row_matrixP=> i.
by rewrite row_mul mul_rV_lin /= cBE subrr !linear0.
Qed.
Implicit Arguments cent_rowP [m n B R].

Lemma cent_mxP : forall m n B (R : 'A_(m, n)),
  reflect (forall A, A \in R -> A *m B = B *m A) (B \in 'C(R))%MS.
Proof.
move=> m n B R; apply: (iffP cent_rowP) => cEB => [A sAE | i A].
  rewrite -[A]mxvecK -(mulmxKpV sAE); move: (mxvec A *m _) => u.
  rewrite !mulmx_sum_row !linear_sum mulmx_suml; apply: eq_bigr => i _ /=.
  by rewrite !linearZ -scalemxAl /= cEB.
by rewrite cEB // vec_mxK row_sub.
Qed.
Implicit Arguments cent_mxP [m n B R].

Lemma scalar_mx_cent : forall m n a (R : 'A_(m, n)), (a%:M \in 'C(R))%MS.
Proof. by move=> m n a R; apply/cent_mxP=> A _; exact: scalar_mxC. Qed.

Lemma center_mx_sub : forall m n (R : 'A_(m, n)), ('Z(R) <= R)%MS.
Proof. move=> m n R; exact: capmxSl. Qed.

Lemma center_mxP : forall m n A (R : 'A_(m, n)),
  reflect (A \in R /\ forall B, B \in R -> B *m A = A *m B)
          (A \in 'Z(R))%MS.
Proof.
move=> m n A R; rewrite sub_capmx; case R_A: (A \in R); last by right; case.
by apply: (iffP cent_mxP) => [cAR | [_ cAR]].
Qed.
Implicit Arguments center_mxP [m n A R].

Lemma mxring_id_uniq : forall m n (R : 'A_(m, n)) e1 e2,
  mxring_id R e1 -> mxring_id R e2 -> e1 = e2.
Proof.
move=> m n R e1 e2 [_ Re1 idRe1 _] [_ Re2 _ ide2R].
by rewrite -(idRe1 _ Re2) ide2R.
Qed.

Lemma cent_mx_ideal : forall m n (R : 'A_(m, n)),
  left_mx_ideal 'C(R)%MS 'C(R)%MS.
Proof.
move=> m n R; apply/mulsmx_subP=> A1 A2 C_A1 C_A2; apply/cent_mxP=> B R_B.
by rewrite mulmxA (cent_mxP C_A1) // -!mulmxA (cent_mxP C_A2).
Qed.

Lemma cent_mx_ring : forall m n (R : 'A_(m, n)), n > 0 -> mxring 'C(R)%MS.
Proof.
move=> m n R n_gt0; rewrite /mxring cent_mx_ideal; apply/mxring_idP.
exists 1%:M; split=> [||A _|A _]; rewrite ?mulmx1 ?mul1mx ?scalar_mx_cent //.
by rewrite -mxrank_eq0 mxrank1 -lt0n.
Qed.

Lemma mxdirect_adds_center : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
    mx_ideal (R1 + R2)%MS R1 -> mx_ideal (R1 + R2)%MS R2 ->
    mxdirect (R1 + R2) ->
  ('Z((R1 + R2)%MS) :=: 'Z(R1) + 'Z(R2))%MS.
Proof.
move=> m1 m2 n R1 R2; case/andP=> idlR1 idrR1; case/andP=> idlR2 idrR2.
move/mxdirect_addsP=> dxR12.
apply/eqmxP; apply/andP; split.
  apply/memmx_subP=> z0; rewrite sub_capmx; case/andP.
  case/memmx_addsP=> z [R1z1 R2z2 ->{z0}] Cz.
  rewrite linearD addmx_sub_adds //= ?sub_capmx ?R1z1 ?R2z2 /=.
    apply/cent_mxP=> A R1_A; have R_A := submx_trans R1_A (addsmxSl R1 R2).
    have Rz2 := submx_trans R2z2 (addsmxSr R1 R2).
    rewrite -{1}[z.1](addrK z.2) mulmx_subr (cent_mxP Cz) // mulmx_addl.
    rewrite [A *m z.2]memmx0 1?[z.2 *m A]memmx0 ?addrK //.
      by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  apply/cent_mxP=> A R2_A; have R_A := submx_trans R2_A (addsmxSr R1 R2).
  have Rz1 := submx_trans R1z1 (addsmxSl R1 R2).
  rewrite -{1}[z.2](addKr z.1) mulmx_addr (cent_mxP Cz) // mulmx_addl.
  rewrite mulmxN [A *m z.1]memmx0 1?[z.1 *m A]memmx0 ?addKr //.
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
rewrite addsmx_sub; apply/andP; split.
  apply/memmx_subP=> z; rewrite sub_capmx; case/andP=> R1z cR1z.
  have Rz := submx_trans R1z (addsmxSl R1 R2).
  rewrite sub_capmx Rz; apply/cent_mxP=> A0.
  case/memmx_addsP=> A [R1_A1 R2_A2] ->{A0}.
  have R_A2 := submx_trans R2_A2 (addsmxSr R1 R2).
  rewrite mulmx_addl mulmx_addr (cent_mxP cR1z) //; congr (_ + _).
  rewrite [A.2 *m z]memmx0 1?[z *m A.2]memmx0 //.
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
apply/memmx_subP=> z; rewrite !sub_capmx; case/andP=> R2z cR2z.
have Rz := submx_trans R2z (addsmxSr R1 R2); rewrite Rz.
apply/cent_mxP=> A0; case/memmx_addsP=> A [R1_A1 R2_A2 ->{A0}].
rewrite mulmx_addl mulmx_addr (cent_mxP cR2z _ R2_A2) //; congr (_ + _).
have R_A1 := submx_trans R1_A1 (addsmxSl R1 R2).
rewrite [A.1 *m z]memmx0 1?[z *m A.1]memmx0 //.
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
Qed.

Lemma mxdirect_sums_center : forall (I : finType) m n (R : 'A_(m, n)) R_,
    (\sum_i R_ i :=: R)%MS -> mxdirect (\sum_i R_ i) ->
    (forall i : I, mx_ideal R (R_ i)) ->
  ('Z(R) :=: \sum_i 'Z(R_ i))%MS.
Proof.
move=> I m n R R_ defR dxR idealR.
have sR_R: (R_ _ <= R)%MS by move=> i; rewrite -defR (sumsmx_sup i).
have anhR: forall i j A B, i != j -> A \in R_ i -> B \in R_ j -> A *m B = 0.
  move=> i j A B ne_ij RiA RjB; apply: memmx0.
  have [[_ idRiR] [idRRj _]] := (andP (idealR i), andP (idealR j)).
  rewrite -(mxdirect_sumsP dxR j) // sub_capmx (sumsmx_sup i) //.
    by rewrite (mulsmx_subP idRRj) // (memmx_subP (sR_R i)).
  by rewrite (mulsmx_subP idRiR) // (memmx_subP (sR_R j)).
apply/eqmxP; apply/andP; split.
  apply/memmx_subP=> Z; rewrite sub_capmx; case/andP.
  rewrite -{1}defR; case/memmx_sumsP=> z ->{Z} Rz cRz.
  apply/memmx_sumsP; exists z => // i; rewrite sub_capmx Rz.
  apply/cent_mxP=> A RiA; have:= cent_mxP cRz A (memmx_subP (sR_R i) A RiA).
  rewrite (bigD1 i) //= mulmx_addl mulmx_addr mulmx_suml mulmx_sumr.
  by rewrite !big1 ?addr0 // => j; last rewrite eq_sym; move/anhR->.
apply/sumsmx_subP => i _; apply/memmx_subP=> z; rewrite sub_capmx.
case/andP=> Riz cRiz; rewrite sub_capmx (memmx_subP (sR_R i)) //=.
apply/cent_mxP=> A; rewrite -{1}defR; case/memmx_sumsP=> a -> R_a.
rewrite (bigD1 i) // mulmx_addl mulmx_addr mulmx_suml mulmx_sumr.
rewrite !big1 => [|j|j]; first by rewrite !addr0 (cent_mxP cRiz).
  by rewrite eq_sym; move/anhR->.
by move/anhR->.
Qed.

End MatrixAlgebra.

Arguments Scope mulsmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope left_mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope right_mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope mxring_id
  [_ nat_scope nat_scope ring_scope matrix_set_scope].
Arguments Scope has_mxring_id
  [_ nat_scope nat_scope ring_scope matrix_set_scope].
Arguments Scope mxring
  [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope cent_mx
  [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope center_mx
  [_ nat_scope nat_scope matrix_set_scope].

Prenex Implicits mulsmx.

Notation "A \in R" := (submx (mxvec A) R) : matrix_set_scope.
Notation "R * S" := (mulsmx R S) : matrix_set_scope.
Notation "''C' ( R )" := (cent_mx R) : matrix_set_scope.
Notation "''C_' R ( S )" := (R :&: 'C(S))%MS : matrix_set_scope.
Notation "''C_' ( R ) ( S )" := ('C_R(S))%MS (only parsing) : matrix_set_scope.
Notation "''Z' ( R )" := (center_mx R) : matrix_set_scope.

Implicit Arguments memmx_subP [F m1 m2 n R1 R2].
Implicit Arguments memmx_eqP [F m1 m2 n R1 R2].
Implicit Arguments memmx_addsP [F m1 m2 n R1 R2].
Implicit Arguments memmx_sumsP [F I P n A R_].
Implicit Arguments mulsmx_subP [F m1 m2 m n R1 R2 R].
Implicit Arguments mulsmxP [F m1 m2 n A R1 R2].
Implicit Arguments mxring_idP [m n R].
Implicit Arguments cent_rowP [F m n B R].
Implicit Arguments cent_mxP [F m n B R].
Implicit Arguments center_mxP [F m n A R].

(* Parametricity for the row-space/F-algebra theory.                         *)
Section MapMatrixSpaces.

Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma gaussian_elimination_map : forall m n (A : 'M_(m, n)),
  gaussian_elimination A^f = ((col_ebase A)^f, (row_ebase A)^f, \rank A).
Proof.
move=> m n A; rewrite mxrankE /row_ebase /col_ebase -lock.
elim: m n A => [|m IHm] [|n] A /=; rewrite ?map_mx1 //.
set pAnz := [pred k | A k.1 k.2 != 0].
rewrite (@eq_pick _ _ pAnz) => [|k]; last by rewrite /= mxE fmorph_eq0.
case: {+}(pick _) => [[i j]|]; last by rewrite !map_mx1.
rewrite mxE -fmorphV  -map_xcol -map_xrow -map_dlsubmx -map_drsubmx.
rewrite -map_ursubmx -map_mxZ -map_mxM -map_mx_sub {}IHm /=.
case: {+}(gaussian_elimination _) => [[L U] r] /=; rewrite map_xrow map_xcol.
by rewrite !(@map_block_mx _ _ f 1 _ 1) !map_mx0 ?map_mx1 ?map_scalar_mx.
Qed.

Lemma mxrank_map : forall m n (A : 'M_(m, n)), \rank A^f = \rank A.
Proof. by move=> m n A; rewrite mxrankE gaussian_elimination_map. Qed.

Lemma row_free_map : forall m n (A : 'M_(m, n)), row_free A^f = row_free A.
Proof. by move=> m n A; rewrite /row_free mxrank_map. Qed.

Lemma row_full_map : forall m n (A : 'M_(m, n)), row_full A^f = row_full A.
Proof. by move=> m n A; rewrite /row_full mxrank_map. Qed.

Lemma map_row_ebase : forall m n (A : 'M_(m, n)),
  (row_ebase A)^f = row_ebase A^f.
Proof.
by move=> m n A; unlock {2}row_ebase; rewrite gaussian_elimination_map.
Qed.

Lemma map_col_ebase : forall m n (A : 'M_(m, n)),
  (col_ebase A)^f = col_ebase A^f.
Proof.
by move=> m n A; unlock {2}col_ebase; rewrite gaussian_elimination_map.
Qed.

Lemma map_row_base : forall m n (A : 'M_(m, n)),
  (row_base A)^f = castmx (mxrank_map A, erefl n) (row_base A^f).
Proof.
move=> m n A; move: (mxrank_map A); rewrite {2}/row_base mxrank_map => eqrr.
by rewrite castmx_id map_mxM map_pid_mx map_row_ebase.
Qed.

Lemma map_col_base : forall m n (A : 'M_(m, n)),
  (col_base A)^f = castmx (erefl m, mxrank_map A) (col_base A^f).
Proof.
move=> m n A; move: (mxrank_map A); rewrite {2}/col_base mxrank_map => eqrr.
by rewrite castmx_id map_mxM map_pid_mx map_col_ebase.
Qed.

Lemma map_pinvmx : forall m n (A : 'M_(m, n)), (pinvmx A)^f = pinvmx A^f.
Proof.
move=> m n A; rewrite !map_mxM !map_invmx map_row_ebase map_col_ebase.
by rewrite map_pid_mx -mxrank_map.
Qed.

Lemma map_kermx : forall m n (A : 'M_(m, n)), (kermx A)^f = kermx A^f.
Proof.
move=> m n A; rewrite !map_mxM map_invmx map_col_ebase -mxrank_map.
by rewrite map_copid_mx.
Qed.

Lemma map_cokermx : forall m n (A : 'M_(m, n)), (cokermx A)^f = cokermx A^f.
Proof.
move=> m n A; rewrite !map_mxM map_invmx map_row_ebase -mxrank_map.
by rewrite map_copid_mx.
Qed.

Lemma map_submx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A^f <= B^f)%MS = (A <= B)%MS.
Proof.
by move=> m1 m2 n A B; rewrite !submxE -map_cokermx -map_mxM map_mx_eq0.
Qed.

Lemma map_ltmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A^f < B^f)%MS = (A < B)%MS.
Proof. by move=> m1 m2 n A B; rewrite /ltmx !map_submx. Qed.

Lemma map_eqmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A^f :=: B^f)%MS <-> (A :=: B)%MS.
Proof.
move=> m1 m2 n A B; split=> [|eqAB].
  by move/eqmxP; rewrite !map_submx; move/eqmxP.
by apply/eqmxP; rewrite !map_submx !eqAB !submx_refl.
Qed.

Lemma map_genmx : forall m n (A : 'M_(m, n)), (<<A>>^f :=: <<A^f>>)%MS.
Proof.
by move=> m n A; apply/eqmxP; rewrite !(genmxE, map_submx) andbb.
Qed.

Lemma map_addsmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (((A + B)%MS)^f :=: A^f + B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !addsmxE -map_col_mx !map_submx.
by rewrite !addsmxE andbb.
Qed.

Let map_capmx_gen : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (capmx_gen A B)^f = capmx_gen A^f B^f.
Proof.
by move=> m1 m2 n A B; rewrite map_mxM map_lsubmx map_kermx map_col_mx.
Qed.

Lemma map_capmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :&: B)^f :=: A^f :&: B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !capmxE -map_capmx_gen.
by rewrite !map_submx -!capmxE andbb.
Qed.

Lemma map_complmx : forall m n (A : 'M_(m, n)), (A^C^f = A^f^C)%MS.
Proof.
by move=> m n A; rewrite map_mxM map_row_ebase -mxrank_map map_copid_mx.
Qed.

Lemma map_diffmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :\: B)^f :=: A^f :\: B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !diffmxE -map_capmx_gen -map_complmx.
by rewrite -!map_capmx !map_submx -!diffmxE andbb.
Qed.

Lemma map_eigenspace : forall n (g : 'M_n) a,
  (eigenspace g a)^f = eigenspace g^f (f a).
Proof. by move=> n g a; rewrite map_kermx map_mx_sub ?map_scalar_mx. Qed.

Lemma eigenvalue_map : forall n (g : 'M_n) a,
  eigenvalue g^f (f a) = eigenvalue g a.
Proof. by move=> n g a; rewrite /eigenvalue -map_eigenspace map_mx_eq0. Qed.

Lemma memmx_map : forall m n A (E : 'A_(m, n)), (A^f \in E^f)%MS = (A \in E)%MS.
Proof. by move=> m n A E; rewrite -map_mxvec map_submx. Qed.

Lemma map_mulsmx : forall m1 m2 n (E1 : 'A_(m1, n)) (E2 : 'A_(m2, n)),
  ((E1 * E2)%MS^f :=: E1^f * E2^f)%MS.
Proof.
rewrite /mulsmx => m1 m2 n E1 E2; pose Rf (P Pf : 'A_n) := (P^f :=: Pf)%MS.
apply: (big_rel Rf) => [|P1 P1f P2 P2f ? ?|i _]; first by rewrite /Rf map_mx0.
  by apply: eqmx_trans (map_addsmx _ _) _; exact: adds_eqmx. 
apply/eqmxP; rewrite !map_genmx // !genmxE map_mxM //.
apply/rV_eqP=> u; congr (u <= _ *m _)%MS.
by apply: map_lin_mx => //= A; rewrite map_mxM // map_vec_mx map_row.
Qed.

Lemma map_cent_mx : forall m n (E : 'A_(m, n)), ('C(E)%MS)^f = 'C(E^f)%MS.
Proof.
move=> m n E; rewrite map_kermx //; congr (kermx _); apply: map_lin_mx => // A.
rewrite map_mxM //; congr (_ *m _); apply: map_lin_mx => //= B.
by rewrite map_mx_sub ? map_mxM.
Qed.

Lemma map_center_mx : forall m n (E : 'A_(m, n)), (('Z(E))^f :=: 'Z(E^f))%MS.
Proof. by move=> m n E; rewrite /center_mx -map_cent_mx; exact: map_capmx. Qed.

End MapMatrixSpaces.


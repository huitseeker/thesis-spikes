(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp.

(******************************************************************************)
(* Basic concrete linear algebra : definition of type for matrices, and all   *)
(* basic matrix operations including determinant, trace and support for block *)
(* decomposition. Matrices are represented by a row-major list of their       *)
(* coefficients but this implementation is hidden by three levels of wrappers *)
(* (Matrix/Finfun/Tuple) so the matrix type should be treated as abstract and *)
(* handled using only the operations described below:                         *)
(*   'M[R]_(m, n) == the type of m rows by n columns matrices with            *)
(*   'M_(m, n)       coefficients in R; the [R] is optional and is usually    *)
(*                   omitted.                                                 *)
(*  'M[R]_n, 'M_n == the type of n x n square matrices.                       *)
(* 'rV[R]_n, 'rV_n == the type of 1 x n row vectors.                          *)
(* 'cV[R]_n, 'cV_n == the type of n x 1 column vectors.                       *)
(*  \matrix_(i < m, j < n) Expr(i, j) ==                                      *)
(*                   the m x n matrix with general coefficient Expr(i, j),    *)
(*                   with i : 'I_m and j : 'I_n. the < m bound can be omitted *)
(*                   if it is equal to n, though usually both bounds are      *)
(*                   omitted as they can be inferred from the context.        *)
(*  \row_(j < n) Expr(j), \col_(i < m) Expr(i)                                *)
(*                   the row / column vectors with general term Expr; the     *)
(*                   parentheses can be omitted along with the bound.         *)
(* \matrix_(i < m) RowExpr(i) ==                                              *)
(*                   the m x n matrix with row i given by RowExpr(i) : 'rV_n. *)
(*          A i j == the coefficient of matrix A : 'M_(m, n) in column j of   *)
(*                   row i, where i : 'I_m, and j : 'I_n (via the coercion    *)
(*                   fun_of_matrix : matrix >-> Funclass).                    *)
(*     const_mx a == the constant matrix whose entries are all a (dimensions  *)
(*                   should be determined by context).                        *)
(*     map_mx f A == the pointwise image of A by f, i.e., the matrix Af       *)
(*                   congruent to A with Af i j = f (A i j) for all i and j.  *)
(*            A^T == the matrix transpose of A.                               *)
(*        row i A == the i'th row of A (this is a row vector).                *)
(*        col j A == the j'th column of A (a column vector).                  *)
(*       row' i A == A with the i'th row spliced out.                         *)
(*       col' i A == A with the j'th column spliced out.                      *)
(*   xrow i1 i2 A == A with rows i1 and i2 interchanged.                      *)
(*   xcol j1 j2 A == A with columns j1 and j2 interchanged.                   *)
(*   row_perm s A == A : 'M_(m, n) with rows permuted by s : 'S_m.            *)
(*   col_perm s A == A : 'M_(m, n) with columns permuted by s : 'S_n.         *)
(*   row_mx Al Ar == the row block matrix <Al Ar> obtained by contatenating   *)
(*                   two matrices Al and Ar of the same height.               *)
(*   col_mx Au Ad == the column block matrix / Au \ (Au and Ad must have the  *)
(*                   same width).            \ Ad /                           *)
(* block_mx Aul Aur Adl Adr == the block matrix / Aul Aur \                   *)
(*                                              \ Adl Adr /                   *)
(*   [l|r]submx A == the left/right submatrices of a row block matrix A.      *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicates how A *)
(*                   should be decomposed.                                    *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.      *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A.  *)
(* castmx eq_mn A == A : 'M_(m, n) cast to 'M_(m', n') using the equation     *)
(*                   pair eq_mn : (m = m') * (n = n'). This is the usual      *)
(*                   workaround for the syntactic limitations of dependent    *)
(*                   types in Coq, and can be used to introduce a block       *)
(*                   decomposition. It simplifies to A when eq_mn is the      *)
(*                   pair (erefl m, erefl n) (using rewrite /castmx /=).      *)
(* conform_mx B A == A if A and B have the same dimensions, else B.           *)
(*        mxvec A == a row vector of width m * n holding all the entries of   *)
(*                   the m x n matrix A.                                      *)
(* mxvec_index i j == the index of A i j in mxvec A.                          *)
(*       vec_mx v == the inverse of mxvec, reshaping a vector of width m * n  *)
(*                   back into into an m x n rectangular matrix.              *)
(* In 'M[R]_(m, n), R can be any type, but 'M[R]_(m, n) inherits the eqType,  *)
(* choiceType, countType, finType, zmodType structures of R; 'M[R]_(m, n)     *)
(* also has a natural lmodType R structure when R has a ringType structure.   *)
(* Because the type of matrices specifies their dimension, only non-trivial   *)
(* square matrices (of type 'M[R]_n.+1) can inherit the ring structure of R;  *)
(* indeed they then have an algebra structure (lalgType R, or algType R if R  *)
(* is a comRingType, or even unitAlgType if R is a comUnitRingType).          *)
(*   We thus provide separate syntax for the general matrix multiplication,   *)
(* and other operations for matrices over a ringType R:                       *)
(*         A *m B == the matrix product of A and B; the width of A must be    *)
(*                   equal to the height of B.                                *)
(*           a%:M == the scalar matrix with a's on the main diagonal; in      *)
(*                   particular 1%:M denotes the identity matrix, and is is   *)
(*                   equal to 1%R when n is of the form n'.+1 (e.g., n >= 1). *)
(* is_scalar_mx A <=> A is a scalar matrix (A = a%:M for some A).             *)
(*      diag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.    *)
(*   delta_mx i j == the matrix with a 1 in row i, column j and 0 elsewhere.  *)
(*       pid_mx r == the partial identity matrix with 1s only on the r first  *)
(*                   coefficients of the main diagonal; the dimensions of     *)
(*                   pid_mx r are determined by the context, and pid_mx r can *)
(*                   be rectangular.                                          *)
(*     copid_mx r == the complement to 1%:M of pid_mx r: a square diagonal    *)
(*                   matrix with 1s on all but the first r coefficients on    *)
(*                   its main diagonal.                                       *)
(*      perm_mx s == the n x n permutation matrix for s : 'S_n.               *)
(* tperm_mx i1 i2 == the permutation matrix that exchanges i1 i2 : 'I_n.      *)
(*   is_perm_mx A == A is a permutation matrix.                               *)
(*     lift0_mx A == the 1 + n square matrix block_mx 1 0 0 A when A : 'M_n.  *)
(*          \tr A == the trace of a square matrix A.                          *)
(*         \det A == the determinant of A, using the Leibnitz formula.        *)
(* cofactor i j A == the i, j cofactor of A (the signed i, j minor of A),     *)
(*         \adj A == the adjugate matrix of A (\adj A i j = cofactor j i A).  *)
(*   A \in unitmx == A is invertible (R must be a comUnitRingType).           *)
(*        invmx A == the inverse matrix of A if A \in unitmx A, otherwise A.  *)
(* The following operations provide a correspondance between linear functions *)
(* and matrices:                                                              *)
(*     lin1_mx f == the m x n matrix that emulates via right product          *)
(*                  a (linear) function f : 'rV_m -> 'rV_n on ROW VECTORS     *)
(*      lin_mx f == the (m1 * n1) x (m2 * n2) matrix that emulates, via the   *)
(*                  right multiplication on the mxvec encodings, a linear     *)
(*                  function f : 'M_(m1, n1) -> 'M_(m2, n2)                   *)
(* lin_mul_row u := lin1_mx (mulmx u \o vec_mx) (applies a row-encoded        *)
(*                  function to the row-vector u).                            *)
(*       mulmx A == partially applied matrix multiplication (mulmx A B is     *)
(*                  displayed as A *m B), with, for A : 'M_(m, n), a          *)
(*                  canonical {linear 'M_(n, p) -> 'M(m, p}} structure.       *)
(*      mulmxr A == self-simplifying right-hand matrix multiplication, i.e.,  *)
(*                  mulmxr A B simplifies to B *m A, with, for A : 'M_(n, p), *)
(*                  a canonical {linear 'M_(m, n) -> 'M(m, p}} structure.     *)
(*   lin_mulmx A := lin_mx (mulmx A).                                         *)
(*  lin_mulmxr A := lin_mx (mulmxr A).                                        *)
(* We also extend any finType structure of R to 'M[R]_(m, n), and define:     *)
(*     {'GL_n[R]} == the finGroupType of units of 'M[R]_n.-1.+1.              *)
(*      'GL_n[R]  == the general linear group of all matrices in {'GL_n(R)}.  *)
(*      'GL_n(p)  == 'GL_n['F_p], the general linear group of a prime field.  *)
(*       GLval u  == the coercion of u : {'GL_n(R)} to a matrix.              *)
(*   In addition to the lemmas relevant to these definitions, this file also  *)
(* proves several classic results, including :                                *)
(* - The determinant is a multilinear alternate form.                         *)
(* - The Laplace determinant expansion formulas: expand_det_[row|col].        *)
(* - The Cramer rule : mul_mx_adj & mul_adj_mx.                               *)
(* Finally, as an example of the use of block products, we program and prove  *)
(* the correctness of a classical linear algebra algorithm:                   *)
(*    cormenLUP A == the triangular decomposition (L, U, P) of a nontrivial   *)
(*                   square matrix A into a lower triagular matrix L with 1s  *)
(*                   on the main diagonal, an upper matrix U, and a           *)
(*                   permutation matrix P, such that P * A = L * U.           *)
(* This is example only; we use a different, more precise algorithm to        *)
(* develop the theory of matrix ranks and row spaces in mxalgebra.v           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").
Reserved Notation "''cV_' n"    (at level 8, n at level 2, format "''cV_' n").
Reserved Notation "''M_' ( n )" (at level 8, only parsing).
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2, only parsing).
Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''cV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''M[' R ]_ ( n )"     (at level 8, only parsing).
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8, only parsing).

Reserved Notation "\matrix_ i E" 
  (at level 36, E at level 36, i at level 2,
   format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\matrix_ ( i  <  n ) E").
Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50,
   format "\matrix_ ( i  <  m ,  j  <  n )  E").
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50,
   format "\matrix_ ( i ,  j  <  n )  E").
Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50,
   format "\row_ ( j  <  n )  E").
Reserved Notation "\col_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50,
   format "\col_ ( j  <  n )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Notation Local simp := (Monoid.Theory.simpm, oppr0).

(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(* We use dependent types (ordinals) for the indices so that ranges are   *)
(* mostly inferred automatically                                          *)

Inductive matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Canonical Structure matrix_subType :=
  Eval hnf in [newType for mx_val by matrix_rect].

Definition matrix_of_fun F := locked Matrix [ffun ij => F ij.1 ij.2].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

Lemma mxE : forall F, matrix_of_fun F =2 F.
Proof. by unlock matrix_of_fun fun_of_matrix => F i j; rewrite /= ffunE. Qed.

Lemma matrixP : forall A B : matrix, A =2 B <-> A = B.
Proof.
unlock fun_of_matrix => [] [A] [B]; split=> [/= eqAB | -> //].
congr Matrix; apply/ffunP=> [] [i j]; exact: eqAB.
Qed.

End MatrixDef.

Bind Scope ring_scope with matrix.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''cV[' R ]_ n" := 'M[R]_(n, 1) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M[' R ]_ ( n )" := 'M[R]_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''cV_' n" := 'M_(n, 1) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.

Notation "\matrix_ i E" :=
  (matrix_of_fun (fun i j => fun_of_matrix E (@GRing.zero (Zp_zmodType 0)) j))
  : ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) E 0 j) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\row_ j E" := (@matrix_of_fun _ 1 _ (fun _ j => E)) : ring_scope.
Notation "\row_ ( j < n ) E" :=
  (@matrix_of_fun _ 1 n (fun _ j => E)) (only parsing) : ring_scope.

Notation "\col_ i E" := (@matrix_of_fun _ _ 1 (fun i _ => E)) : ring_scope.
Notation "\col_ ( i < n ) E" :=
  (@matrix_of_fun _ n 1 (fun i _ => E)) (only parsing) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical Structure matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).
Canonical Structure matrix_subFinType (R : finType) m n :=
  Eval hnf in [subFinType of 'M[R]_(m, n)].

Lemma card_matrix : forall (F : finType) m n,
  (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
Proof. by move=> F m n; rewrite card_sub card_ffun card_prod !card_ord. Qed.

(*****************************************************************************)
(****** Matrix structural operations (transpose, permutation, blocks) ********)
(*****************************************************************************)

Section MatrixStructural.

Variable R : Type.

(* Constant matrix *)
Definition const_mx m n a : 'M[R]_(m, n) := \matrix_(i, j) a.
Implicit Arguments const_mx [[m] [n]].

Section FixedDim.
(* Definitions and properties for which we can work with fixed dimensions. *)

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

(* Reshape a matrix, to accomodate the block functions for instance. *)
Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Definition conform_mx m' n' B A :=
  match m =P m', n =P n' with
  | ReflectT eq_m, ReflectT eq_n => castmx (eq_m, eq_n) A
  | _, _ => B
  end.

(* Transpose a matrix *)
Definition trmx A := \matrix_(i, j) A j i.

(* Permute a matrix vertically (rows) or horizontally (columns) *)
Definition row_perm (s : 'S_m) A := \matrix_(i, j) A (s i) j.
Definition col_perm (s : 'S_n) A := \matrix_(i, j) A i (s j).

(* Exchange two rows/columns of a matrix *)
Definition xrow i1 i2 := row_perm (tperm i1 i2).
Definition xcol j1 j2 := col_perm (tperm j1 j2).

(* Row/Column sub matrices of a matrix *)
Definition row i0 A := \row_j A i0 j.
Definition col j0 A := \col_i A i j0.

(* Removing a row/column from a matrix *)
Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

Lemma castmx_const : forall m' n' (eq_mn : (m = m') * (n = n')) a,
  castmx eq_mn (const_mx a) = const_mx a.
Proof. by rewrite /castmx => m' n' []; case: m' /; case: n' /. Qed.

Lemma trmx_const : forall a, trmx (const_mx a) = const_mx a.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma row_perm_const : forall s a, row_perm s (const_mx a) = const_mx a.
Proof. by move=> s a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm_const : forall s a, col_perm s (const_mx a) = const_mx a.
Proof. by move=> s a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma xrow_const : forall i1 i2 a, xrow i1 i2 (const_mx a) = const_mx a.
Proof. by move=> i1 i2; exact: row_perm_const. Qed.

Lemma xcol_const : forall j1 j2 a, xcol j1 j2 (const_mx a) = const_mx a.
Proof. by move=> j1 j2; exact: col_perm_const. Qed.

Lemma rowP : forall u v : 'rV[R]_n, u = v <-> u 0 =1 v 0.
Proof.
by move=> u v; split=> [-> // | eq_uv]; apply/matrixP=> i; rewrite [i]ord1.
Qed.

Lemma rowK : forall u_ i0, row i0 (\matrix_i u_ i) = u_ i0.
Proof. by move=> u_ i0; apply/rowP=> i'; rewrite !mxE. Qed.

Lemma row_matrixP : forall A B, (forall i, row i A = row i B) <-> A = B.
Proof.
move=> A B; split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/rowP: (eqAB i); move/(_ j); rewrite !mxE.
Qed.

Lemma colP : forall u v : 'cV[R]_m, u = v <-> u^~ 0 =1 v^~ 0.
Proof.
by move=> u v; split=> [-> // | eq_uv]; apply/matrixP=> i j; rewrite [j]ord1.
Qed.

Lemma row_const : forall i0 a, row i0 (const_mx a) = const_mx a.
Proof. by move=> i0 a; apply/rowP=> j; rewrite !mxE. Qed.

Lemma col_const : forall j0 a, col j0 (const_mx a) = const_mx a.
Proof. by move=> j0 a; apply/colP=> i; rewrite !mxE. Qed.

Lemma row'_const : forall i0 a, row' i0 (const_mx a) = const_mx a.
Proof. by move=> i0 a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col'_const : forall j0 a, col' j0 (const_mx a) = const_mx a.
Proof. by move=> j0 a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm1 : forall A, col_perm 1 A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma row_perm1 : forall A, row_perm 1 A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma col_permM : forall s t A, col_perm (s * t) A = col_perm s (col_perm t A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma row_permM : forall s t A, row_perm (s * t) A = row_perm s (row_perm t A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma col_row_permC : forall s t A,
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE. Qed.

End FixedDim.

Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma castmx_id : forall m n erefl_mn (A : 'M_(m, n)), castmx erefl_mn A = A.
Proof. by move=> m n [e_m e_n]; rewrite [e_m]eq_axiomK [e_n]eq_axiomK. Qed.

Lemma castmx_comp : forall m1 n1 m2 n2 m3 n3,
                    forall (eq_m1 : m1 = m2) (eq_n1 : n1 = n2),
                    forall (eq_m2 : m2 = m3) (eq_n2 : n2 = n3) A,
  castmx (eq_m2, eq_n2) (castmx (eq_m1, eq_n1) A)
    = castmx (etrans eq_m1 eq_m2, etrans eq_n1 eq_n2) A.
Proof.
by move=> m1 n1 m2 n2 m3 n3; case: m2 /; case: n2 /; case: m3 /; case: n3 /.
Qed.

Lemma castmxK : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2),
  cancel (castmx (eq_m, eq_n)) (castmx (esym eq_m, esym eq_n)).
Proof. by move=> m1 n1 m2 n2; case: m2 /; case: n2/. Qed.

Lemma castmxKV : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2),
  cancel (castmx (esym eq_m, esym eq_n)) (castmx (eq_m, eq_n)).
Proof. by move=> m1 n1 m2 n2; case: m2 /; case: n2/. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castmx_sym : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A1 A2,
  A1 = castmx (eq_m, eq_n) A2 -> A2 = castmx (esym eq_m, esym eq_n) A1.
Proof. by symmetry; apply: (canLR (castmxK _ _)). Qed.

Lemma castmxE : forall m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j,
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.1) i) (cast_ord (esym eq_mn.2) j).
Proof.
by move=> m1 n1 m2 n2 []; case: m2 /; case: n2 / => A i j; rewrite !cast_ord_id.
Qed.

Lemma conform_mx_id : forall m n (B A : 'M_(m, n)), conform_mx B A = A.
Proof.
by rewrite /conform_mx => m n B A; do 2!case: eqP => // *; rewrite castmx_id.
Qed.

Lemma nonconform_mx : forall m m' n n' (B : 'M_(m', n')) (A : 'M_(m, n)),
  (m != m') || (n != n') -> conform_mx B A = B.
Proof. by rewrite /conform_mx => m m' n n' B A; do 2!case: eqP. Qed.

Lemma conform_castmx : forall m1 n1 m2 n2 m3 n3 (e : (m2 = m3) * (n2 = n3)),
  forall (B : 'M_(m1, n1)) A, conform_mx B (castmx e A) = conform_mx B A.
Proof. by move=> m1 n1 m2 n2 m3 n3 []; case: m3 /; case: n3 /. Qed.

Lemma trmxK : forall m n, cancel (@trmx m n) (@trmx n m).
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_inj : forall m n, injective (@trmx m n).
Proof. move=> m n; exact: can_inj (@trmxK m n). Qed.

Lemma trmx_cast : forall m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A,
  (castmx eq_mn A)^T = castmx (eq_mn.2, eq_mn.1) A^T.
Proof.
move=> m1 n1 m2 n2 [eq_m eq_n] A; apply/matrixP=> i j.
by rewrite !(mxE, castmxE).
Qed.

Lemma tr_row_perm : forall m n s (A : 'M_(m, n)),
  (row_perm s A)^T = col_perm s A^T.
Proof. by move=> m n s A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col_perm : forall m n s (A : 'M_(m, n)),
  (col_perm s A)^T = row_perm s A^T.
Proof. by move=> m n s A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_xrow : forall m n i1 i2 (A : 'M_(m, n)),
  (xrow i1 i2 A)^T = xcol i1 i2 A^T.
Proof. by move=> m n A i1 i2; exact: tr_row_perm. Qed.

Lemma tr_xcol : forall m n j1 j2 (A : 'M_(m, n)),
  (xcol j1 j2 A)^T = xrow j1 j2 A^T.
Proof. by move=> m n A j1 j2; exact: tr_col_perm. Qed.

Lemma row_id : forall n i (V : 'rV_n), row i V = V.
Proof. by move=> n i V; apply/rowP=> j; rewrite mxE [i]ord1. Qed.

Lemma col_id : forall n j (V : 'cV_n), col j V = V.
Proof. by move=> n j V; apply/colP=> i; rewrite mxE [j]ord1. Qed.

Lemma row_eq : forall m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
Proof.
by move=> m1 m2 n i1 i2 A1 A2 eq12 j; move/rowP: eq12; move/(_ j); rewrite !mxE.
Qed.

Lemma col_eq : forall m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof.
by move=> m n1 n2 j1 j2 A1 A2 eq12 i; move/colP: eq12; move/(_ i); rewrite !mxE.
Qed.

Lemma row'_eq : forall m n i0 (A B : 'M_(m, n)),
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
move=> m n i0 A B; move/matrixP=> eqAB' i.
rewrite !inE eq_sym; case/unlift_some=> i' -> _ j.
by have:= eqAB' i' j; rewrite !mxE.
Qed.

Lemma col'_eq : forall m n j0 (A B : 'M_(m, n)),
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
Proof.
move=> m n j0 A B; move/matrixP=> eqAB' i j.
rewrite !inE eq_sym; case/unlift_some=> j' -> _.
by have:= eqAB' i j'; rewrite !mxE.
Qed.

Lemma tr_row : forall m n i0 (A : 'M_(m, n)),
  (row i0 A)^T = col i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row' : forall m n i0 (A : 'M_(m, n)),
  (row' i0 A)^T = col' i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col : forall m n j0 (A : 'M_(m, n)),
  (col j0 A)^T = row j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col' : forall m n j0 (A : 'M_(m, n)),
  (col' j0 A)^T = row' j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

(* Concatenating two matrices, in either direction. *)

Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix_(i, j) match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix_(i, j) match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Left/Right | Up/Down submatrices of a rows | columns matrix.   *)
(* The shape of the (dependent) width parameters of the type of A *)
(* determines which submatrix is selected.                        *)

Definition lsubmx (A : 'M[R]_(m, n1 + n2)) := \matrix_(i, j) A i (lshift n2 j).

Definition rsubmx (A : 'M[R]_(m, n1 + n2)) := \matrix_(i, j) A i (rshift n1 j).

Definition usubmx (A : 'M[R]_(m1 + m2, n)) := \matrix_(i, j) A (lshift m2 i) j.

Definition dsubmx (A : 'M[R]_(m1 + m2, n)) := \matrix_(i, j) A (rshift m1 i) j.

Lemma row_mxEl : forall A1 A2 i j, row_mx A1 A2 i (lshift n2 j) = A1 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma row_mxKl : forall A1 A2, lsubmx (row_mx A1 A2) = A1.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE row_mxEl. Qed.

Lemma row_mxEr : forall A1 A2 i j, row_mx A1 A2 i (rshift n1 j) = A2 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma row_mxKr : forall A1 A2, rsubmx (row_mx A1 A2) = A2.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE row_mxEr. Qed.

Lemma hsubmxK : forall A, row_mx (lsubmx A) (rsubmx A) = A.
Proof.
move=> A; apply/matrixP=> i j; rewrite !mxE.
case: splitP => k Dk //=; rewrite !mxE //=; congr (A _ _); exact: val_inj.
Qed.

Lemma col_mxEu : forall A1 A2 i j, col_mx A1 A2 (lshift m2 i) j = A1 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma col_mxKu : forall A1 A2, usubmx (col_mx A1 A2) = A1.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE col_mxEu. Qed.

Lemma col_mxEd : forall A1 A2 i j, col_mx A1 A2 (rshift m1 i) j = A2 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma col_mxKd : forall A1 A2, dsubmx (col_mx A1 A2) = A2.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE col_mxEd. Qed.

Lemma eq_row_mx : forall A1 A2 B1 B2,
  row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> A1 A2 B1 B2 eqAB; move: (congr1 lsubmx eqAB) (congr1 rsubmx eqAB).
by rewrite !(row_mxKl, row_mxKr).
Qed.

Lemma eq_col_mx : forall A1 A2 B1 B2,
  col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> A1 A2 B1 B2 eqAB; move: (congr1 usubmx eqAB) (congr1 dsubmx eqAB).
by rewrite !(col_mxKu, col_mxKd).
Qed.

Lemma row_mx_const : forall a, row_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

Lemma col_mx_const : forall a, col_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

End CutPaste.

Lemma trmx_lsub : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (lsubmx A)^T = usubmx A^T.
Proof. by move=> m n1 n2 A; split_mxE. Qed.

Lemma trmx_rsub : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (rsubmx A)^T = dsubmx A^T.
Proof. by move=> m n1 n2 A; split_mxE. Qed.

Lemma tr_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
Proof. by move=> m n1 n2 A1 A2; split_mxE. Qed.

Lemma tr_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
Proof. by move=> m1 m2 n A1 A2; split_mxE. Qed.

Lemma trmx_usub : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (usubmx A)^T = lsubmx A^T.
Proof. by move=> m1 m2 n A; split_mxE. Qed.

Lemma trmx_dsub : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (dsubmx A)^T = rsubmx A^T.
Proof. by move=> m1 m2 n A; split_mxE. Qed.

Lemma vsubmxK : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  col_mx (usubmx A) (dsubmx A) = A.
Proof.
move=> m1 m2 n A; apply: trmx_inj.
by rewrite tr_col_mx trmx_usub trmx_dsub hsubmxK.
Qed.

Lemma cast_row_mx : forall m m' n1 n2 (eq_m : m = m') A1 A2,
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
Proof. by move=> m m' n1 n2; case: m' /. Qed.

Lemma cast_col_mx : forall m1 m2 n n' (eq_n : n = n') A1 A2,
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
Proof. by move=> m1 m2 n n'; case: n' /. Qed.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma row_mxA : forall m n1 n2 n3,
  forall (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)),
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
  row_mx A1 (row_mx A2 A3) = castmx cast (row_mx (row_mx A1 A2) A3).
Proof.
move=> m n1 n2 n3 A1 A2 A3; apply: (canRL (castmxKV _ _)); apply/matrixP=> i j.
rewrite castmxE !mxE cast_ord_id; case: splitP => j1 /= def_j.
  have: (j < n1 + n2) && (j < n1) by rewrite def_j lshift_subproof /=.
  by move: def_j; do 2![case: splitP => // ? ->; rewrite ?mxE]; move/ord_inj->.
case: splitP def_j => j2 ->{j} def_j; rewrite !mxE.
  have: ~~ (j2 < n1) by rewrite -leqNgt def_j leq_addr.
  have: j1 < n2 by rewrite -(ltn_add2l n1) -def_j.
  by move: def_j; do 2![case: splitP => // ? ->]; move/addnI; move/val_inj->.
have: ~~ (j1 < n2) by rewrite -leqNgt -(leq_add2l n1) -def_j leq_addr.
by case: splitP def_j => // ? ->; rewrite addnA; move/addnI; move/val_inj->.
Qed.
Definition row_mxAx := row_mxA. (* bypass Prenex Implicits. *)

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma col_mxA : forall m1 m2 m3 n,
  forall (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)),
  let cast := (esym (addnA m1 m2 m3), erefl n) in
  col_mx A1 (col_mx A2 A3) = castmx cast (col_mx (col_mx A1 A2) A3).
Proof. by move=> *; apply: trmx_inj; rewrite trmx_cast !tr_col_mx -row_mxA. Qed.
Definition col_mxAx := col_mxA. (* bypass Prenex Implicits. *)

Lemma row_row_mx : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  row i0 (row_mx A1 A2) = row_mx (row i0 A1) (row i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma col_col_mx : forall m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).
Proof.
by move=> *; apply: trmx_inj; rewrite !(tr_col, tr_col_mx, row_row_mx).
Qed.

Lemma row'_row_mx : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma col'_col_mx : forall m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  col' j0 (col_mx A1 A2) = col_mx (col' j0 A1) (col' j0 A2).
Proof.
by move=> *; apply: trmx_inj; rewrite !(tr_col', tr_col_mx, row'_row_mx).
Qed.

Lemma colKl : forall m n1 n2 j1 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col (lshift n2 j1) (row_mx A1 A2) = col j1 A1.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(row_mxEl, mxE). Qed.

Lemma colKr : forall m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col (rshift n1 j2) (row_mx A1 A2) = col j2 A2.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(row_mxEr, mxE). Qed.

Lemma rowKu : forall m1 m2 n i1 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row (lshift m2 i1) (col_mx A1 A2) = row i1 A1.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(col_mxEu, mxE). Qed.

Lemma rowKd : forall m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row (rshift m1 i2) (col_mx A1 A2) = row i2 A2.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(col_mxEd, mxE). Qed.

Lemma col'Kl : forall m n1 n2 j1 (A1 : 'M_(m, n1.+1)) (A2 : 'M_(m, n2)),
  col' (lshift n2 j1) (row_mx A1 A2) = row_mx (col' j1 A1) A2.
Proof.
move=> m n1 n2 j1 A1 A2; apply/matrixP=> i /= j; symmetry; rewrite 2!mxE.
case: splitP => j' def_j'.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j'.
rewrite -(row_mxEr A1); congr (row_mx _ _ _); apply: ord_inj => /=.
by rewrite /bump def_j' -ltnS -addSn ltn_addr.
Qed.

Lemma row'Ku : forall m1 m2 n i1 (A1 : 'M_(m1.+1, n)) (A2 : 'M_(m2, n)),
  row' (lshift m2 i1) (@col_mx m1.+1 m2 n A1 A2) = col_mx (row' i1 A1) A2.
Proof.
move=> m1 m2 n i1 A1 A2; apply: trmx_inj.
by rewrite tr_col_mx !(@tr_row' _.+1) (@tr_col_mx _.+1) col'Kl.
Qed.

Lemma mx'_cast : forall m n, 'I_n -> (m + n.-1)%N = (m + n).-1.
Proof. by move=> m n [j]; move/ltn_predK <-; rewrite addnS. Qed.

Lemma col'Kr : forall m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col' (rshift n1 j2) (@row_mx m n1 n2 A1 A2)
    = castmx (erefl m, mx'_cast n1 j2) (row_mx A1 (col' j2 A2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply/matrixP=> i j; symmetry.
rewrite castmxE mxE cast_ord_id; case: splitP => j' /= def_j.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j /bump leqNgt ltn_addr.
rewrite 2!mxE -(row_mxEr A1); congr (row_mx _ _ _ _); apply: ord_inj.
by rewrite /= def_j /bump leq_add2l addnCA.
Qed.

Lemma row'Kd : forall m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row' (rshift m1 i2) (col_mx A1 A2)
    = castmx (mx'_cast m1 i2, erefl n) (col_mx A1 (row' i2 A2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply: trmx_inj.
by rewrite trmx_cast !(tr_row', tr_col_mx) col'Kr.
Qed.

Section Block.

Variables m1 m2 n1 n2 : nat.

(* Building a block matrix from 4 matrices :               *)
(*  up left, up right, down left and down right components *)

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Lemma eq_block_mx : forall Aul Aur Adl Adr Bul Bur Bdl Bdr,
 block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
  [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].
Proof.
move=> Aul Aur Adl Adr Bul Bur Bdl Bdr.
by case/eq_col_mx; do 2!case/eq_row_mx=> -> ->.
Qed.

Lemma block_mx_const : forall a,
  block_mx (const_mx a) (const_mx a) (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lsubmx (usubmx A).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

Lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = A.
Proof. by rewrite /block_mx !hsubmxK vsubmxK. Qed.

End CutBlock.

Section CatBlock.

Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Let A := block_mx Aul Aur Adl Adr.

Lemma block_mxEul : forall i j, A (lshift m2 i) (lshift n2 j) = Aul i j.
Proof. by move=> i j; rewrite col_mxEu row_mxEl. Qed.
Lemma block_mxKul : ulsubmx A = Aul.
Proof. by rewrite /ulsubmx col_mxKu row_mxKl. Qed.

Lemma block_mxEur : forall i j, A (lshift m2 i) (rshift n1 j) = Aur i j.
Proof. by move=> i j; rewrite col_mxEu row_mxEr. Qed.
Lemma block_mxKur : ursubmx A = Aur.
Proof. by rewrite /ursubmx col_mxKu row_mxKr. Qed.

Lemma block_mxEdl : forall i j, A (rshift m1 i) (lshift n2 j) = Adl i j.
Proof. by move=> i j; rewrite col_mxEd row_mxEl. Qed.
Lemma block_mxKdl : dlsubmx A = Adl.
Proof. by rewrite /dlsubmx col_mxKd row_mxKl. Qed.

Lemma block_mxEdr : forall i j, A (rshift m1 i) (rshift n1 j) = Adr i j.
Proof. by move=> i j; rewrite col_mxEd row_mxEr. Qed.
Lemma block_mxKdr : drsubmx A = Adr.
Proof. by rewrite /drsubmx col_mxKd row_mxKr. Qed.

Lemma block_mxEv : A = col_mx (row_mx Aul Aur) (row_mx Adl Adr).
Proof. by []. Qed.

End CatBlock.

End Block.

Section TrCutBlock.

Variables m1 m2 n1 n2 : nat.
Variable A : 'M[R]_(m1 + m2, n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T = ulsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_ursub : (ursubmx A)^T = dlsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_dlsub : (dlsubmx A)^T = ursubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_drsub : (drsubmx A)^T = drsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End TrCutBlock.

Section TrBlock.
Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma tr_block_mx :
 (block_mx Aul Aur Adl Adr)^T = block_mx Aul^T Adl^T Aur^T Adr^T.
Proof.
rewrite -[_^T]submxK -trmx_ulsub -trmx_ursub -trmx_dlsub -trmx_drsub.
by rewrite block_mxKul block_mxKur block_mxKdl block_mxKdr.
Qed.

Lemma block_mxEh :
  block_mx Aul Aur Adl Adr = row_mx (col_mx Aul Adl) (col_mx Aur Adr).
Proof. by apply: trmx_inj; rewrite tr_block_mx tr_row_mx 2!tr_col_mx. Qed.
End TrBlock.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma block_mxA : forall m1 m2 m3 n1 n2 n3,
  forall (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3)),
  forall (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3)),
  forall (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)),
  let cast := (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3)) in
  let row1 := row_mx A12 A13 in let col1 := col_mx A21 A31 in
  let row3 := row_mx A31 A32 in let col3 := col_mx A13 A23 in
  block_mx A11 row1 col1 (block_mx A22 A23 A32 A33)
    = castmx cast (block_mx (block_mx A11 A12 A21 A22) col3 row3 A33).
Proof.
move=> m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33 /=.
rewrite block_mxEh !col_mxA -cast_row_mx -block_mxEv -block_mxEh.
rewrite block_mxEv block_mxEh !row_mxA -cast_col_mx -block_mxEh -block_mxEv.
by rewrite castmx_comp etrans_id.
Qed.
Definition block_mxAx := block_mxA. (* Bypass Prenex Implicits *)

(* Bijections mxvec : 'M_(m, n) <----> 'rV_(m * n) : vec_mx *)
Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N. 
Proof. by rewrite card_prod !card_ord. Qed.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

CoInductive is_mxvec_index : 'I_(m * n) -> Type :=
  IsMxvecIndex i j : is_mxvec_index (mxvec_index i j).

Lemma mxvec_indexP : forall k, is_mxvec_index k.
Proof.
move=> k; rewrite -[k](cast_ordK (esym mxvec_cast)) esymK.
by rewrite -[_ k]enum_valK; case: (enum_val _).
Qed.

Coercion pair_of_mxvec_index k (i_k : is_mxvec_index k) :=
  let: IsMxvecIndex i j := i_k in (i, j).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Definition vec_mx (u : 'rV[R]_(m * n)) := \matrix_(i, j) u 0 (mxvec_index i j).

Lemma mxvecE : forall A i j, mxvec A 0 (mxvec_index i j) = A i j.
Proof. by move=> A i j; rewrite castmxE mxE cast_ordK enum_rankK. Qed.

Lemma mxvecK : cancel mxvec vec_mx.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE mxvecE. Qed.

Lemma vec_mxK : cancel vec_mx mxvec.
Proof.
by move=> u; apply/rowP=> k; case/mxvec_indexP: k => i j; rewrite mxvecE mxE.
Qed.

End VecMatrix.

End MatrixStructural.

Implicit Arguments const_mx [R m n].
Implicit Arguments row_mxA [R m n1 n2 n3 A1 A2 A3].
Implicit Arguments col_mxA [R m1 m2 m3 n A1 A2 A3].
Implicit Arguments block_mxA
  [R m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33].
Prenex Implicits const_mx castmx trmx lsubmx rsubmx usubmx dsubmx row_mx col_mx.
Prenex Implicits block_mx ulsubmx ursubmx dlsubmx drsubmx.
Prenex Implicits row_mxA col_mxA block_mxA.
Prenex Implicits mxvec vec_mx mxvec_indexP mxvecK vec_mxK.

Notation "A ^T" := (trmx A) : ring_scope.

(* Matrix parametricity. *)
Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Definition map_mx m n (A : 'M_(m, n)) := \matrix_(i, j) f (A i j).

Notation "A ^f" := (map_mx A) : ring_scope.

Section OneMatrix.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_trmx : A^f^T = A^T^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_const_mx : forall a, (const_mx a)^f = const_mx (f a) :> 'M_(m, n).
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row : forall i, (row i A)^f = row i A^f.
Proof. by move=> i; apply/rowP=> j; rewrite !mxE. Qed.

Lemma map_col : forall j, (col j A)^f = col j A^f.
Proof. by move=> j; apply/colP=> i; rewrite !mxE. Qed.

Lemma map_row' : forall i0, (row' i0 A)^f = row' i0 A^f.
Proof. by move=> i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col' : forall j0, (col' j0 A)^f = col' j0 A^f.
Proof. by move=> j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row_perm : forall s, (row_perm s A)^f = row_perm s A^f.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col_perm : forall s, (col_perm s A)^f = col_perm s A^f.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xrow : forall i1 i2, (xrow i1 i2 A)^f = xrow i1 i2 A^f.
Proof. by move=> i1 i2; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xcol : forall j1 j2, (xcol j1 j2 A)^f = xcol j1 j2 A^f.
Proof. by move=> j1 j2; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_castmx : forall m' n' c, (castmx c A)^f = castmx c A^f :> 'M_(m', n').
Proof. by move=> m' n' c; apply/matrixP=> i j; rewrite !(castmxE, mxE). Qed.

Lemma map_conform_mx : forall m' n' (B : 'M_(m', n')),
  (conform_mx B A)^f = conform_mx B^f A^f.
Proof.
move=> m' n'; case: (eqVneq (m, n) (m', n')) => [[<- <-] B|].
  by rewrite !conform_mx_id.
by rewrite negb_and => neq_mn B; rewrite !nonconform_mx.
Qed.

Lemma map_mxvec : (mxvec A)^f = mxvec A^f.
Proof. by apply/rowP=> i; rewrite !(castmxE, mxE). Qed.

Lemma map_vec_mx : forall v : 'rV_(m * n), (vec_mx v)^f = vec_mx v^f.
Proof. by move=> v; apply/matrixP=> i j; rewrite !mxE. Qed.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[aT]_(m1, n1)) (Aur : 'M[aT]_(m1, n2)).
Variables (Adl : 'M[aT]_(m2, n1)) (Adr : 'M[aT]_(m2, n2)).
Variables (Bh : 'M[aT]_(m1, n1 + n2)) (Bv : 'M[aT]_(m1 + m2, n1)).
Variable B : 'M[aT]_(m1 + m2, n1 + n2).

Lemma map_row_mx : (row_mx Aul Aur)^f = row_mx Aul^f Aur^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_col_mx : (col_mx Aul Adl)^f = col_mx Aul^f Adl^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_block_mx :
  (block_mx Aul Aur Adl Adr)^f = block_mx Aul^f Aur^f Adl^f Adr^f.
Proof. by apply/matrixP=> i j; do 3![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_lsubmx : (lsubmx Bh)^f = lsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_rsubmx : (rsubmx Bh)^f = rsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_usubmx : (usubmx Bv)^f = usubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dsubmx : (dsubmx Bv)^f = dsubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ulsubmx : (ulsubmx B)^f = ulsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ursubmx : (ursubmx B)^f = ursubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dlsubmx : (dlsubmx B)^f = dlsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_drsubmx : (drsubmx B)^f = drsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End Block.

End MapMatrix.

(*****************************************************************************)
(********************* Matrix Zmodule (additive) structure *******************)
(*****************************************************************************)

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Definition oppmx A := \matrix_(i, j) (- A i j).
Definition addmx A B := \matrix_(i, j) (A i j + B i j).
(* In principle, diag_mx and scalar_mx could be defined here, but since they *)
(* only make sense with the graded ring operations, we defer them to the     *)
(* next section.                                                             *)

Lemma addmxA : associative addmx.
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE addrA. Qed.

Lemma addmxC : commutative addmx.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE addrC. Qed.

Lemma add0mx : left_id (const_mx 0) addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE add0r. Qed.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE addNr. Qed.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.

Canonical Structure matrix_zmodType :=
  Eval hnf in ZmodType 'M[V]_(m, n) matrix_zmodMixin.

Lemma mulmxnE : forall A d i j, (A *+ d) i j = A i j *+ d.
Proof. by move=> A d i j; elim: d => [|d IHd]; rewrite ?mulrS mxE ?IHd. Qed.

Lemma summxE : forall I r (P : pred I) (E : I -> 'M_(m, n)) i j,
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
Proof.
move=> I r P E i j.
by apply: (big_morph (fun A => A i j)) => [A B|]; rewrite mxE.
Qed.

Lemma const_mx_is_additive : additive const_mx.
Proof. by move=> a b; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical Structure const_mx_additive := Additive const_mx_is_additive.

End FixedDim.

Section Additive.

Variables (m n p q : nat) (f : 'I_p -> 'I_q -> 'I_m) (g : 'I_p -> 'I_q -> 'I_n).

Definition swizzle_mx (A : 'M[V]_(m, n)) := \matrix_(i, j) A (f i j) (g i j).

Lemma swizzle_mx_is_additive : additive swizzle_mx.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical Structure swizzle_mx_additive := Additive swizzle_mx_is_additive.

End Additive.

Local Notation SwizzleAdd op := [additive of op as swizzle_mx _ _].

Canonical Structure trmx_additive m n := SwizzleAdd (@trmx V m n).
Canonical Structure row_additive m n i := SwizzleAdd (@row V m n i).
Canonical Structure col_additive m n j := SwizzleAdd (@col V m n j).
Canonical Structure row'_additive m n i := SwizzleAdd (@row' V m n i).
Canonical Structure col'_additive m n j := SwizzleAdd (@col' V m n j).
Canonical Structure row_perm_additive m n s := SwizzleAdd (@row_perm V m n s).
Canonical Structure col_perm_additive m n s := SwizzleAdd (@col_perm V m n s).
Canonical Structure xrow_additive m n i1 i2 := SwizzleAdd (@xrow V m n i1 i2).
Canonical Structure xcol_additive m n j1 j2 := SwizzleAdd (@xcol V m n j1 j2).
Canonical Structure lsubmx_additive m n1 n2 := SwizzleAdd (@lsubmx V m n1 n2).
Canonical Structure rsubmx_additive m n1 n2 := SwizzleAdd (@rsubmx V m n1 n2).
Canonical Structure usubmx_additive m1 m2 n := SwizzleAdd (@usubmx V m1 m2 n).
Canonical Structure dsubmx_additive m1 m2 n := SwizzleAdd (@dsubmx V m1 m2 n).
Canonical Structure vec_mx_additive m n := SwizzleAdd (@vec_mx V m n).
Canonical Structure mxvec_additive m n :=
  Additive (can2_additive (@vec_mxK V m n) mxvecK).

Lemma flatmx0 : forall n, all_equal_to (0 : 'M_(0, n)).
Proof. by move=> n A; apply/matrixP=> [] []. Qed.

Lemma thinmx0 : forall n, all_equal_to (0 : 'M_(n, 0)).
Proof. by move=> n A; apply/matrixP=> i []. Qed.

Lemma trmx0 : forall m n, (0 : 'M_(m, n))^T = 0.
Proof. by move=> m n; exact: trmx_const. Qed.

Lemma row0 : forall m n i0, row i0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n i0; exact: row_const. Qed.

Lemma col0 : forall m n j0, col j0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n j0; exact: col_const. Qed.

Lemma mxvec_eq0 : forall m n (A : 'M_(m, n)), (mxvec A == 0) = (A == 0).
Proof. by move=> m n A; rewrite (can2_eq mxvecK vec_mxK) raddf0. Qed.

Lemma vec_mx_eq0 : forall m n (v : 'rV_(m * n)), (vec_mx v == 0) = (v == 0).
Proof. by move=>  m n v; rewrite (can2_eq vec_mxK mxvecK) raddf0. Qed.

Lemma row_mx0 : forall m n1 n2, row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
Proof. by move=> m n1 n2; exact: row_mx_const. Qed.

Lemma col_mx0 : forall m1 m2 n, col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
Proof. by move=> m1 m2 n; exact: col_mx_const. Qed.

Lemma block_mx0 : forall m1 m2 n1 n2,
  block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
Proof. by move=> m1 m2 n1 n2; exact: block_mx_const. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma opp_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  - row_mx A1 A2 = row_mx (- A1) (- A2).
Proof. by move=> *; split_mxE. Qed.

Lemma opp_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  - col_mx A1 A2 = col_mx (- A1) (- A2).
Proof. by move=> *; split_mxE. Qed.

Lemma opp_block_mx : forall m1 m2 n1 n2,
  forall (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)),
  - block_mx Aul Aur Adl Adr = block_mx (- Aul) (- Aur) (- Adl) (- Adr).
Proof. by move=> *; rewrite opp_col_mx !opp_row_mx. Qed.

Lemma add_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2,
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_mxE. Qed.

Lemma add_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2,
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_mxE. Qed.

Lemma add_block_mx : forall m1 m2 n1 n2,
  forall (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) Bul Bur Bdl Bdr,
  let A := block_mx Aul Aur Adl Adr in let B := block_mx Bul Bur Bdl Bdr in
  A + B = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
Proof. by move=> *; rewrite add_col_mx !add_row_mx. Qed.

Definition nz_row m n (A : 'M_(m, n)) :=
  oapp (fun i => row i A) 0 [pick i | row i A != 0].

Lemma nz_row_eq0 : forall m n (A : 'M_(m, n)), (nz_row A == 0) = (A == 0).
Proof.
rewrite /nz_row => m n A; symmetry; case: pickP => [i /= nzAi | Ai0].
  by rewrite (negbTE nzAi); apply: contraTF nzAi; move/eqP->; rewrite row0 eqxx.
rewrite eqxx; apply/eqP; apply/row_matrixP=> i.
by move/eqP: (Ai0 i) ->; rewrite row0. 
Qed.

End MatrixZmodule.

Section FinZmodMatrix.
Variables (V : finZmodType) (m n : nat).
Local Notation MV := 'M[V]_(m, n).

Canonical Structure matrix_finZmodType := Eval hnf in [finZmodType of MV].
Canonical Structure matrix_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of MV for +%R].
Canonical Structure matrix_finGroupType :=
  Eval hnf in [finGroupType of MV for +%R].
End FinZmodMatrix.

(* Parametricity over the additive structure. *)
Section MapZmodMatrix.

Variables (aR rR : zmodType) (f : {additive aR -> rR}) (m n : nat).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mx0 : 0^f = 0 :> 'M_(m, n).
Proof. by rewrite map_const_mx raddf0. Qed.

Lemma map_mxN : forall A, (- A)^f = - A^f.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE raddfN. Qed.

Lemma map_mxD : forall A B, (A + B)^f = A^f + B^f.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE raddfD. Qed.

Lemma map_mx_sub : forall A B, (A - B)^f = A^f - B^f.
Proof. by move=> A B; rewrite map_mxD map_mxN. Qed.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

Canonical Structure map_mx_additive := Additive map_mx_sub.

End MapZmodMatrix.

(*****************************************************************************)
(*********** Matrix ring module, graded ring, and ring structures ************)
(*****************************************************************************)

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

(* The ring module/vector space structure *)

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Definition scalemx x A := \matrix_(i < m, j < n) (x * A i j).

(* Basis *)
Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix_(i < m, j < n) ((i == i0) && (j == j0))%:R.

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx : forall A, 1 *m: A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE mul1r. Qed.

Lemma scalemx_addl : forall A x y, (x + y) *m: A = x *m: A + y *m: A.
Proof. by move=> A x y; apply/matrixP=> i j; rewrite !mxE mulr_addl. Qed.

Lemma scalemx_addr : forall x A B, x *m: (A + B) = x *m: A + x *m: B.
Proof. by move=> x A B; apply/matrixP=> i j; rewrite !mxE mulr_addr. Qed.

Lemma scalemxA : forall x y A, x *m: (y *m: A) = (x * y) *m: A.
Proof. by move=> x y A; apply/matrixP=> i j; rewrite !mxE mulrA. Qed.

Definition matrix_lmodMixin := 
  LmodMixin scalemxA scale1mx scalemx_addr scalemx_addl.

Canonical Structure matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

Lemma scalemx_const : forall a b, a *: const_mx b = const_mx (a * b).
Proof. by move=> a b; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma matrix_sum_delta : forall A,
  A = \sum_(i < m) \sum_(j < n) A i j *: delta_mx i j.
Proof.
move=> A; apply/matrixP=> i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE !eqxx mulr1.
rewrite !big1 ?addr0 //= => [i' | j']; rewrite eq_sym; move/negbTE=> diff.
  by rewrite summxE big1 // => j' _; rewrite !mxE diff mulr0.
by rewrite !mxE eqxx diff mulr0.
Qed.

End RingModule.

Section StructuralLinear.

Lemma swizzle_mx_is_scalable : forall m n p q f g,
  scalable (@swizzle_mx R m n p q f g).
Proof. by move=> m n p q f g a A; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical Structure swizzle_mx_scalable m n p q f g :=
  AddLinear (@swizzle_mx_is_scalable m n p q f g).

Local Notation SwizzleLin op := [linear of op as swizzle_mx _ _].

Canonical Structure trmx_linear m n := SwizzleLin (@trmx R m n).
Canonical Structure row_linear m n i := SwizzleLin (@row R m n i).
Canonical Structure col_linear m n j := SwizzleLin (@col R m n j).
Canonical Structure row'_linear m n i := SwizzleLin (@row' R m n i).
Canonical Structure col'_linear m n j := SwizzleLin (@col' R m n j).
Canonical Structure row_perm_linear m n s := SwizzleLin (@row_perm R m n s).
Canonical Structure col_perm_linear m n s := SwizzleLin (@col_perm R m n s).
Canonical Structure xrow_linear m n i1 i2 := SwizzleLin (@xrow R m n i1 i2).
Canonical Structure xcol_linear m n j1 j2 := SwizzleLin (@xcol R m n j1 j2).
Canonical Structure lsubmx_linear m n1 n2 := SwizzleLin (@lsubmx R m n1 n2).
Canonical Structure rsubmx_linear m n1 n2 := SwizzleLin (@rsubmx R m n1 n2).
Canonical Structure usubmx_linear m1 m2 n := SwizzleLin (@usubmx R m1 m2 n).
Canonical Structure dsubmx_linear m1 m2 n := SwizzleLin (@dsubmx R m1 m2 n).
Canonical Structure vec_mx_linear m n := SwizzleLin (@vec_mx R m n).
Definition mxvec_is_linear m n := can2_linear (@vec_mxK R m n) mxvecK.
Canonical Structure mxvec_linear m n := AddLinear (@mxvec_is_linear m n).

End StructuralLinear.

Lemma trmx_delta : forall m n i j,
  (delta_mx i j)^T = delta_mx j i :> 'M[R]_(n, m).
Proof. by move=> m n i j; apply/matrixP=> i' j'; rewrite !mxE andbC. Qed.

Lemma row_sum_delta : forall n (u : 'rV_n),
  u = \sum_(j < n) u 0 j *: delta_mx 0 j.
Proof. by move=> n u; rewrite {1}[u]matrix_sum_delta big_ord1. Qed.

Lemma delta_mx_lshift : forall m n1 n2 i j,
  delta_mx i (lshift n2 j) = row_mx (delta_mx i j) 0 :> 'M_(m, n1 + n2).
Proof.
move=> m n1 n2 i j; apply/matrixP=> i' j'; rewrite !mxE -(can_eq (@splitK _ _)).
by rewrite (unsplitK (inl _ _)); case: split => ?; rewrite mxE ?andbF.
Qed.

Lemma delta_mx_rshift : forall m n1 n2 i j,
  delta_mx i (rshift n1 j) = row_mx 0 (delta_mx i j) :> 'M_(m, n1 + n2).
Proof.
move=> m n1 n2 i j; apply/matrixP=> i' j'; rewrite !mxE -(can_eq (@splitK _ _)).
by rewrite (unsplitK (inr _ _)); case: split => ?; rewrite mxE ?andbF.
Qed.

Lemma delta_mx_ushift : forall m1 m2 n i j,
  delta_mx (lshift m2 i) j = col_mx (delta_mx i j) 0 :> 'M_(m1 + m2, n).
Proof.
move=> m1 m2 n i j; apply/matrixP=> i' j'; rewrite !mxE -(can_eq (@splitK _ _)).
by rewrite (unsplitK (inl _ _)); case: split => ?; rewrite mxE.
Qed.

Lemma delta_mx_dshift : forall m1 m2 n i j,
  delta_mx (rshift m1 i) j = col_mx 0 (delta_mx i j) :> 'M_(m1 + m2, n).
Proof.
move=> m1 m2 n i j; apply/matrixP=> i' j'; rewrite !mxE -(can_eq (@splitK _ _)).
by rewrite (unsplitK (inr _ _)); case: split => ?; rewrite mxE.
Qed.

Lemma vec_mx_delta : forall m n i j,
  vec_mx (delta_mx 0 (mxvec_index i j)) = delta_mx i j :> 'M_(m, n).
Proof.
move=> m n i j; apply/matrixP=> i' j'.
by rewrite !mxE /= [_ == _](inj_eq (@enum_rank_inj _)).
Qed.

Lemma mxvec_delta : forall m n i j,
  mxvec (delta_mx i j) = delta_mx 0 (mxvec_index i j) :> 'rV_(m * n).
Proof. by move=> m n i j; rewrite -vec_mx_delta vec_mxK. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma scale_row_mx : forall m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  a *: row_mx A1 A2 = row_mx (a *: A1) (a *: A2).
Proof. by move=> *; split_mxE. Qed.

Lemma scale_col_mx : forall m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  a *: col_mx A1 A2 = col_mx (a *: A1) (a *: A2).
Proof. by move=> *; split_mxE. Qed.

Lemma scale_block_mx : forall m1 m2 n1 n2 a,
                       forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
                       forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
  a *: block_mx Aul Aur Adl Adr
     = block_mx (a *: Aul) (a *: Aur) (a *: Adl) (a *: Adr).
Proof. by move=> *; rewrite scale_col_mx !scale_row_mx. Qed.

(* Diagonal matrices *)

Definition diag_mx n (d : 'rV[R]_n) := \matrix_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx : forall n (d : 'rV_n), (diag_mx d)^T = diag_mx d.
Proof.
by move=> n d; apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->.
Qed.

Lemma diag_mx_is_linear : forall n, linear (@diag_mx n).
Proof.
by move=> n a d e; apply/matrixP=> i j; rewrite !mxE mulrnAr mulrn_addl.
Qed.
Canonical Structure diag_mx_additive n := Additive (@diag_mx_is_linear n).
Canonical Structure diag_mx_linear n := Linear (@diag_mx_is_linear n).

Lemma diag_mx_sum_delta : forall n (d : 'rV_n),
  diag_mx d = \sum_i d 0 i *: delta_mx i i.
Proof.
move=> n d; apply/matrixP=> i j; rewrite summxE (bigD1 i) //= !mxE eqxx /=.
rewrite eq_sym mulr_natr big1 ?addr0 // => i' ne_i'i.
by rewrite !mxE eq_sym (negbTE ne_i'i) mulr0.
Qed.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Section ScalarMx.

Variable n : nat.

Definition scalar_mx x : 'M[R]_n := \matrix_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma diag_const_mx : forall a, diag_mx (const_mx a) = a%:M :> 'M_n.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_scalar_mx : forall a, (a%:M)^T = a%:M.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma trmx1 : (1%:M)^T = 1%:M. Proof. exact: tr_scalar_mx. Qed.

Lemma scalar_mx_is_additive : additive scalar_mx.
Proof. by move=> a b; rewrite -!diag_const_mx !raddf_sub. Qed.
Canonical Structure scalar_mx_additive := Additive scalar_mx_is_additive.

Lemma scale_scalar_mx : forall a1 a2, a1 *: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof. by move=> a1 a2; apply/matrixP=> i j; rewrite !mxE mulrnAr. Qed.

Lemma scalemx1 : forall a, a *: 1%:M = a%:M.
Proof. by move=> a; rewrite scale_scalar_mx mulr1. Qed.

Lemma scalar_mx_sum_delta : forall a, a%:M = \sum_i a *: delta_mx i i.
Proof.
move=> a; rewrite -diag_const_mx diag_mx_sum_delta.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mx1_sum_delta : 1%:M = \sum_i delta_mx i i.
Proof. by rewrite [1%:M]scalar_mx_sum_delta -scaler_sumr scale1r. Qed.

Lemma row1 : forall i, row i 1%:M = delta_mx 0 i.
Proof. by move=> i; apply/rowP=> j; rewrite !mxE eq_sym. Qed.

Definition is_scalar_mx (A : 'M[R]_n) :=
  if insub 0%N is Some i then A == (A i i)%:M else true.

Lemma is_scalar_mxP : forall A, reflect (exists a, A = a%:M) (is_scalar_mx A).
Proof.
rewrite /is_scalar_mx; case: insubP => [i _ _ A | ].
  by apply: (iffP eqP) => [|[a ->]]; [exists (A i i) | rewrite mxE eqxx].
rewrite -eqn0Ngt; move/eqP=> n0 A; left; exists 0.
by rewrite raddf0; rewrite n0 in A *; rewrite [A]flatmx0.
Qed.

Lemma scalar_mx_is_scalar : forall a, is_scalar_mx a%:M.
Proof. by move=> a; apply/is_scalar_mxP; exists a. Qed.

Lemma mx0_is_scalar : is_scalar_mx 0.
Proof. by apply/is_scalar_mxP; exists 0; rewrite raddf0. Qed.

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma mx11_scalar : forall A : 'M_1, A = (A 0 0)%:M.
Proof. by move=> A; apply/rowP=> j; rewrite [j]ord1 mxE. Qed.

Lemma scalar_mx_block : forall n1 n2 a,
  a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
move=> n1 n2 a; apply/matrixP=> i j; rewrite !mxE -val_eqE /=.
by do 2![case: splitP => ? ->; rewrite !mxE];
  rewrite ?eqn_addl // -?(eq_sym (n1 + _)%N) eqn_leq leqNgt lshift_subproof.
Qed.

(* Matrix multiplication using bigops. *)
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA : forall m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)),
  A *m (B *m C) = A *m B *m C.
Proof.
move=> m n p q A B C; apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j * (B j k * C k l)))).
by apply: eq_bigr => j _; rewrite mxE big_distrr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Lemma mul0mx : forall m n p (A : 'M_(n, p)), 0 *m A = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k.
by rewrite !mxE big1 //= => j _; rewrite mxE mul0r.
Qed.

Lemma mulmx0 : forall m n p (A : 'M_(m, n)), A *m 0 = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxE big1 // => j _.
by rewrite mxE mulr0.
Qed.

Lemma mulmxN : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m (- B) = - (A *m B).
Proof.
move=> m n p A B; apply/matrixP=> i k; rewrite !mxE -sumr_opp.
by apply: eq_bigr => j _; rewrite mxE mulrN.
Qed.

Lemma mulNmx : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  - A *m B = - (A *m B).
Proof.
move=> m n p A B; apply/matrixP=> i k; rewrite !mxE -sumr_opp.
by apply: eq_bigr => j _; rewrite mxE mulNr.
Qed.

Lemma mulmx_addl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Proof.
move=> m n p A1 A2 B; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE -mulr_addl.
Qed.

Lemma mulmx_addr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 + B2) = A *m B1 + A *m B2.
Proof.
move=> m n p A B1 B2; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite mxE mulr_addr.
Qed.

Lemma mulmx_subl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 - A2) *m B = A1 *m B - A2 *m B.
Proof. by move=> m n p A1 A2 B; rewrite mulmx_addl mulNmx. Qed.

Lemma mulmx_subr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 - B2) = A *m B1 - A *m B2.
Proof. by move=> m n p A1 A2 B; rewrite mulmx_addr mulmxN. Qed.

Lemma mulmx_suml : forall m n p (A : 'M_(n, p)) I r P (B_ : I -> 'M_(m, n)),
   (\sum_(i <- r | P i) B_ i) *m A = \sum_(i <- r | P i) B_ i *m A.
Proof.
move=> m n p A; apply: (big_morph (mulmx^~ A)) => [B C|]; last exact: mul0mx.
by rewrite mulmx_addl.
Qed.

Lemma mulmx_sumr : forall m n p (A : 'M_(m, n)) I r P (B_ : I -> 'M_(n, p)),
   A *m (\sum_(i <- r | P i) B_ i) = \sum_(i <- r | P i) A *m B_ i.
Proof.
move=> m n p A; apply: (big_morph (mulmx A)) => [B C|]; last exact: mulmx0.
by rewrite mulmx_addr.
Qed.

Lemma scalemxAl : forall m n p a (A : 'M_(m, n)) (B : 'M_(n, p)),
  a *: (A *m B) = (a *: A) *m B.
Proof.
move=> m n p a A B; apply/matrixP=> i k; rewrite !mxE big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxE.
Qed.
(* Right scaling associativity requires a commutative ring *)

Lemma rowE : forall m n i (A : 'M_(m, n)), row i A = delta_mx 0 i *m A.
Proof.
move=> m n i A; apply/rowP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mul1r.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mul0r.
Qed.

Lemma row_mul : forall m n p (i : 'I_m) A (B : 'M_(n, p)),
  row i (A *m B) = row i A *m B.
Proof. by move=> m n p i A B; rewrite !rowE mulmxA. Qed.

Lemma mulmx_sum_row : forall m n (u : 'rV_m) (A : 'M_(m, n)),
  u *m A = \sum_i u 0 i *: row i A.
Proof.
move=> m n u A; apply/rowP=> j; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

Lemma mul_delta_mx_cond : forall m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p),
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
Proof.
move=> m n p j1 j2 i1 k2; apply/matrixP=> i k; rewrite !mxE (bigD1 j1) //=.
rewrite mulmxnE !mxE !eqxx andbT -natr_mul -mulrnA !mulnb !andbA andbAC.
by rewrite big1 ?addr0 // => j; rewrite !mxE andbC -natr_mul; move/negbTE->.
Qed.

Lemma mul_delta_mx : forall m n p (j : 'I_n) (i : 'I_m) (k : 'I_p),
  delta_mx i j *m delta_mx j k = delta_mx i k.
Proof. by move=> m n p j i k; rewrite mul_delta_mx_cond eqxx. Qed.

Lemma mul_delta_mx_0 : forall m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p),
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
Proof.
by move=> m n p j1 j2 i1 k2; rewrite mul_delta_mx_cond; move/negbTE->.
Qed.

Lemma mul_diag_mx : forall m n d (A : 'M_(m, n)),
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
move=> m n d A; apply/matrixP=> i j.
rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAl; move/negbTE->.
Qed.

Lemma mul_mx_diag : forall m n (A : 'M_(m, n)) d,
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
move=> m n A d; apply/matrixP=> i j.
rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAr; move/negbTE->.
Qed.

Lemma mulmx_diag : forall n (d e : 'rV_n),
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
Proof.
by move=> n d e; apply/matrixP=> i j; rewrite mul_diag_mx !mxE mulrnAr.
Qed.

Lemma mul_scalar_mx : forall m n a (A : 'M_(m, n)), a%:M *m A = a *: A.
Proof.
move=> m n a A; rewrite -diag_const_mx mul_diag_mx.
by apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma scalar_mxM : forall n a b, (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof. by move=> n a b; rewrite mul_scalar_mx scale_scalar_mx. Qed.

Lemma mul1mx : forall m n (A : 'M_(m, n)), 1%:M *m A = A.
Proof. by move=> m n A; rewrite mul_scalar_mx scale1r. Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m 1%:M = A.
Proof.
move=> m n A; rewrite -diag_const_mx mul_mx_diag.
by apply/matrixP=> i j; rewrite !mxE mulr1.
Qed.

Lemma mul_col_perm : forall m n p s (A : 'M_(m, n)) (B : 'M_(n, p)),
  col_perm s A *m B = A *m row_perm s^-1 B.
Proof.
move=> m n p s A B; apply/matrixP=> i k; rewrite !mxE.
rewrite (reindex_inj (@perm_inj _ s^-1)); apply: eq_bigr => j _ /=.
by rewrite !mxE permKV.
Qed.

Lemma mul_row_perm : forall m n p s (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m row_perm s B = col_perm s^-1 A *m B.
Proof. by move=> m n p s A B; rewrite mul_col_perm invgK. Qed.

Lemma mul_xcol : forall m n p j1 j2 (A : 'M_(m, n)) (B : 'M_(n, p)),
  xcol j1 j2 A *m B = A *m xrow j1 j2 B.
Proof. by move=> m n p j1 j2 A B; rewrite mul_col_perm tpermV. Qed.

(* Permutation matrix *)

Definition perm_mx n s : 'M_n := row_perm s 1%:M.

Definition tperm_mx n i1 i2 : 'M_n := perm_mx (tperm i1 i2).

Lemma col_permE : forall m n s (A : 'M_(m, n)),
  col_perm s A = A *m perm_mx s^-1.
Proof. by move=> m n s A; rewrite mul_row_perm mulmx1 invgK. Qed.

Lemma row_permE : forall m n s (A : 'M_(m, n)), row_perm s A = perm_mx s *m A.
Proof.
move=> m n s a; rewrite -[perm_mx _]mul1mx mul_row_perm mulmx1.
by rewrite -mul_row_perm mul1mx.
Qed.

Lemma xcolE : forall m n j1 j2 (A : 'M_(m, n)),
  xcol j1 j2 A = A *m tperm_mx j1 j2.
Proof. by move=> m n j1 j2 A; rewrite /xcol col_permE tpermV. Qed.

Lemma xrowE : forall m n i1 i2 (A : 'M_(m, n)),
  xrow i1 i2 A = tperm_mx i1 i2 *m A.
Proof. by move=> m n i1 i2 A; exact: row_permE. Qed.

Lemma tr_perm_mx : forall n (s : 'S_n), (perm_mx s)^T = perm_mx s^-1.
Proof.
by move=> n s; rewrite -[_^T]mulmx1 tr_row_perm mul_col_perm trmx1 mul1mx.
Qed.

Lemma tr_tperm_mx : forall n i1 i2, (tperm_mx i1 i2)^T = tperm_mx i1 i2 :> 'M_n.
Proof. by move=> n i1 i2; rewrite tr_perm_mx tpermV. Qed.

Lemma perm_mx1 : forall n, perm_mx 1 = 1%:M :> 'M_n.
Proof. move=> n; exact: row_perm1. Qed.

Lemma perm_mxM : forall n (s t : 'S_n),
  perm_mx (s * t) = perm_mx s *m perm_mx t.
Proof. by move=> n s t; rewrite -row_permE -row_permM. Qed.

Definition is_perm_mx n (A : 'M_n) := existsb s, A == perm_mx s.

Lemma is_perm_mxP : forall n (A : 'M_n),
  reflect (exists s, A = perm_mx s) (is_perm_mx A).
Proof. by move=> n A; apply: (iffP existsP) => [] [s]; move/eqP; exists s. Qed.

Lemma perm_mx_is_perm : forall n (s : 'S_n), is_perm_mx (perm_mx s).
Proof. by move=> n s; apply/is_perm_mxP; exists s. Qed.

Lemma is_perm_mx1 : forall n, is_perm_mx (1%:M : 'M_n).
Proof. by move=> n; rewrite -perm_mx1 perm_mx_is_perm. Qed.

Lemma is_perm_mxMl : forall n (A B : 'M_n),
  is_perm_mx A -> is_perm_mx (A *m B) = is_perm_mx B.
Proof.
move=> n A B; case/is_perm_mxP=> s ->.
apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; last first.
  by exists (s * t)%g; rewrite perm_mxM.
exists (s^-1 * t)%g.
by rewrite perm_mxM -def_t -!row_permE -row_permM mulVg row_perm1.
Qed.

Lemma is_perm_mx_tr : forall n (A : 'M_n), is_perm_mx A^T = is_perm_mx A.
Proof.
move=> n A; apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; exists t^-1%g.
  by rewrite -tr_perm_mx -def_t trmxK.
by rewrite tr_perm_mx.
Qed.

Lemma is_perm_mxMr : forall n (A B : 'M_n),
  is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.
Proof.
move=> n A B; case/is_perm_mxP=> s ->.
rewrite -[s]invgK -col_permE -is_perm_mx_tr tr_col_perm row_permE.
by rewrite is_perm_mxMl (perm_mx_is_perm, is_perm_mx_tr).
Qed.

(* Partial identity matrix (used in rank decomposition). *)

Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix_(i, j) ((i == j :> nat) && (i < r))%:R.

Lemma pid_mx_0 : forall m n, pid_mx 0 = 0 :> 'M_(m, n).
Proof. by move=> m n; apply/matrixP=> i j; rewrite !mxE andbF. Qed.

Lemma pid_mx_1 : forall r, pid_mx r = 1%:M :> 'M_r.
Proof. by move=> r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT. Qed.

Lemma pid_mx_row : forall n r, pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
Proof.
move=> n r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT.
case: splitP => j' ->; rewrite !mxE // .
by rewrite eqn_leq andbC leqNgt lshift_subproof.
Qed.

Lemma pid_mx_col : forall m r, pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
Proof.
move=> m r; apply/matrixP=> i j; rewrite !mxE andbC.
by case: splitP => i' ->; rewrite !mxE // eq_sym.
Qed.

Lemma pid_mx_block : forall m n r,
  pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
Proof.
move=> m n r; apply/matrixP=> i j; rewrite !mxE row_mx0 andbC.
case: splitP => i' ->; rewrite !mxE //; case: splitP => j' ->; rewrite !mxE //=.
by rewrite eqn_leq andbC leqNgt lshift_subproof.
Qed.

Lemma tr_pid_mx : forall m n r, (pid_mx r)^T = pid_mx r :> 'M_(n, m).
Proof.
by move=> m n r; apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->.
Qed.

Lemma pid_mx_minv : forall m n r, pid_mx (minn m r) = pid_mx r :> 'M_(m, n).
Proof. by move=> m n r; apply/matrixP=> i j; rewrite !mxE leq_minr ltn_ord. Qed.
 
Lemma pid_mx_minh : forall m n r, pid_mx (minn n r) = pid_mx r :> 'M_(m, n).
Proof. by move=> m n r; apply: trmx_inj; rewrite !tr_pid_mx pid_mx_minv. Qed.

Lemma mul_pid_mx : forall m n p q r,
  (pid_mx q : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx (minn n (minn q r)).
Proof.
move=> m n p q r; apply/matrixP=> i k; rewrite !mxE !leq_minr.
case: leqP => [le_n_i | lt_i_n].
  rewrite andbF big1 // => j _.
  by rewrite -pid_mx_minh !mxE leq_minr ltnNge le_n_i andbF mul0r.
rewrite (bigD1 (Ordinal lt_i_n)) //= big1 ?addr0 => [|j].
  by rewrite !mxE eqxx /= -natr_mul mulnb andbCA.
by rewrite -val_eqE /= !mxE eq_sym -natr_mul; move/negbTE=> ->.
Qed.

Lemma pid_mx_id : forall m n p r,
  r <= n -> (pid_mx r : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx r.
Proof. by move=> m n p r le_r_n; rewrite mul_pid_mx minnn minnr. Qed.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Lemma mul_copid_mx_pid : forall m n r,
  r <= m -> copid_mx r *m pid_mx r = 0 :> 'M_(m, n).
Proof. by move=> m n r le_r_m; rewrite mulmx_subl mul1mx pid_mx_id ?subrr. Qed.

Lemma mul_pid_mx_copid : forall m n r,
  r <= n -> pid_mx r *m copid_mx r = 0 :> 'M_(m, n).
Proof. by move=> m n r le_r_n; rewrite mulmx_subr mulmx1 pid_mx_id ?subrr. Qed.

Lemma copid_mx_id : forall n r,
  r <= n -> copid_mx r *m copid_mx r = copid_mx r :> 'M_n.
Proof.
by move=> n r le_r_n; rewrite mulmx_subl mul1mx mul_pid_mx_copid // oppr0 addr0.
Qed.

(* Block products; we cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)
Lemma mul_mx_row : forall m n p1 p2,
    forall (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)),
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
move=> m n p1 p2 A Bl Br; apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defk.
Qed.

Lemma mul_col_mx : forall m1 m2 n p,
    forall (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)),
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
Proof.
move=> m1 m2 n p Au Ad B; apply/matrixP=> i k; rewrite !mxE.
by case defi: (split i); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defi.
Qed.

Lemma mul_row_col : forall m n1 n2 p,
    forall (Al : 'M_(m, n1)) (Ar : 'M_(m, n2)),
    forall (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)),
  row_mx Al Ar *m col_mx Bu Bd = Al *m Bu + Ar *m Bd.
Proof.
move=> m n1 n2 p Al Ar Bu Bd.
apply/matrixP=> i k; rewrite !mxE big_split_ord /=.
congr (_ + _); apply: eq_bigr => j _; first by rewrite row_mxEl col_mxEu.
by rewrite row_mxEr col_mxEd.
Qed.

Lemma mul_col_row : forall m1 m2 n p1 p2,
    forall (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)),
    forall (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)),
  col_mx Au Ad *m row_mx Bl Br
     = block_mx (Au *m Bl) (Au *m Br) (Ad *m Bl) (Ad *m Br).
Proof. by move=> *; rewrite mul_col_mx !mul_mx_row. Qed.

Lemma mul_row_block : forall m n1 n2 p1 p2,
    forall (Al : 'M_(m, n1)) (Ar : 'M_(m, n2)),
    forall (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2)),
    forall (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)),
  row_mx Al Ar *m block_mx Bul Bur Bdl Bdr
   = row_mx (Al *m Bul + Ar *m Bdl) (Al *m Bur + Ar *m Bdr).
Proof. by move=> *; rewrite block_mxEh mul_mx_row !mul_row_col. Qed.

Lemma mul_block_col : forall m1 m2 n1 n2 p,
    forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
    forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
    forall (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)),
  block_mx Aul Aur Adl Adr *m col_mx Bu Bd
   = col_mx (Aul *m Bu + Aur *m Bd) (Adl *m Bu + Adr *m Bd).
Proof. by move=> *; rewrite mul_col_mx !mul_row_col. Qed.

Lemma mulmx_block : forall m1 m2 n1 n2 p1 p2,
    forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
    forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
    forall (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2)),
    forall (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)),
  block_mx Aul Aur Adl Adr *m block_mx Bul Bur Bdl Bdr
    = block_mx (Aul *m Bul + Aur *m Bdl) (Aul *m Bur + Aur *m Bdr)
               (Adl *m Bul + Adr *m Bdl) (Adl *m Bur + Adr *m Bdr).
Proof. by move=> *; rewrite mul_col_mx !mul_row_block. Qed.

(* Correspondance between matrices and linear function on row vectors. *) 
Section LinRowVector.

Variables m n : nat.

Definition lin1_mx (f : 'rV[R]_m -> 'rV[R]_n) :=
  \matrix_(i, j) f (delta_mx 0 i) 0 j.

Variable f : {linear 'rV[R]_m -> 'rV[R]_n}.

Lemma mul_rV_lin1 : forall u, u *m lin1_mx f = f u.
Proof.
move=> u; rewrite {2}[u]matrix_sum_delta big_ord1 linear_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite linearZ !mxE.
Qed.

End LinRowVector.

(* Correspondance between matrices and linear function on matrices. *) 
Section LinMatrix.

Variables m1 n1 m2 n2 : nat.

Definition lin_mx (f : 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)) :=
  lin1_mx (mxvec \o f \o vec_mx).

Variable f : {linear 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)}.

Lemma mul_rV_lin : forall u, u *m lin_mx f = mxvec (f (vec_mx u)).
Proof. exact: mul_rV_lin1. Qed.

Lemma mul_vec_lin : forall A, mxvec A *m lin_mx f = mxvec (f A).
Proof. by move=> A; rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_rV_lin : forall u, vec_mx (u *m lin_mx f) = f (vec_mx u).
Proof. by move=> A; rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_vec_lin : forall A, vec_mx (mxvec A *m lin_mx f) = f A.
Proof. by move=> A; rewrite mul_rV_lin !mxvecK. Qed.

End LinMatrix.

Canonical Structure mulmx_additive m n p A := Additive (@mulmx_subr m n p A).

Section Mulmxr.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Definition mulmxr_head t B A := let: tt := t in A *m B.
Local Notation mulmxr := (mulmxr_head tt).

Definition lin_mulmxr B := lin_mx (mulmxr B).

Lemma mulmxr_is_linear : forall B, linear (mulmxr B).
Proof. by move=> B a A1 A2; rewrite /= mulmx_addl scalemxAl. Qed.
Canonical Structure mulmxr_additive B := Additive (mulmxr_is_linear B).
Canonical Structure mulmxr_linear B := Linear (mulmxr_is_linear B).

Lemma lin_mulmxr_is_linear : linear lin_mulmxr.
Proof.
move=> a A B; apply/row_matrixP; case/mxvec_indexP=> i j.
rewrite linearP /= !rowE !mul_rV_lin /= vec_mx_delta -linearP mulmx_addr.
congr (mxvec (_ + _)); apply/row_matrixP=> k.
rewrite linearZ /= !row_mul rowE mul_delta_mx_cond.
by case: (k == i); [rewrite -!rowE linearZ | rewrite !mul0mx raddf0]. 
Qed.
Canonical Structure lin_mulmxr_additive := Additive lin_mulmxr_is_linear.
Canonical Structure lin_mulmxr_linear := Linear lin_mulmxr_is_linear.

End Mulmxr.

(* The trace. *)
Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr : forall A, \tr A^T = \tr A.
Proof. by move=> A; apply: eq_bigr=> i _; rewrite mxE. Qed.

Lemma mxtrace_is_linear : linear (mxtrace : 'M_n -> R^o).
Proof.
move=> a A B; rewrite raddf_sum -big_split /=; apply: eq_bigr=> i _.
by rewrite !mxE.
Qed.
Canonical Structure mxtrace_additive := Additive mxtrace_is_linear.
Canonical Structure mxtrace_linear := Linear mxtrace_is_linear.

Lemma mxtrace0 : \tr 0 = 0. Proof. exact: raddf0. Qed.

Lemma mxtraceD : forall A B, \tr (A + B) = \tr A + \tr B.
Proof. exact: raddfD. Qed.

Lemma mxtraceZ : forall a A, \tr (a *: A) = a * \tr A.
Proof. by move=> a A; rewrite linearZ. Qed.

Lemma mxtrace_diag : forall D, \tr (diag_mx D) = \sum_j D 0 j.
Proof. by move=> D; apply: eq_bigr => j _; rewrite mxE eqxx. Qed.

Lemma mxtrace_scalar : forall a, \tr a%:M = a *+ n.
Proof.
move=> a; rewrite -diag_const_mx mxtrace_diag.
by rewrite (eq_bigr _ (fun j _ => mxE _ 0 j)) sumr_const card_ord.
Qed.

Lemma mxtrace1 : \tr 1%:M = n%:R. Proof. exact: mxtrace_scalar. Qed.

End Trace.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma trace_mx11 : forall A : 'M_1, \tr A = A 0 0.
Proof. by move=> A; rewrite {1}[A]mx11_scalar mxtrace_scalar. Qed.

Lemma mxtrace_block : forall n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2),
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
move=> n1 n2 Aul Aur Adl Adr; rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite (block_mxEul, block_mxEdr).
Qed.

(* The matrix ring structure requires a strutural condition (dimension of the *)
(* form n.+1) to statisfy the nontriviality condition we have imposed.        *)
Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Proof.
by apply/eqP; move/matrixP; move/(_ 0 0); move/eqP; rewrite !mxE oner_eq0.
Qed.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmx_addl n n n) (@mulmx_addr n n n) matrix_nonzero1.

Canonical Structure matrix_ringType :=
  Eval hnf in RingType 'M[R]_n matrix_ringMixin.

Canonical Structure matrix_lAlgType :=
  Eval hnf in LalgType R 'M[R]_n (@scalemxAl n n n).

Lemma mulmxE : mulmx = *%R. Proof. by []. Qed.
Lemma idmxE : 1%:M = 1 :> 'M_n. Proof. by []. Qed.

Lemma scalar_mx_is_multiplicative : multiplicative (@scalar_mx n).
Proof. by split=> //; exact: scalar_mxM. Qed.
Canonical Structure scalar_mx_rmorphism :=
  AddRMorphism scalar_mx_is_multiplicative.

End MatrixRing.

Section LiftPerm.

(* Block expresssion of a lifted permutation matrix, for the Cormen LUP. *)

Variable n : nat.

(* These could be in zmodp, but that would introduce a dependency on perm. *)

Definition lift0_perm s : 'S_n.+1 := lift_perm 0 0 s.

Lemma lift0_perm0 : forall s, lift0_perm s 0 = 0.
Proof. by move=> s; exact: lift_perm_id. Qed.

Lemma lift0_perm_lift : forall s k',
  lift0_perm s (lift 0 k') = lift (0 : 'I_n.+1) (s k').
Proof. by move=> s i; exact: lift_perm_lift. Qed.

Lemma lift0_permK : forall s, cancel (lift0_perm s) (lift0_perm s^-1).
Proof. by move=> s i; rewrite /lift0_perm -lift_permV permK. Qed.

Lemma lift0_perm_eq0 : forall s i, (lift0_perm s i == 0) = (i == 0).
Proof. by move=> s i; rewrite (canF_eq (lift0_permK s)) lift0_perm0. Qed.

(* Block expresssion of a lifted permutation matrix *)

Definition lift0_mx A : 'M_(1 + n) := block_mx 1 0 0 A.

Lemma lift0_mx_perm : forall s, lift0_mx (perm_mx s) = perm_mx (lift0_perm s).
Proof.
move=> s; apply/matrixP=> /= i j.
rewrite !mxE split1 /=; case: unliftP => [i'|] -> /=.
  rewrite lift0_perm_lift !mxE split1 /=.
  by case: unliftP => [j'|] ->; rewrite ?(inj_eq (@lift_inj _ _)) /= !mxE.
rewrite lift0_perm0 !mxE split1 /=.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma lift0_mx_is_perm : forall s, is_perm_mx (lift0_mx (perm_mx s)).
Proof. by move=> s; rewrite lift0_mx_perm perm_mx_is_perm. Qed.

End LiftPerm.

(* Determinants and adjugates are defined here, but most of their properties *)
(* only hold for matrices over a commutative ring, so their theory is        *)
(* deferred to that section.                                                 *)

(* The determinant, in one line with the Leibniz Formula *)
Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

(* The cofactor of a matrix on the indexes i and j *)
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Definition adjugate n (A : 'M_n) := \matrix_(i, j) cofactor A j i.

End MatrixAlgebra.

Implicit Arguments delta_mx [R m n].
Implicit Arguments scalar_mx [R n].
Implicit Arguments perm_mx [R n].
Implicit Arguments tperm_mx [R n].
Implicit Arguments pid_mx [R m n].
Implicit Arguments copid_mx [R n].
Implicit Arguments lin_mulmxr [R m n p].
Prenex Implicits delta_mx diag_mx scalar_mx is_scalar_mx perm_mx tperm_mx.
Prenex Implicits pid_mx copid_mx mulmx lin_mulmxr.
Prenex Implicits mxtrace determinant cofactor adjugate.

Implicit Arguments is_scalar_mxP [R n A].
Implicit Arguments mul_delta_mx [R m n p].
Prenex Implicits mul_delta_mx.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation mulmxr := (mulmxr_head tt).
Notation "\tr A" := (mxtrace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

(* Non-commutative transpose requires multiplication in the converse ring.   *)
Lemma trmx_mul_rev : forall (R : ringType) m n p,
    forall (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)),
  (A *m B)^T = (B : 'M[R^c]_(n, p))^T *m (A : 'M[R^c]_(m, n))^T.
Proof.
move=> R m n p /= A B; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite !mxE.
Qed.

Canonical Structure matrix_finRingType (R : finRingType) n' :=
  Eval hnf in [finRingType of 'M[R]_n'.+1].

(* Parametricity over the algebra structure. *)
Section MapRingMatrix.

Variables (aR rR : ringType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mxZ : forall a A, (a *: A)^f = f a *: A^f.
Proof. by move=> a A; apply/matrixP=> i j; rewrite !mxE rmorphM. Qed.

Lemma map_mxM : forall A B, (A *m B)^f = A^f *m B^f :> 'M_(m, p).
Proof.
move=> A B; apply/matrixP=> i k; rewrite !mxE rmorph_sum //.
by apply: eq_bigr => j; rewrite !mxE rmorphM.
Qed.

Lemma map_delta_mx : forall i j, (delta_mx i j)^f = delta_mx i j :> 'M_(m, n).
Proof. by move=> i j; apply/matrixP=> i' j'; rewrite !mxE rmorph_nat. Qed.

Lemma map_diag_mx : forall d, (diag_mx d)^f = diag_mx d^f :> 'M_n.
Proof. by move=> d; apply/matrixP=> i j; rewrite !mxE rmorphMn. Qed.

Lemma map_scalar_mx : forall a, a%:M^f = (f a)%:M :> 'M_n.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE rmorphMn. Qed.

Lemma map_mx1 : 1%:M^f = 1%:M :> 'M_n.
Proof. by rewrite map_scalar_mx rmorph1. Qed.

Lemma map_perm_mx : forall s : 'S_n, (perm_mx s)^f = perm_mx s.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE rmorph_nat. Qed.

Lemma map_tperm_mx : forall i1 i2 : 'I_n, (tperm_mx i1 i2)^f = tperm_mx i1 i2.
Proof. by move=> i j; exact: map_perm_mx. Qed.

Lemma map_pid_mx : forall r, (pid_mx r)^f = pid_mx r :> 'M_(m, n).
Proof. by move=> r; apply/matrixP=> i j; rewrite !mxE rmorph_nat. Qed.

Lemma trace_map_mx : forall A : 'M_n, \tr A^f = f (\tr A).
Proof. by move=> A; rewrite rmorph_sum; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma det_map_mx : forall n' (A : 'M_n'), \det A^f = f (\det A).
Proof.
move=> n' A; rewrite rmorph_sum //; apply: eq_bigr => s _.
rewrite rmorphM rmorph_sign rmorph_prod; congr (_ * _).
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma cofactor_map_mx : forall (A : 'M_n) i j,
  cofactor A^f i j = f (cofactor A i j).
Proof.
by move=> A i j; rewrite rmorphM rmorph_sign -det_map_mx map_row' map_col'.
Qed.

Lemma map_mx_adj : forall A : 'M_n, (\adj A)^f = \adj A^f.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE cofactor_map_mx. Qed.

End FixedSize.

Lemma map_copid_mx : forall n r, (copid_mx r)^f = copid_mx r :> 'M_n.
Proof. by move=> n r; rewrite map_mx_sub map_mx1 map_pid_mx. Qed.

Lemma map_mx_is_multiplicative : forall n' (n := n'.+1),
  multiplicative ((map_mx f) n n).
Proof. by move=> n'; split; [exact: map_mxM | exact: map_mx1]. Qed.

Canonical Structure map_mx_rmorphism n' :=
  AddRMorphism (map_mx_is_multiplicative n').

Lemma map_lin1_mx : forall m n (g : 'rV_m -> 'rV_n) gf, 
  (forall v, (g v)^f = gf v^f) -> (lin1_mx g)^f = lin1_mx gf.
Proof.
move=> m n g gf def_gf; apply/matrixP=> i j.
by rewrite !mxE -map_delta_mx -def_gf mxE.
Qed.

Lemma map_lin_mx : forall m1 n1 m2 n2 (g : 'M_(m1, n1) -> 'M_(m2, n2)) gf, 
  (forall A, (g A)^f = gf A^f) -> (lin_mx g)^f = lin_mx gf.
Proof.
move=> m1 n1 m2 n2 g gf def_gf; apply: map_lin1_mx => A /=.
by rewrite map_mxvec def_gf map_vec_mx.
Qed.

End MapRingMatrix.

Section ComMatrix.
(* Lemmas for matrices with coefficients in a commutative ring *)
Variable R : comRingType.

Section AssocLeft.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Lemma trmx_mul : forall A B, (A *m B)^T = B^T *m A^T.
Proof.
move=> A B; rewrite trmx_mul_rev; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Lemma scalemxAr : forall a A B, a *: (A *m B) = A *m (a *: B).
Proof.
move=> a A B; apply: trmx_inj.
by rewrite trmx_mul !linearZ /= trmx_mul scalemxAl.
Qed.

Lemma mulmx_is_scalable : forall A, scalable (@mulmx _ m n p A).
Proof. by move=> A a B; rewrite scalemxAr. Qed.
Canonical Structure mulmx_linear A := AddLinear (mulmx_is_scalable A).

Definition lin_mulmx A : 'M[R]_(n * p, m * p) := lin_mx (mulmx A).

Lemma lin_mulmx_is_linear : linear lin_mulmx.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)) linearP.
Qed.
Canonical Structure lin_mulmx_additive := Additive lin_mulmx_is_linear.
Canonical Structure lin_mulmx_linear := Linear lin_mulmx_is_linear.

End AssocLeft.

Section LinMulRow.

Variables m n : nat.

Definition lin_mul_row u : 'M[R]_(m * n, n) := lin1_mx (mulmx u \o vec_mx).

Lemma lin_mul_row_is_linear : linear lin_mul_row.
Proof.
move=> a u v; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin1 /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)).
Qed.
Canonical Structure lin_mul_row_additive := Additive lin_mul_row_is_linear.
Canonical Structure lin_mul_row_linear := Linear lin_mul_row_is_linear.

Lemma mul_vec_lin_row : forall A u, mxvec A *m lin_mul_row u = u *m A.
Proof. by move=> A u; rewrite mul_rV_lin1 /= mxvecK. Qed.

End LinMulRow.

Section MatrixAlgType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical Structure matrix_algType :=
  Eval hnf in AlgType R 'M[R]_n (fun k => scalemxAr k).

End MatrixAlgType.

Lemma diag_mxC : forall n (d e : 'rV[R]_n),
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
Proof.
move=> n d e; rewrite !mulmx_diag; congr (diag_mx _).
by apply/rowP=> i; rewrite !mxE mulrC.
Qed.

Lemma diag_mx_comm : forall n' (d e : 'rV[R]_n'.+1),
  GRing.comm (diag_mx d) (diag_mx e).
Proof. move=> n'; exact: diag_mxC. Qed.

Lemma scalar_mxC : forall m n a (A : 'M[R]_(m, n)), A *m a%:M = a%:M *m A.
Proof.
move=> m n a A; apply: trmx_inj.
by rewrite trmx_mul tr_scalar_mx !mul_scalar_mx linearZ.
Qed.

Lemma scalar_mx_comm : forall n' a (A : 'M[R]_n'.+1), GRing.comm A a%:M.
Proof. move=> n; exact: scalar_mxC. Qed.

Lemma mul_mx_scalar : forall m n a (A : 'M[R]_(m, n)), A *m a%:M = a *: A.
Proof. by move=> m n a A; rewrite scalar_mxC mul_scalar_mx. Qed.

Lemma mxtrace_mulC : forall m n (A : 'M[R]_(m, n)) (B : 'M_(n, m)),
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B; transitivity (\sum_i \sum_j A i j * B j i).
  by apply: eq_bigr => i _; rewrite mxE.
rewrite exchange_big; apply: eq_bigr => i _ /=; rewrite mxE.
apply: eq_bigr => j _; exact: mulrC.
Qed.

(* The theory of determinants *)

Lemma determinant_multilinear : forall n (A B C : 'M[R]_n) i0 b c,
    row i0 A = b *: row i0 B + c *: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c; rewrite -[_ + _](row_id 0); move/row_eq=> ABC.
move/row'_eq=> BA; move/row'_eq=> CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulr_addr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //= {}ABC !mxE mulr_addl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i i0i; rewrite ?BA ?CA.
Qed.

Lemma determinant_alternate : forall n (A : 'M[R]_n) i1 i2,
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> n A i1 i2 Di12 A12; pose t := tperm i1 i2.
have oddMt: forall s, (t * s)%g = ~~ s :> bool.
  by move=> s; rewrite odd_permM odd_tperm Di12.
rewrite /(\det _) (bigID (@odd_perm _)) /=.
apply: canLR (subrK _) _; rewrite add0r -sumr_opp.
rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
rewrite oddMt; move/negPf->; rewrite mulN1r mul1r; congr (- _).
rewrite (reindex_inj (@perm_inj _ t)); apply: eq_bigr => /= i _.
by rewrite permM tpermK /t; case: tpermP => // ->; rewrite A12.
Qed.

Lemma det_tr : forall n (A : 'M[R]_n), \det A^T = \det A.
Proof.
move=> n A; rewrite /(\det _) (reindex_inj (@invg_inj _)) /=.
apply: eq_bigr => s _ /=; rewrite !odd_permV (reindex_inj (@perm_inj _ s)) /=.
by congr (_ * _); apply: eq_bigr => i _; rewrite mxE permK.
Qed.

Lemma det_perm : forall n (s : 'S_n), \det (perm_mx s) = (-1) ^+ s :> R.
Proof.
move=> n s; rewrite /(\det _) (bigD1 s) //=.
rewrite big1 => [|i _]; last by rewrite /= !mxE eqxx.
rewrite mulr1 big1 ?addr0 => //= t Dst.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= !mxE (negbTE ist) mul0r.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma det1 : forall n, \det (1%:M : 'M[R]_n) = 1.
Proof. by move=> n; rewrite -perm_mx1 det_perm odd_perm1. Qed.

Lemma det_scalemx : forall n x (A : 'M[R]_n), \det (x *: A) = x ^+ n * \det A.
Proof.
move=> n x A; rewrite big_distrr /=; apply: eq_bigr => s _.
rewrite mulrCA; congr (_ * _).
rewrite -{10}[n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxE.
Qed.

Lemma det0 : forall n', \det (0 : 'M[R]_n'.+1) = 0.
Proof. by move=> n'; rewrite -(scale0r 0) det_scalemx exprS !mul0r. Qed.

Lemma det_scalar : forall n a, \det (a%:M : 'M[R]_n) = a ^+ n.
Proof.
by move=> n a; rewrite -{1}(mulr1 a) -scale_scalar_mx det_scalemx det1 mulr1.
Qed.

Lemma det_scalar1 : forall a, \det (a%:M : 'M[R]_1) = a.
Proof. exact: det_scalar. Qed.

Lemma det_mulmx : forall n (A B : 'M[R]_n), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite big_distrl /=.
pose F := {ffun 'I_n -> 'I_n}; pose AB s i j := A i j * B j (s i).
transitivity (\sum_(f : F) \sum_(s : 'S_n) (-1) ^+ s * \prod_i AB s i (f i)).
  rewrite exchange_big; apply: eq_bigr => /= s _; rewrite -big_distrr /=.
  congr (_ * _); rewrite -(bigA_distr_bigA (AB s)) /=.
  by apply: eq_bigr => x _; rewrite mxE.
rewrite (bigID (fun f : F => injectiveb f)) /= addrC big1 ?add0r => [|f Uf].
  rewrite (reindex (@pval _)) /=; last first.
    pose in_Sn := insubd (1%g : 'S_n).
    by exists in_Sn => /= f Uf; first apply: val_inj; exact: insubdK.
  apply: eq_big => /= [s | s _]; rewrite ?(valP s) // big_distrr /=.
  rewrite (reindex_inj (mulgI s)); apply: eq_bigr => t _ /=.
  rewrite big_split /= mulrA mulrCA mulrA mulrCA mulrA.
  rewrite -signr_addb odd_permM !pvalE; congr (_ * _); symmetry.
  by rewrite (reindex_inj (@perm_inj _ s)); apply: eq_bigr => i; rewrite permM.
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_i A i (f i)).
  rewrite mulrC big_distrr /=; apply: eq_bigr => s _.
  rewrite mulrCA big_split //=; congr (_ * (_ * _)).
  by apply: eq_bigr => x _; rewrite mxE.
case/injectivePn: Uf => i1 [i2 Di12 Ef12].
by rewrite (determinant_alternate Di12) ?simp //= => j; rewrite !mxE Ef12.
Qed.

Lemma detM : forall n' (A B : 'M[R]_n'.+1), \det (A * B) = \det A * \det B.
Proof. move=> n'; exact: det_mulmx. Qed.

Lemma det_diag : forall n (d : 'rV[R]_n), \det (diag_mx d) = \prod_i d 0 i.
Proof.
move=> n d; rewrite /(\det _) (bigD1 1%g) //= addrC big1 => [|p p1].
  by rewrite add0r odd_perm1 mul1r; apply: eq_bigr => i; rewrite perm1 mxE eqxx.
have{p1}: ~~ perm_on set0 p.
  apply: contra p1; move/subsetP=> p1; apply/eqP; apply/permP=> i.
  by rewrite perm1; apply/eqP; apply/idPn; move/p1; rewrite inE.
case/subsetPn=> i; rewrite !inE eq_sym; move/negbTE=> p_i _.
by rewrite (bigD1 i) //= mulrCA mxE p_i mul0r.
Qed.

(* Laplace expansion lemma *)
Lemma expand_cofactor : forall n (A : 'M[R]_n) i j,
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1) ^+ s * \prod_(k | i != k) A k (s k).
Proof.
move=> [_ [] //|n] A i0 j0; rewrite (reindex (lift_perm i0 j0)); last first.
  pose ulsf i (s : 'S_n.+1) k := odflt k (unlift (s i) (s (lift i k))).
  have ulsfK: forall i (s : 'S__) k, lift (s i) (ulsf i s k) = s (lift i k).
    rewrite /ulsf => i s k; have:= neq_lift i k.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1%g) _ => k'.
    by rewrite {1}/ulsf ulsfK !permK liftK.
  exists (fun s => perm (inj_ulsf s)) => [s _ | s].
    by apply/permP=> k'; rewrite permE /ulsf lift_perm_lift lift_perm_id liftK.
  move/(s _ =P _) => si0; apply/permP=> k.
  case: (unliftP i0 k) => [k'|] ->; rewrite ?lift_perm_id //.
  by rewrite lift_perm_lift -si0 permE ulsfK.
rewrite /cofactor big_distrr /=.
apply: eq_big => [s | s _]; first by rewrite lift_perm_id eqxx.
rewrite -signr_odd mulrA -signr_addb odd_add -odd_lift_perm; congr (_ * _).
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [j | i _]; first case/unlift_some=> i; have:= n0 i.
rewrite (reindex (lift i0)).
  by apply: eq_big => [k | k _] /=; rewrite ?neq_lift // !mxE lift_perm_lift.
exists (fun k => odflt k0 (unlift i0 k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Lemma expand_det_row : forall n (A : 'M[R]_n) i0,
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (partition_big (fun s : 'S_n => s i0) predT) //=.
apply: eq_bigr => j0 _; rewrite expand_cofactor big_distrr /=.
apply: eq_bigr => s; move/eqP=> Dsi0.
rewrite mulrCA (bigID (pred1 i0)) /= big_pred1_eq Dsi0; congr (_ * (_ * _)).
by apply: eq_bigl => i; rewrite eq_sym.
Qed.

Lemma cofactor_tr : forall n (A : 'M[R]_n) i j,
  cofactor A^T i j = cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC; congr (_ * _).
rewrite -tr_row' -tr_col' det_tr; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxE.
Qed.

Lemma expand_det_col : forall n (A : 'M[R]_n) j0,
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -det_tr (expand_det_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxE.
Qed.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj : forall n (A : 'M[R]_n), A *m \adj A = (\det A)%:M.
Proof.
move=> n A; apply/matrixP=> i1 i2; rewrite !mxE; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE Di eq_refl.
rewrite -[_ *+ _](determinant_alternate (negbT Di) EBi12) (expand_det_row _ i2).
apply: eq_bigr => j _; rewrite !mxE eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxE eq_sym -if_neg neq_lift.
Qed.

Lemma trmx_adj : forall n (A : 'M[R]_n), (\adj A)^T = \adj A^T.
Proof. by move=> n A; apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

(* Cramer rule : adjugate on the right *)
Lemma mul_adj_mx : forall n (A : 'M[R]_n), \adj A *m A = (\det A)%:M.
Proof.
move=> n A; apply: trmx_inj; rewrite trmx_mul trmx_adj mul_mx_adj.
by rewrite det_tr tr_scalar_mx.
Qed.

(* Left inverses are right inverses. *)
Lemma mulmx1C : forall n (A B : 'M[R]_n), A *m B = 1%:M -> B *m A = 1%:M.
Proof.
move=> n A B AB1; pose A' := \det B *: \adj A.
suffices kA: A' *m A = 1%:M by rewrite -[B]mul1mx -kA -(mulmxA A') AB1 mulmx1.
by rewrite -scalemxAl mul_adj_mx scale_scalar_mx mulrC -det_mulmx AB1 det1.
Qed.

(* Only tall matrices have inverses. *)
Lemma mulmx1_min : forall m n (A : 'M[R]_(m, n)) B, A *m B = 1%:M -> m <= n.
Proof.
move=> m n A B AB1; rewrite leqNgt; apply/negP; move/subnKC; rewrite addSnnS.
move: (_ - _)%N => m' def_m; move: AB1; rewrite -{m}def_m in A B *.
rewrite -(vsubmxK A) -(hsubmxK B) mul_col_row scalar_mx_block.
case/eq_block_mx; move/mulmx1C=> BlAu1 AuBr0 _; move/eqP; case/idPn.
by rewrite -[_ B]mul1mx -BlAu1 -mulmxA AuBr0 !mulmx0 eq_sym nonzero1r.
Qed.

Lemma det_ublock : forall n1 n2 Aul (Aur : 'M[R]_(n1, n2)) Adr,
  \det (block_mx Aul Aur 0 Adr) = \det Aul * \det Adr.
Proof.
move=> n1 n2 Aul Aur Adr; elim: n1 => [|n1 IHn1] in Aul Aur *.
  have ->: Aul = 1%:M by apply/matrixP=> i [].
  rewrite det1 mul1r; congr (\det _); apply/matrixP=> i j.
  by do 2![rewrite !mxE; case: splitP => [[]|k] //=; move/val_inj=> <- {k}].
rewrite (expand_det_col _ (lshift n2 0)) big_split_ord /=.
rewrite addrC big1 1?simp => [|i _]; last by rewrite block_mxEdl mxE simp.
rewrite (expand_det_col _ 0) big_distrl /=; apply eq_bigr=> i _.
rewrite block_mxEul -!mulrA; do 2!congr (_ * _).
by rewrite col'_col_mx !col'Kl raddf0 row'Ku row'_row_mx IHn1.
Qed.

Lemma det_lblock : forall n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr,
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof. by move=> *; rewrite -det_tr tr_block_mx trmx0 det_ublock !det_tr. Qed.

End ComMatrix.

Implicit Arguments lin_mul_row [R m n].
Implicit Arguments lin_mulmx [R m n p].
Prenex Implicits lin_mul_row lin_mulmx.

(*****************************************************************************)
(********************** Matrix unit ring and inverse matrices ****************)
(*****************************************************************************)

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.

Definition unitmx : pred 'M[R]_n := fun A => GRing.unit (\det A).
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma unitmxE : forall A, (A \in unitmx) = GRing.unit (\det A).
Proof. by []. Qed.

Lemma unitmx1 : 1%:M \in unitmx. Proof. by rewrite unitmxE det1 unitr1. Qed.

Lemma unitmx_perm : forall s, perm_mx s \in unitmx.
Proof. by move=> s; rewrite unitmxE det_perm unitr_exp ?unitr_opp ?unitr1. Qed.

Lemma unitmx_tr : forall A, (A^T \in unitmx) = (A \in unitmx).
Proof. by move=> A; rewrite unitmxE det_tr. Qed.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAl mul_adj_mx scale_scalar_mx mulVr.
Qed.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAr mul_mx_adj scale_scalar_mx mulVr.
Qed.

Lemma mulKmx : forall m, {in unitmx, @left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite mulmxA mulVmx ?mul1mx. Qed.

Lemma mulKVmx : forall m, {in unitmx, @rev_left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite mulmxA mulmxV ?mul1mx. Qed.

Lemma mulmxK : forall m, {in unitmx, @right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite -mulmxA mulmxV ?mulmx1. Qed.

Lemma mulmxKV : forall m, {in unitmx, @rev_right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite -mulmxA mulVmx ?mulmx1. Qed.

Lemma det_inv : forall A, \det (invmx A) = (\det A)^-1.
Proof.
move=> A; case uA: (A \in unitmx); last by rewrite /invmx uA invr_out ?negbT.
by apply: (mulrI uA); rewrite -det_mulmx mulmxV ?divrr ?det1.
Qed.

Lemma unitmx_inv : forall A, (invmx A \in unitmx) = (A \in unitmx).
Proof. by move=> A; rewrite !unitmxE det_inv unitr_inv. Qed.

Lemma unitmx_mul : forall A B,
  (A *m B \in unitmx) = (A \in unitmx) && (B \in unitmx).
Proof. by move=> A B; rewrite -unitr_mul -det_mulmx. Qed.

Lemma trmx_inv : forall A : 'M_n, (invmx A)^T = invmx (A^T).
Proof.
by move=> A; rewrite (fun_if trmx) linearZ /= trmx_adj -unitmx_tr -det_tr.
Qed.

Lemma invmxK : involutive invmx.
Proof.
move=> A; case uA : (A \in unitmx); last by rewrite /invmx !uA.
by apply: (can_inj (mulKVmx uA)); rewrite mulVmx // mulmxV ?unitmx_inv.
Qed.

Lemma mulmx1_unit : forall A B, A *m B = 1%:M -> A \in unitmx /\ B \in unitmx.
Proof. by move=> A B AB1; apply/andP; rewrite -unitmx_mul AB1 unitmx1. Qed.

Lemma intro_unitmx : forall A B, B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Proof. by move=> A B [_]; case/mulmx1_unit. Qed.

Lemma invmx_out : {in predC unitmx, invmx =1 id}.
Proof. by move=> A; rewrite inE /= /invmx -if_neg => ->. Qed.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical Structure matrix_unitRing :=
  Eval hnf in UnitRingType 'M[R]_n matrix_unitRingMixin.

Canonical Structure matrix_unitAlg :=
  Eval hnf in [unitAlgType R of 'M[R]_n].

(* Lemmas requiring that the coefficients are in a unit ring *)

Lemma detV : forall A : 'M_n, \det A^-1 = (\det A)^-1.
Proof. exact: det_inv. Qed.

Lemma unitr_trmx : forall A : 'M_n, GRing.unit A^T = GRing.unit A.
Proof. exact: unitmx_tr. Qed.

Lemma trmxV : forall A : 'M_n, A^-1^T = (A^T)^-1.
Proof. exact: trmx_inv. Qed.

Lemma perm_mxV : forall s : 'S_n, perm_mx s^-1 = (perm_mx s)^-1.
Proof.
move=> s; rewrite -[_^-1]mul1r; apply: (canRL (mulmxK (unitmx_perm s))).
by rewrite -perm_mxM mulVg perm_mx1.
Qed.

Lemma is_perm_mxV : forall A : 'M_n, is_perm_mx A^-1 = is_perm_mx A.
Proof.
move=> A; apply/is_perm_mxP/is_perm_mxP=> [] [s defA]; exists s^-1%g.
  by rewrite -(invrK A) defA perm_mxV.
by rewrite defA perm_mxV.
Qed.

End MatrixInv.

Prenex Implicits unitmx invmx.

(* Finite inversible matrices and the general linear group. *)
Section FinUnitMatrix.

Variables (n : nat) (R : finComUnitRingType).

Canonical Structure matrix_finUnitRingType n' :=
  Eval hnf in [finUnitRingType of 'M[R]_n'.+1].

Definition GLtype of phant R := {unit 'M[R]_n.-1.+1}.

Coercion GLval ph (u : GLtype ph) : 'M[R]_n.-1.+1 :=
  let: FinRing.Unit A _ := u in A.

End FinUnitMatrix.

Bind Scope group_scope with GLtype.
Arguments Scope GLval [nat_scope _ _ group_scope].
Prenex Implicits GLval.

Notation "{ ''GL_' n [ R ] }" := (GLtype n (Phant R))
  (at level 0, n at level 2, format "{ ''GL_' n [ R ] }") : type_scope.
Notation "{ ''GL_' n ( p ) }" := {'GL_n['F_p]}
  (at level 0, n at level 2, p at level 10,
    format "{ ''GL_' n ( p ) }") : type_scope.

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

Canonical Structure GL_subType := [subType for @GLval n _ (Phant R)].
Definition GL_eqMixin := Eval hnf in [eqMixin of {'GL_n[R]} by <:].
Canonical Structure GL_eqType := Eval hnf in EqType {'GL_n[R]} GL_eqMixin.
Canonical Structure GL_choiceType := Eval hnf in [choiceType of {'GL_n[R]}].
Canonical Structure GL_countType := Eval hnf in [countType of {'GL_n[R]}].
Canonical Structure GL_subCountType :=
  Eval hnf in [subCountType of {'GL_n[R]}].
Canonical Structure GL_finType := Eval hnf in [finType of {'GL_n[R]}].
Canonical Structure GL_subFinType := Eval hnf in [subFinType of {'GL_n[R]}].
Canonical Structure GL_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of {'GL_n[R]}].
Canonical Structure GL_finGroupType :=
  Eval hnf in [finGroupType of {'GL_n[R]}].
Definition GLgroup of phant R := [set: {'GL_n[R]}].
Canonical Structure GLgroup_group ph := Eval hnf in [group of GLgroup ph].

Implicit Types u v : {'GL_n[R]}.

Lemma GL_1E : GLval 1 = 1. Proof. by []. Qed.
Lemma GL_VE : forall u, GLval u^-1 = (GLval u)^-1. Proof. by []. Qed.
Lemma GL_VxE : forall u, GLval u^-1 = invmx u. Proof. by []. Qed.
Lemma GL_ME : forall u v, GLval (u * v) = GLval u * GLval v. Proof. by []. Qed.
Lemma GL_MxE : forall u v, GLval (u * v) = u *m v. Proof. by []. Qed.
Lemma GL_unit : forall u, GRing.unit (GLval u). Proof. exact: valP. Qed.
Lemma GL_unitmx : forall u, val u \in unitmx. Proof. exact: GL_unit. Qed.

Lemma GL_det : forall u, \det u != 0.
Proof.
move=> u; apply: contraL (GL_unitmx u); rewrite unitmxE; move/eqP->.
by rewrite unitr0.
Qed.

End GL_unit.

Notation "''GL_' n [ R ]" := (GLgroup n (Phant R))
  (at level 8, n at level 2, format "''GL_' n [ R ]") : group_scope.
Notation "''GL_' n ( p )" := 'GL_n['F_p]
  (at level 8, n at level 2, p at level 10,
   format "''GL_' n ( p )") : group_scope.
Notation "''GL_' n [ R ]" := (GLgroup_group n (Phant R)) : subgroup_scope.
Notation "''GL_' n ( p )" := (GLgroup_group n (Phant 'F_p)) : subgroup_scope.

(* Parametricity at the field level (mx_is_scalar, unit and inverse are only *)
(* mapped at this level).                                                    *)
Section MapFieldMatrix.

Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_mx_inj : forall m n, injective ((map_mx f) m n).
Proof.
move=> m n A B; move/matrixP=> eq_AB; apply/matrixP=> i j.
by move/(_ i j): eq_AB; rewrite !mxE; exact: fmorph_inj.
Qed.

Lemma map_mx_is_scalar : forall n (A : 'M_n), is_scalar_mx A^f = is_scalar_mx A.
Proof.
move=> n A; rewrite /is_scalar_mx; case: (insub _) => // i.
by rewrite mxE -map_scalar_mx inj_eq //; exact: map_mx_inj.
Qed.

Lemma map_unitmx : forall n (A : 'M_n), (A^f \in unitmx) = (A \in unitmx).
Proof. by move=> n A; rewrite unitmxE det_map_mx // fmorph_unit // -unitfE. Qed.

Lemma map_mx_unit : forall n' (A : 'M_n'.+1), GRing.unit A^f = GRing.unit A.
Proof. by move=> n'; exact: map_unitmx. Qed.

Lemma map_invmx : forall n (A : 'M_n), (invmx A)^f = invmx A^f.
Proof.
move=> n A; rewrite /invmx map_unitmx (fun_if ((map_mx f) n n)).
by rewrite map_mxZ map_mx_adj det_map_mx fmorphV. 
Qed.

Lemma map_mx_inv : forall n' (A : 'M_n'.+1), A^-1^f = A^f^-1.
Proof. by move=> n'; exact: map_invmx. Qed.

Lemma map_mx_eq0 : forall m n (A : 'M_(m, n)), (A^f == 0) = (A == 0).
Proof. by move=> m n A; rewrite -(inj_eq (@map_mx_inj m n)) raddf0. Qed.

End MapFieldMatrix.

(*****************************************************************************)
(****************************** LUP decomposion ******************************)
(*****************************************************************************)

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with *)
(*   - P a permutation matrix                      *)
(*   - L a unipotent lower triangular matrix       *)
(*   - U an upper triangular matrix                *)

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Lemma cormen_lup_perm : forall n (A : 'M_n.+1), is_perm_mx (cormen_lup A).1.1.
Proof.
elim=> [| n IHn] A /=; first exact: is_perm_mx1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/=.
rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).
case/is_perm_mxP => s ->; exact: lift0_mx_is_perm.
Qed.

Lemma cormen_lup_correct : forall n (A : 'M_n.+1),
  let: (P, L, U) := cormen_lup A in P * A = L * U.
Proof.
elim=> [|n IHn] A /=; first by rewrite !mul1r.
set k := odflt _ _; set A1 : 'M_(1 + _) := xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P' L' U']] /= IHn.
rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulr_addr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL : forall n (A : 'M_n.+1), \det (cormen_lup A).1.2 = 1.
Proof.
elim=> [|n IHn] A /=; first by rewrite det1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower : forall n A (i j : 'I_n.+1),
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
Proof.
elim=> [|n IHn] A /= i j; first by rewrite [i]ord1 [j]ord1 mxE.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; exact: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper : forall n A (i j : 'I_n.+1),
  j < i -> (cormen_lup A).2 i j = 0 :> F.
Proof.
elim=> [|n IHn] A /= i j; first by rewrite [i]ord1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [exact: Uu | rewrite /= mxE].
Qed.

End CormenLUP.

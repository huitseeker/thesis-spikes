(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import Bool. (* For bool_scope delimiter 'bool'. *)

Declare ML Module "ssreflect".

(***************************************************************************)
(* This file is the Gallina part of the ssreflect plugin implementation.   *)
(* Files that use the ssreflect plugin should always Require ssreflect and *)
(* either Import ssreflect or Import ssreflect.SsrSyntax.                  *)
(*   The contents of this file is quite technical and should only interest *)
(* advanced developers; features not covered by the Ssreflect reference    *)
(* manual, such as the Unlockable interface, phantom types, and the        *)
(* [the struct of T] construct, are covered by specific comments below.    *)
(***************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SsrSyntax.

(* Declare Ssr keywords: 'is' 'by' 'of' '//' '/=' and '//='.                *)
(* We also declare the parsing level 8, as a workaround for a notation      *)
(* grammar factoring problem. Arguments of application-style notations      *)
(* (at level 10) should be declared at level 8 rather than 9 or the camlp4  *)
(* grammar will not factor properly.                                        *)

Reserved Notation "(* x 'is' y 'by' z 'of' // /= //= *)" (at level 8).
Reserved Notation "(* 69 *)" (at level 69).

End SsrSyntax.

Export SsrSyntax.

(* Make the general "if" into a notation, so that we can override it below *)
(* The notations are "only parsing" because the Coq decompiler won't       *)
(* recognize the expansion of the boolean if; using the default printer    *)
(* avoids a spurrious trailing %GEN_IF.                                    *)

Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c then v1 else v2)
  (at level 200, c, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c as x return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, x ident, only parsing)
     : general_if_scope.

(* Force boolean interpretation of simple if expressions.          *)

Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true in bool return t then v1 else v2) : boolean_if_scope.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c%bool is true in bool return _ then v1 else v2) : boolean_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true as x in bool return t then v1 else v2) : boolean_if_scope.

Open Scope boolean_if_scope.

(* To allow a wider variety of notations without reserving a large number *)
(* of identifiers, the ssreflect library systematically uses "forms" to   *)
(* enclose complex mixfix syntax. A "form" is simply a mixfix expression  *)
(* enclosed in square brackets and introduced by a keyword:               *)
(*      [keyword ... ]                                                    *)
(* Because the keyword follows a bracket it does not need to be reserved. *)
(* Non-ssreflect libraries that do not respect the form syntax (e.g., the *)
(* Coq Lists library) should be loaded before ssreflect so that their     *)
(* notations do not mask all ssreflect forms.                             *)
Delimit Scope form_scope with FORM.
Open Scope form_scope.

(* Allow overloading of the cast (x : T) syntax, put whitespace around the    *)
(* ":" symbol to avoid lexical clashes (and for consistency with the parsing  *)
(* precedence of the notation, which binds less tightly than application),    *)
(* and put printing boxes that print the type of a long definition on a       *)
(* separate line rather than force-fit it at the right margin.                *)
Notation "x : T" := (x : T)
  (at level 100, right associativity,
   format "'[hv' x '/ '  :  T ']'") : core_scope.

(* Allow the casual use of notations like nat * nat for explicit Type *)
(* declarations. Note that (nat * nat : Type) is NOT equivalent to    *)
(* (nat * nat)%type, whose inferred type is legacy type "Set".        *)
Notation "T : 'Type'" := (T%type : Type)
  (at level 100, only parsing) : core_scope.
(* Allow similarly Prop annotation for, e.g., rewrite multirules.     *)
Notation "P : 'Prop'" := (P%type : Prop)
  (at level 100, only parsing) : core_scope.

(* Syntax for referring to canonical structures:                   *)
(*      [the struct_type of proj_val by proj_fun]                  *)
(* This form denotes the Canonical instance s of the Structure     *)
(* type struct_type whose proj_fun projection is proj_val, i.e.,   *)
(* such that proj_fun s = proj_val. Typically proj_fun will be one *)
(* of the record field accessors of struct_type, but this need not *)
(* be the case; it can be, for instance, a field of a record type  *)
(* to which struct_type coerces; proj_val will likewise be coerced *)
(* to the return type of proj_fun. In all but the simplest cases,  *)
(* proj_fun should be eta-expanded to allow for the insertion of   *)
(* implicit arguments.                                             *)
(*   In the common case where proj_fun itself is a coercion, the   *)
(* "by" part can be omitted entirely; in this case it is inferred  *)
(* by casting s : struct_type to the inferred type of proj_val.    *)
(* Obviously the latter can be fixed by using an implicit cast on  *)
(* proj_val, and it is highly recommended to do so when the return *)
(* type intended for proj_fun is "Type", as the type inferred for  *)
(* proj_val may vary because of sort polymorphism (it could be Set *)
(* or Prop).                                                       *)
(*   Special note for telescopes (structures with coercion-based   *)
(* inheritance): when using the "the" form to generate a           *)
(* substructure from a canonical hierarchy, on should always       *)
(* project or coerce the value to the BASE structure, because Coq  *)
(* will only find a Canonical derived structure for the Canonical  *)
(* base structure -- not for a base structure that is specific to  *)
(* proj_value.                                                     *)

Module TheCanonical.

CoInductive put vT sT (v1 v2 : vT) (s : sT) : Type := Put.

Definition get vT sT v s (p : @put vT sT v v s) := let: Put := p in s.

Definition get_by vT sT of sT -> vT := @get vT sT.

End TheCanonical.

Import TheCanonical. (* Note: no export. *)

Notation "[ 'the' sT 'of' v 'by' f ]" :=
  (@get_by _ sT f _ _ ((fun v' (s : sT) => Put v' (f s) s) v _))
  (at level 0, only parsing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (get ((fun s : sT => Put v (*coerce*)s s) _))
  (at level 0, only parsing) : form_scope.

(* The following are "format only" versions of the above notations.   *)
(* Since Coq doesn't provide this option, we fake it by splitting the *)
(* "the" keyword. We need to do this because the formatter will be    *)
(* thrown off by application collapsing, coercion insertion and beta  *)
(* reduction in the right hand sides of the above notations.          *)

Notation "[ 'th' 'e' sT 'of' v 'by' f ]" := (@get_by _ sT f v _ _)
  (at level 0,  format "[ 'th' 'e'  sT  'of'  v  'by'  f ]") : form_scope.

Notation "[ 'th' 'e' sT 'of' v ]" := (@get _ sT v _ _)
  (at level 0, format "[ 'th' 'e'  sT   'of'  v ]") : form_scope.

(* We would like to recognize
Notation "[ 'th' 'e' sT 'of' v : 'Type' ]" := (@get Type sT v _ _)
  (at level 0, format "[ 'th' 'e'  sT   'of'  v  :  'Type' ]") : form_scope.
*)

(* Helper notation for canonical structure inheritance support.           *)
(* This is a workaround for the poor interaction between delta reduction  *)
(* and canonical projections in Coq's unification algorithm, by which     *)
(* transparent definitions hide canonical structures, i.e., in            *)
(*   Canonical Structure a_type_struct := @Struct a_type ...              *)
(*   Definition my_type := a_type.                                        *)
(* my_type doesn't effectively inherit the struct structure from a_type.  *)
(* Our solution is to redeclare the structure, as follows                 *)
(*   Canonical Structure my_type_struct :=                                *)
(*     Eval hnf in [struct of my_type].                                   *)
(* The special notation [str of _] must be defined for each Strucure      *)
(* "str" with constructor "Str", typically as follows                     *)
(*   Definition repack_str s :=                                           *)
(*      let: Str _ x y ... z := s return {type of Str for s} -> str in    *)
(*      fun k => k _ x y ... z.                                           *)
(*    Notation "[ 'str' 'of' T 'for' s ]" := (@repack_str s (@Str T))     *)
(*      (at level 0, format "[ 'str'  'of'  T  'for'  s ]") : form_scope. *)
(*    Notation "[ 'str' 'of' T ]" := (repack_str (fun x => @Str T x))     *)
(*      (at level 0, format "[ 'str'  'of'  T ]") : form_scope.           *)
(* The notation for the match return predicate is defined below; the eta  *)
(* expansion in the second form serves both to distinguish it from the    *)
(* first and to avoid the delta reduction problem.                        *)
(*   There are several variations on the notation and the definition of   *)
(* the "repack" function, for telescopes, mixin classes, and join         *)
(* (multiple inheritance) classes; see fintype.v and ssralg.v for         *)
(* examples; they involve inferring the structure from instances of       *)
(* reflexivity or from phantoms (see below), rather than directly from    *)
(* the constructor as above.                                              *)

Definition argumentType T P & forall x : T, P x := T.
Definition dependentReturnType T P & forall x : T, P x := P.
Definition returnType aT rT & aT -> rT := rT.

Notation "{ 'type' 'of' c 'for' s }" := (dependentReturnType c s)
  (at level 0, format "{ 'type'  'of'  c  'for'  s }") : type_scope.

(* A generic "phantom" type (actually, the unit type with a phantom      *)
(* parameter). This can be used for type definitions that require some   *)
(* Structure on one of their parameters, to allow Coq to infer said      *)
(* structure rather that having to supply it explicitly or to resort to  *)
(* the "[is _ <: _]" notation, which interacts poorly with Notation.     *)
(*   The definition of a (co)inductive type with a parameter p : p_type, *)
(* that uses the operations of a structure                               *)
(*  Structure p_str : Type := p_Str {                                    *)
(*    p_repr :> p_type; p_op : p_repr -> ...}                            *)
(* should be given as                                                    *)
(*  Inductive indt_type (p : p_str) : Type := Indt ... .                 *)
(*  Definition indt_of (p : p_str) & phantom p_type p := indt_type p.    *)
(*  Notation "{ 'indt' p }" := (indt_of (Phantom p)).                    *)
(*  Definition indt p x y ... z : {indt p} := @Indt p x y ... z.         *)
(*  Notation "[ 'indt' x y ... z ]" := (indt x y ... z).                 *)
(* That is, the concrete type and its constructor should be shadowed by  *)
(* definitions that use a phantom argument to infer and display the true *)
(* value of p (in practice, the "indt" constructor often performs        *)
(* additional functions, like "locking" the representation (see below).  *)
(*   We also define a simpler version ("phant" / "Phant") of phantom for *)
(* the common case where p_type is Type.                                 *)

CoInductive phantom (T :  Type) (p : T) :  Type := Phantom.
Implicit Arguments phantom [].
Implicit Arguments Phantom [].
CoInductive phant (p : Type) :  Type := Phant.

(* Internal tagging used by the implementation of the ssreflect elim. *)

Definition protect_term (A :  Type) (x : A) : A := x.

(** Term tagging (user-level).                                              *)
(* We provide two strengths of term tagging :                               *)
(*  - (nosimpl t) simplifies to t EXCEPT in a definition; more precisely,   *)
(*    given Definition foo := (nosimpl bar), foo (or (foo t')) will NOT be  *)
(*    expanded by the simpl tactic unless it is in a forcing context (e.g., *)
(*    in match foo t' with ... end, foo t' will be reduced if this allows   *)
(*    match to be reduced. Note that nosimpl bar is simply notation for     *)
(*    a term that beta-iota reduces to bar; hence unfold foo will replace   *)
(*    foo by bar, and fold foo will replace bar by foo. A final warning:    *)
(*    nosimpl only works if no reduction is apparent in t; in particular    *)
(*    Definition foo x := nosimpl t. will usually not work.                 *)
(*    CAVEAT: nosimpl should not be used inside a Section, because the end  *)
(*    of section "cooking" removes the iota redex.                          *)
(*  - (locked t) is provably equal to t, but is not convertible to t; it    *)
(*    provides support for abstract data types, and selective rewriting.    *)
(*    The equation t == (locked t) is provided as a lemma, but it should    *)
(*    only be used for selective rewriting (see below). For ADTs, the       *)
(*    unlock tactic should be used to remove locking.                       *)
(* locked is also used as a placeholder for the implementation of flexible  *)
(* matching.                                                                *)
(* Addendum: it appears that the use of a generic key confuses the term     *)
(* comparison heuristic of the Coq kernel, which thinks all locked terms    *)
(* have the same "head constant", and therefore immediately jumps to        *)
(* comparing their LAST argument. Furthermore, Coq still needs to delta     *)
(* expand a locked constant when comparing unequal terms, and, given the    *)
(* total absence of caching of comparisons, this causes an exponential      *)
(* blowup in comparisons that return false on terms that are built from     *)
(* many combinators, which is quite common in a modular development.        *)
(*   As a stopgap, we use the module system to create opaque constants      *)
(* with an expansion lemma; this is pretty clumsy because design of the     *)
(* module language does not support such small-scale usage very well. See   *)
(* the definiiton of card and subset in fintype.v for examples of this.     *)
(*   Of course the unlock tactic will not support the expansion of this new *)
(* kind of opaque constants; to compensate for that we use "unlockable"     *)
(* canonical structures to store the expansion lemmas, which can then be    *)
(* retrieved by a generic "unlock" rewrite rule. Note that because of a     *)
(* technical limitation of the implementation of canonical projection       *)
(* in ssreflect 1.1, unlock must weaken the intensional equality between    *)
(* the constant and its definition to an extensional one.                   *)

Notation "'nosimpl' t" := (let: tt := tt in t) (at level 10, t at level 8).

(* To unlock opaque constants. *)
Structure unlockable (T : Type) (v : T) : Type :=
  Unlockable {unlocked : T; _ : unlocked = v}.

Lemma unlock : forall aT rT (f : forall x : aT, rT x) (u : unlockable f) x,
  unlocked u x = f x.
Proof. move=> aT rT f [u /= ->]; split. Qed.

(*
Definition locked_with key A := let: tt := key in fun x : A => x.

Lemma unlock : forall key A, @locked_with key A = (fun x => x).
Proof. case; split. Qed.
*)

Lemma master_key : unit. Proof. exact tt. Qed.

(* This should be Definition locked := locked_with master_key, *)
(* but for compatibility with the ml4 code.                    *)
Definition locked A := let: tt := master_key in fun x : A => x.

Lemma lock : forall A x, x = locked x :> A.
Proof. rewrite /locked; case master_key; split. Qed.

(* Needed for locked predicates, in particular for eqType's. *)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. rewrite -lock; discriminate. Qed.

(* The basic closing tactic "done".                                       *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(* The internal lemmas for the have tactics.                                *)

Definition ssr_have Plemma Pgoal (step : Plemma) rest : Pgoal := rest step.
Implicit Arguments ssr_have [Pgoal].

Definition ssr_suff Plemma Pgoal step (rest : Plemma) : Pgoal := step rest.
Implicit Arguments ssr_suff [Pgoal].

Definition ssr_wlog := ssr_suff.
Implicit Arguments ssr_wlog [Pgoal].


(* Internal  N-ary congruence lemma for the congr tactic *)

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.

Lemma nary_congruence : forall n : nat,
 let k B e := forall y : B, (e y y : Prop) in nary_congruence_statement n k.
Proof.
move=> n k; have: k _ _ := _; rewrite {1}/k.
elim: n k  => [|n IHn] k Hk /= A; auto.
by apply: IHn => B e He; apply: Hk => f x1 x2 <-.
Qed.

Lemma ssr_congr_arrow : forall Plemma Pgoal, Plemma = Pgoal -> Plemma -> Pgoal.
Proof. by move=> H G ->; apply. Qed.
Implicit Arguments ssr_congr_arrow [].


(* View lemmas that don't use reflection.                       *)

Section ApplyIff.

Variables P Q : Prop.
Hypothesis eqPQ : P <-> Q.

Lemma iffLR : P -> Q. Proof. by case eqPQ. Qed.
Lemma iffRL : Q -> P. Proof. by case eqPQ. Qed.

Lemma iffLRn : ~P -> ~Q. Proof. by move=> nP tQ; case: nP; case: eqPQ tQ. Qed.
Lemma iffRLn : ~Q -> ~P. Proof. by move=> nQ tP; case: nQ; case: eqPQ tP. Qed.

End ApplyIff.

Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.

Unset Implicit Arguments.

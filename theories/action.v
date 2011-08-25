(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq fintype.
Require Import bigop finset fingroup morphism perm automorphism quotient.

(******************************************************************************)
(* Group action: orbits, stabilisers, transitivity.                           *)
(*        is_action D to == the function to : T -> aT -> T defines an action  *)
(*                          of D : {set aT} on T.                             *)
(*            action D T == structure for a function defining an action of D. *)
(*            act_dom to == the domain D of to : action D rT.                 *)
(*    {action: aT &-> T} == structure for a total action.                     *)
(*                       := action [set: aT] T                                *)
(*   TotalAction to1 toM == the constructor for total actions; to1 and toM    *)
(*                          are the proofs of the action identities for 1 and *)
(*                          a * b, respectively.                              *)
(*   is_groupAction R to == to is a group action on range R: for all a in D,  *)
(*                          the permutation induced by to a is in Aut R. Thus *)
(*                          the action of D must be trivial outside R.        *)
(*       groupAction D R == the structure for group actions of D on R. This   *)
(*                          is a telescope on action D rT.                    *)
(*         gact_range to == the range R of to : groupAction D R.              *)
(*     GroupAction toAut == construct a groupAction for action to from        *)
(*                          toAut : actm to @* D \subset Aut R (actm to is    *)
(*                          the morphism to {perm rT} associated to 'to').    *)
(*      orbit to A x == the orbit of x under the action of A via to.          *)
(*    amove to A x y == the set of a in A whose action send x to y.           *)
(*      'C_A[x | to] == the stabiliser of x : rT in A :&: D.                  *)
(*      'C_A(S | to) == the point-wise stabiliser of S : {set rT} in D :&: A. *)
(*      'N_A(S | to) == the global stabiliser of S : {set rT} in D :&: A.     *)
(*  'Fix_(S | to)[a] == the set of fixpoints of a in S.                       *)
(*  'Fix_(S | to)(A) == the set of fixpoints of A in S.                       *)
(* In the first three _A can be omitted and defaults to the domain D of to;   *)
(* In the last two S can be omitted and defaults to [set: T], so 'Fix_to[a]   *)
(* is the set of all fixpoints of a.                                          *)
(*   The domain restriction ensures that stabilisers have a canonical group   *)
(* structure, but note that 'Fix sets are generally not groups. Indeed, we    *)
(* provide alternative definitions when to is a group action on R:            *)
(*      'C_(G | to)(A) == the centraliser in R :&: G of the group action of   *)
(*                        D :&: A via to                                      *)
(*      'C_(G | to)[a] == the centraliser in R :&: G of a \in D, via to.      *)
(*   These sets are groups when G is. G can be omitted: 'C(|to)(A) is the     *)
(* centraliser in R of the action of D :&: A via to.                          *)
(*          [acts A, on S | to] == A \subset D acts on the set S via to.      *)
(*          {acts A, on S | to} == A acts on the set S (Prop statement).      *)
(*    {acts A, on group G | to} == [acts A, on S | to] /\ G \subset R, i.e.,  *)
(*                                 A \subset D acts on G \subset R, via       *)
(*                                 to : groupAction D R.                      *)
(*    [transitive A, on S | to] == A acts transitively on S.                  *)
(*      [faithful A, on S | to] == A acts faithfully on S.                    *)
(*      acts_irreducibly to A G == A acts irreducibly via the groupAction to  *)
(*                                 on the nontrivial group G, i.e., A does    *)
(*                                 not act on any nontrivial subgroup of G.   *)
(* Important caveat: the definitions of orbit, amove, 'Fix_(S | to)(A),       *)
(* transitive and faithful assume that A is a subset of the domain D. As most *)
(* of the permutation actions we consider are total this is usually harmless. *)
(* (Note that the theory of partial actions is only partially developed.)     *)
(*   In all of the above, to is expected to be the actual action structure,   *)
(* not merely the function. There is a special scope %act for actions, and    *)
(* constructions and notations for many classical actions:                    *)
(*       'P == natural action of a permutation group via aperm.               *)
(*       'J == internal group action (conjugation) via conjg (_ ^ _).         *)
(*       'R == regular group action (right translation) via mulg (_ * _).     *)
(*             (but, to limit ambiguity, _ * _ is NOT a canonical action)     *)
(*     to^* == the action induced by to on {set rT} via to^* (== setact to).  *)
(*      'Js == the internal action on subsets via _ :^ _, equivalent to 'J^*. *)
(*      'Rs == the regular action on subsets via rcoset, equivalent to 'R^*.  *)
(*      'JG == the conjugation action on {group rT} via (_ :^ _)%G.           *)
(*   to / H == the action induced by to on coset_of H via qact to H, and      *)
(*             restricted to qact_dom to H == 'N(rcosets H 'N(H) | to^* ).    *)
(*       'Q == the action induced to cosets by conjugation; the domain is     *)
(*             qact_dom 'J H, which is provably equal to 'N(H).               *)
(*  to %% A == the action of coset_of A via modact to A, with domain D / A    *)
(*             and support restricted to 'C(D :&: A | to).                    *)
(* to \ sAD == the action of A via ract to sAD == to, if sAD : A \subset D.   *)
(*  [Aut G] == the permutation action restricted to Aut G, via autact G.      *)
(*  <[nRA]> == the action of A on R via actby nRA == to in A and on R, and    *)
(*             the trivial action elsewhere; here nRA : [acts A, on R | to]   *)
(*             or nRA : {acts A, on group R | to}.                            *)
(*     to^? == the action induced by to on sT : @subType rT P, via subact to  *)
(*             with domain subact_dom P to == 'N([set x | P x] | to).         *)
(*  <<phi>> == the action of phi : D >-> {perm rT}, via mact phi.             *)
(*  to \o f == the composite action (with domain f @*^-1 D) of the action to  *)
(*             with f : {morphism G >-> aT}, via comp_act to f. Here f must   *)
(*             be the actual morphism object (e.g., coset_morphism H), not    *)
(*             the underlying function (e.g., coset H).                       *)
(* The explicit application of an action to is usually written (to%act x a),  *)
(* where the %act omitted if to is an abstract action or a set action to0^*.  *)
(* Note that this form will simplify and expose the acting function.          *)
(*   There is a %gact scope for group actions; the notations above are        *)
(* recognised in %gact when they denote canonical group actions.              *)
(*   Actions can be used to define morphisms:                                 *)
(* actperm to == the morphism D >-> {perm rT} induced by to.                  *)
(*  actm to a == if a \in D the function on D induced by the action to, else  *)
(*               the identity function. If to is a group action with range R  *)
(*               then actm to a is canonically a morphism on R.               *)
(* We also define here the restriction operation on permutations (the domain  *)
(* of this operations is a stabiliser), and local automorphpism groups:       *)
(*  restr_perm S p == if p acts on S, the permutation with support in S that  *)
(*                    coincides with p on S; else the identity. Note that     *)
(*                    restr_perm is a permutation group morphism that maps    *)
(*                    Aut G to Aut S when S is a subgroup of G.               *)
(*      Aut_in A G == the local permutation group 'N_A(G | 'P) / 'C_A(G | 'P) *)
(*                    Usually A is an automorphism group, and then Aut_in A G *)
(*                    is isomorphic to a subgroup of Aut G, specifically      *)
(*                    restr_perm @* A.                                        *)
(*  Finally, gproduct.v will provide a semi-direct group construction that    *)
(* maps an external group action to an internal one; the theory of morphisms  *)
(* between such products makes use of the following definition:               *)
(*  morph_act to to' f fA <=> the action of to' on the images of f and fA is  *)
(*                   the image of the action of to, i.e., for all x and a we  *)
(*                   have f (to x a) = to' (f x) (fA a). Note that there is   *)
(*                   no mention of the domains of to and to'; if needed, this *)
(*                   predicate should be restricted via the {in ...} notation *)
(*                   and domain conditions should be added.                   *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section ActionDef.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Implicit Types a b : aT.
Implicit Type x : rT.

Definition act_morph to x := forall a b, to x (a * b) = to (to x a) b.

Definition is_action to :=
  left_injective to /\ forall x, {in D &, act_morph to x}.

Record action := Action {act :> rT -> aT -> rT; _ : is_action act}.

Definition clone_action to :=
  let: Action _ toP := to return {type of Action for to} -> action in
  fun k => k toP.

End ActionDef.

(* Need to close the Section here to avoid re-declaring all Argument Scopes *)
Delimit Scope action_scope with act.
Bind Scope action_scope with action.
Arguments Scope
  act [_ group_scope type_scope action_scope group_scope group_scope].
Arguments Scope clone_action [_ group_scope type_scope action_scope _].

Notation "{ 'action' aT &-> T }" := (action [set: aT] T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' to ]" := (clone_action (@Action _ _ _ to))
  (at level 0, format "[ 'action'  'of'  to ]") : form_scope.

Definition act_dom aT D rT of @action aT D rT := D.

Section TotalAction.

Variables (aT : finGroupType) (rT : Type) (to : rT -> aT -> rT).
Hypotheses (to1 : to^~ 1 =1 id) (toM : forall x, act_morph to x).

Lemma is_total_action : is_action setT to.
Proof.
split=> [a | x a b _ _] /=; last by rewrite toM.
by apply: can_inj (to^~ a^-1) _ => x; rewrite -toM ?mulgV.
Qed.

Definition TotalAction := Action is_total_action.

End TotalAction.

Section ActionDefs.

Variables (aT aT' : finGroupType) (D : {set aT}) (D' : {set aT'}).

Definition morph_act rT rT' (to : action D rT) (to' : action D' rT') f fA :=
  forall x a, f (to x a) = to' (f x) (fA a).

Variable rT : finType. (* Most definitions require a finType structure on rT *)
Implicit Type to : action D rT.
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.

Definition actm to a := if a \in D then to^~ a else id.

Definition setact to S a := [set to x a | x <- S].

Definition orbit to A x := to x @: A.

Definition amove to A x y := [set a \in A | to x a == y].

Definition afix to A := [set x | A \subset [set a | to x a == x]].

Definition astab S to := D :&: [set a | S \subset [set x | to x a == x]].

Definition astabs S to := D :&: [set a | S \subset to^~ a @^-1: S].

Definition acts_on A S to := {in A, forall a x, (to x a \in S) = (x \in S)}.

Definition atrans A S to := S \in orbit to A @: S.

Definition faithful A S to := A :&: astab S to \subset [1].

End ActionDefs.

Notation "to ^*" := (setact to) (at level 2, format "to ^*") : fun_scope.

Prenex Implicits orbit amove.

Notation "''Fix_' to ( A )" := (afix to A)
 (at level 8, to at level 2, format "''Fix_' to ( A )") : group_scope.

(* camlp4 grammar factoring *)
Notation "''Fix_' ( to ) ( A )" := 'Fix_to(A)
  (at level 8, only parsing) : group_scope.

Notation "''Fix_' ( S | to ) ( A )" := (S :&: 'Fix_to(A))
 (at level 8, format "''Fix_' ( S  |  to ) ( A )") : group_scope.

Notation "''Fix_' to [ a ]" := ('Fix_to([set a]))
 (at level 8, to at level 2, format "''Fix_' to [ a ]") : group_scope.

Notation "''Fix_' ( S | to ) [ a ]" := (S :&: 'Fix_to[a])
 (at level 8, format "''Fix_' ( S  |  to ) [ a ]") : group_scope.

Notation "''C' ( S | to )" := (astab S to)
 (at level 8, format "''C' ( S  |  to )") : group_scope.

Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))
 (at level 8, A at level 2, format "''C_' A ( S  |  to )") : group_scope.
Notation "''C_' ( A ) ( S | to )" := 'C_A(S | to)
  (at level 8, only parsing) : group_scope.

Notation "''C' [ x | to ]" := ('C([set x] | to))
 (at level 8, format "''C' [ x  |  to ]") : group_scope.

Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])
  (at level 8, A at level 2, format "''C_' A [ x  |  to ]") : group_scope.
Notation "''C_' ( A ) [ x | to ]" := 'C_A[x | to]
  (at level 8, only parsing) : group_scope.

Notation "''N' ( S | to )" := (astabs S to)
  (at level 8, format "''N' ( S  |  to )") : group_scope.

Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))
  (at level 8, A at level 2, format "''N_' A ( S  |  to )") : group_scope.

Notation "[ 'acts' A , 'on' S | to ]" := (A \subset pred_of_set 'N(S | to))
  (at level 0, format "[ 'acts'  A ,  'on'  S  |  to ]") : form_scope.

Notation "{ 'acts' A , 'on' S | to }" := (acts_on A S to)
  (at level 0, format "{ 'acts'  A ,  'on'  S  |  to }") : form_scope.

Notation "[ 'transitive' A , 'on' S | to ]" := (atrans A S to)
  (at level 0, format "[ 'transitive'  A ,  'on'  S  |  to ]") : form_scope.

Notation "[ 'faithful' A , 'on' S | to ]" := (faithful A S to)
  (at level 0, format "[ 'faithful'  A ,  'on'  S  |  to ]") : form_scope.

Section RawAction.
(* Lemmas that do not require the group structure on the action domain. *)
(* Some lemmas like actMin would be actually be valid for arbitrary rT, *)
(* e.g., for actions on a function type, but would be difficult to use  *)
(* as a view due to the confusion between parameters and assumptions.   *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType) (to : action D rT).

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Type A B : {set aT}.
Implicit Types S T : {set rT}.

Lemma act_inj : left_injective to. Proof. by case: to => ? []. Qed.
Implicit Arguments act_inj [].

Lemma actMin : forall x, {in D &, act_morph to x}.
Proof. by case: to => ? []. Qed.

Lemma actmEfun : forall a, a \in D -> actm to a = to^~ a.
Proof. by rewrite /actm => a ->. Qed.

Lemma actmE : forall a, a \in D -> actm to a =1 to^~ a.
Proof. by move=> a Da; rewrite actmEfun. Qed.

Lemma setactE : forall S a, to^* S a = [set to x a | x <- S].
Proof. by []. Qed.

Lemma mem_setact : forall S a x, x \in S -> to x a \in to^* S a.
Proof. move=> S a; exact: mem_imset. Qed.

Lemma card_setact : forall S a, #|to^* S a| = #|S|.
Proof. by move=> S a; apply: card_imset; exact: act_inj. Qed.

Lemma setact_is_action : is_action D to^*.
Proof.
split=> [a R S eqRS | a b Da Db S]; last first.
  rewrite /setact /= -imset_comp; apply: eq_imset => x; exact: actMin.
apply/setP=> x; apply/idP/idP; move/(mem_setact a).
  by rewrite eqRS; case/imsetP=> y Sy; move/act_inj->.
by rewrite -eqRS; case/imsetP=> y Ry; move/act_inj->.
Qed.

Canonical Structure set_action := Action setact_is_action.

Lemma orbitE : forall A x, orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP : forall A x y,
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by move=> A x y; apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma mem_orbit : forall A x a, a \in A -> to x a \in orbit to A x.
Proof. move=> A x a; exact: mem_imset. Qed.

Lemma afixP : forall A x,
  reflect (forall a, a \in A -> to x a = x) (x \in 'Fix_to(A)).
Proof.
move=> A x; rewrite inE; apply: (iffP subsetP) => [xfix a | xfix a Aa].
  by move/xfix; rewrite inE; move/eqP.
by rewrite inE xfix.
Qed.

Lemma afixS : forall A B, A \subset B -> 'Fix_to(B) \subset 'Fix_to(A).
Proof.
by move=> A B sAB; apply/subsetP=> u; rewrite !inE; exact: subset_trans.
Qed.

Lemma afixU : forall A B, 'Fix_to(A :|: B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by move=> A B; apply/setP=> x; rewrite !inE subUset. Qed.

Lemma afix1P : forall a x, reflect (to x a = x) (x \in 'Fix_to[a]).
Proof. move=> a x; rewrite inE sub1set inE; exact: eqP. Qed.

Lemma astabIdom : forall S, 'C_D(S | to) = 'C(S | to).
Proof. by move=> S; rewrite setIA setIid. Qed.

Lemma astab_dom : forall S, {subset 'C(S | to) <= D}.
Proof. by move=> S a; case/setIP. Qed.

Lemma astab_act : forall S a x, a \in 'C(S | to) -> x \in S -> to x a = x.
Proof.
move=> S a x; rewrite 2!inE; case/andP=> _ cSa Sx; apply/eqP.
by have:= subsetP cSa x Sx; rewrite inE.
Qed.

Lemma astabS : forall S1 S2 : {set rT},
  S1 \subset S2 -> 'C(S2 | to) \subset 'C(S1 | to).
Proof.
move=> S1 S2 sS12; apply/subsetP=> x; rewrite !inE; case/andP=> ->.
exact: subset_trans.
Qed.

Lemma astabsIdom : forall S, 'N_D(S | to) = 'N(S | to).
Proof. by move=> S; rewrite setIA setIid. Qed.

Lemma astabs_dom : forall S, {subset 'N(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma astabs_act : forall S a x,
  a \in 'N(S | to) -> (to x a \in S) = (x \in S).
Proof.
move=> S a x; rewrite 2!inE subEproper properEcard; case/andP=> _.
rewrite (card_preimset _ (act_inj _)) ltnn andbF orbF; move/eqP=> defS.
by rewrite {2}defS inE.
Qed.

Lemma astab_sub : forall S, 'C(S | to) \subset 'N(S | to).
Proof.
move=> S; apply/subsetP=> a cSa; rewrite !inE (astab_dom cSa).
by apply/subsetP=> x Sx; rewrite inE (astab_act cSa).
Qed.

Lemma astabsC : forall S, 'N(~: S | to) = 'N(S | to). 
Proof.
move=> S; apply/setP=> a; apply/idP/idP=> nSa; rewrite !inE (astabs_dom nSa).
  by rewrite -setCS -preimsetC; apply/subsetP=> x; rewrite inE astabs_act.
by rewrite preimsetC setCS; apply/subsetP=> x; rewrite inE astabs_act.
Qed.

Lemma astabsI : forall S T, 'N(S | to) :&: 'N(T | to) \subset 'N(S :&: T | to). 
Proof.
move=> S T; apply/subsetP=> a; rewrite !inE -!andbA preimsetI.
by case/and4P=> -> nSa _ nTa; rewrite setISS.
Qed.

Lemma astabs_setact : forall S a, a \in 'N(S | to) -> to^* S a = S.
Proof.
move=> S a nSa; apply/eqP; rewrite eqEcard card_setact leqnn andbT.
by apply/subsetP=> xa; case/imsetP=> x Sx ->; rewrite astabs_act.
Qed.

Lemma astab1_set : forall S, 'C[S | set_action] = 'N(S | to).
Proof.
move=> S; apply/setP=> a; apply/idP/idP=> nSa.
  case/setIdP: nSa => Da; rewrite !inE Da sub1set inE; move/eqP=> defS.
  by apply/subsetP=> x Sx; rewrite inE -defS mem_setact.
by rewrite !inE (astabs_dom nSa) sub1set inE /= astabs_setact.
Qed.

Lemma astabs_set1 : forall x, 'N([set x] | to) = 'C[x | to].
Proof.
move=> x; apply/eqP; rewrite eqEsubset astab_sub andbC setIS //.
by apply/subsetP=> a; rewrite ?(inE,sub1set).
Qed.

Lemma acts_dom : forall A S, [acts A, on S | to] -> A \subset D.
Proof. by move=> A S nSA; rewrite (subset_trans nSA) ?subsetIl. Qed.

Lemma acts_act : forall A S, [acts A, on S | to] -> {acts A, on S | to}.
Proof. by move=> A S nAS a Aa x; rewrite astabs_act ?(subsetP nAS). Qed.

Lemma astabCin : forall A S, 
  A \subset D -> (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof.
move=> A S sAD; apply/subsetP/subsetP.
  by move=> sAC x xS; apply/afixP=> a aA; exact: astab_act (sAC _ aA) xS.
move=> sSF a aA; rewrite !inE (subsetP sAD _ aA); apply/subsetP=> x xS.
by move/afixP: (sSF _ xS); move/(_ _ aA); rewrite inE => ->. 
Qed.

Section ActsSetop.

Variables (A : {set aT}) (S T : {set rT}).
Hypotheses (AactS : [acts A, on S | to]) (AactT : [acts A, on T | to]).

Lemma astabU : 'C(S :|: T | to) = 'C(S | to) :&: 'C(T | to).
Proof. by apply/setP=> a; rewrite !inE subUset; case: (a \in D). Qed.

Lemma astabsU : 'N(S | to) :&: 'N(T | to) \subset 'N(S :|: T | to). 
Proof.
by rewrite -(astabsC S) -(astabsC T) -(astabsC (S :|: T)) setCU astabsI.
Qed.

Lemma astabsD : 'N(S | to) :&: 'N(T | to) \subset 'N(S :\: T| to). 
Proof. by rewrite setDE -(astabsC T) astabsI. Qed.

Lemma actsI : [acts A, on S :&: T | to].
Proof. by apply: subset_trans (astabsI S T); rewrite subsetI AactS. Qed.

Lemma actsU : [acts A, on S :|: T | to].
Proof. by apply: subset_trans astabsU; rewrite subsetI AactS. Qed.

Lemma actsD : [acts A, on S :\: T | to].
Proof. by apply: subset_trans astabsD; rewrite subsetI AactS. Qed.

End ActsSetop.

Lemma acts_in_orbit : forall A S x y,
  [acts A, on S | to] -> y \in orbit to A x -> x \in S -> y \in S.
Proof.
move=> A S x y nSA; case/imsetP=> a Aa ->{y} Sx.
by rewrite (astabs_act _ (subsetP nSA a Aa)).
Qed.

Lemma subset_faithful : forall A B S,
  B \subset A -> [faithful A, on S | to] -> [faithful B, on S | to].
Proof. move=> A B S sAB; apply: subset_trans; exact: setSI. Qed.

Section Reindex.

Variables (vT : Type) (idx : vT) (op : Monoid.com_law idx) (S : {set rT}).

Lemma reindex_astabs : forall a F, a \in 'N(S | to) ->
  \big[op/idx]_(i \in S) F i = \big[op/idx]_(i \in S) F (to i a).
Proof.
move=> a F nSa; rewrite (reindex_inj (act_inj a)); apply: eq_bigl => x.
exact: astabs_act.
Qed.

Lemma reindex_acts : forall A a F, [acts A, on S | to] -> a \in A ->
  \big[op/idx]_(i \in S) F i = \big[op/idx]_(i \in S) F (to i a).
Proof. move=> A a F nSA; move/(subsetP nSA); exact: reindex_astabs. Qed.

End Reindex.

End RawAction.

(* Warning: this directive depends on names of bound variables in the *)
(* definition of injective, in ssrfun.v.                              *)
Implicit Arguments act_inj [[aT] [D] [rT] x1 x2].

Notation "to ^*" := (set_action to) : action_scope.

Implicit Arguments orbitP [aT D rT to A x y].
Implicit Arguments afixP [aT D rT to A x].
Implicit Arguments afix1P [aT D rT to a x].
Prenex Implicits orbitP afixP afix1P.

Implicit Arguments reindex_astabs [aT D rT vT idx op S F].
Implicit Arguments reindex_acts [aT D rT vT idx op S A a F].

Section PartialAction.
(* Lemmas that require a (partial) group domain. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Types A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Types S : {set rT}.

Lemma act1 : forall x, to x 1 = x.
Proof. by move=> x; apply: (act_inj to 1); rewrite -actMin ?mulg1. Qed.

Lemma actKin : {in D, right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -actMin ?groupV // mulgV act1. Qed.

Lemma actKVin : {in D, rev_right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -{2}(invgK a) actKin ?groupV. Qed.

Lemma setactVin : forall S a, a \in D -> to^* S a^-1 = to^~ a @^-1: S.
Proof.
move=> S a Da; apply: can2_imset_pre; [exact: actKVin | exact: actKin].
Qed.

Lemma actXin : forall x a i, a \in D -> to x (a ^+ i) = iter i (to^~ a) x.
Proof.
move=> x a i Da; elim: i => /= [|i <-]; first by rewrite act1.
by rewrite expgSr actMin ?groupX.
Qed.

Lemma afix1 : 'Fix_to(1) = setT.
Proof. by apply/setP=> x; rewrite !inE sub1set inE act1 eqxx. Qed.

Lemma afixD1 : forall G, 'Fix_to(G^#) = 'Fix_to(G).
Proof. by move=> G; rewrite -{2}(setD1K (group1 G)) afixU afix1 setTI. Qed.

Lemma orbit_refl : forall G x, x \in orbit to G x.
Proof. by move=> G x; rewrite -{1}[x]act1 mem_orbit. Qed.

Local Notation orbit_rel A := (fun x y => y \in orbit to A x).

Lemma contra_orbit : forall G x y, x \notin orbit to G y -> x != y.
Proof. move=> G x y; apply: contraNneq => ->; exact: orbit_refl. Qed.

Lemma orbit_in_sym : forall G, G \subset D -> symmetric (orbit_rel G).
Proof.
move=> G sGD; apply: symmetric_from_pre => x y; case/imsetP=> a Ga.
by move/(canLR (actKin (subsetP sGD a Ga))) <-; rewrite mem_orbit ?groupV.
Qed.

Lemma orbit_in_trans : forall G, G \subset D -> transitive (orbit_rel G).
Proof.
move=> G sGD y x z; case/imsetP=> a Ga ->; case/imsetP=> b Gb ->{y z}.
by rewrite -actMin ?mem_orbit ?groupM // (subsetP sGD).
Qed.

Lemma orbit_in_transl : forall G x y,
  G \subset D -> y \in orbit to G x -> orbit to G y = orbit to G x.
Proof.
move=> G x y sGD Gxy; apply/setP=> z.
by apply/idP/idP; apply: orbit_in_trans; rewrite // orbit_in_sym.
Qed.

Lemma orbit_in_transr : forall G x y z,
    G \subset D -> y \in orbit to G x ->
  (y \in orbit to G z) = (x \in orbit to G z).
Proof.
by move=> G x y z sGD Gxy; rewrite !(orbit_in_sym _ z) ?(orbit_in_transl _ Gxy).
Qed.

Lemma orbit_inv_in : forall A x y, A \subset D ->
  (y \in orbit to A^-1 x) = (x \in orbit to A y).
Proof.
move=> A x y; move/subsetP=> sAD; apply/imsetP/imsetP=> [] [a Aa ->].
  by exists a^-1; rewrite -?mem_invg ?actKin // -groupV sAD -?mem_invg.
by exists a^-1; rewrite ?memV_invg ?actKin // sAD.
Qed.

Lemma orbit_lcoset_in : forall A a x, A \subset D -> a \in D ->
  orbit to (a *: A) x = orbit to A (to x a).
Proof.
move=> A a x; move/subsetP=> sAD Da; apply/setP=> y.
apply/imsetP/imsetP=> [] [b Ab ->{y}].
  by exists (a^-1 * b); rewrite -?actMin ?mulKVg // ?sAD -?mem_lcoset.
by exists (a * b); rewrite ?mem_mulg ?set11 ?actMin // sAD.
Qed.

Lemma orbit_rcoset_in : forall A a x y, A \subset D -> a \in D ->
  (to y a \in orbit to (A :* a) x) = (y \in orbit to A x).
Proof.
move=> A a x y sAD Da; rewrite -orbit_inv_in ?mul_subG ?sub1set // invMg.
by rewrite invg_set1 orbit_lcoset_in ?inv_subG ?groupV ?actKin ?orbit_inv_in.
Qed.

Lemma orbit_conjsg_in : forall A a x y, A \subset D -> a \in D ->
  (to y a \in orbit to (A :^ a) (to x a)) = (y \in orbit to A x).
Proof.
move=> A a x y sAD Da; rewrite conjsgE.
by rewrite orbit_lcoset_in ?groupV ?mul_subG ?sub1set ?actKin ?orbit_rcoset_in.
Qed.

Lemma orbit1P : forall G x,
  reflect (orbit to G x = [set x]) (x \in 'Fix_to(G)).
Proof.
move=> G x; apply: (iffP afixP) => [xfix | xfix a Ga].
  apply/eqP; rewrite eq_sym eqEsubset sub1set -{1}[x]act1 mem_imset //=.
  by apply/subsetP=> y; case/imsetP=> a Ga ->; rewrite inE xfix.
by apply/set1P; rewrite -xfix mem_imset.
Qed.

Lemma card_orbit1 : forall G x,
  #|orbit to G x| = 1%N -> orbit to G x = [set x].
Proof.
move=> G x orb1; apply/eqP; rewrite eq_sym eqEcard {}orb1 cards1.
by rewrite sub1set orbit_refl.
Qed.

Lemma group_set_astab : forall S, group_set 'C(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x _; rewrite inE act1.
rewrite !inE groupM ?(@astab_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astab_dom _ _ _ to S) ?(astab_act _ Sx).
Qed.

Canonical Structure astab_group S := group (group_set_astab S).

Lemma afix_gen_in : forall A, A \subset D -> 'Fix_to(<<A>>) = 'Fix_to(A).
Proof.
move=> A sAD; apply/eqP; rewrite eqEsubset afixS ?sub_gen //=.
by rewrite -astabCin gen_subG ?astabCin.
Qed.

Lemma afix_cycle_in : forall a, a \in D -> 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by move=> a Da; rewrite afix_gen_in ?sub1set. Qed.

Lemma afixYin : forall A B,
  A \subset D -> B \subset D -> 'Fix_to(A <*> B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by move=> A B sAD sBD; rewrite afix_gen_in ?afixU // subUset sAD. Qed. 

Lemma afixMin : forall G H,
  G \subset D -> H \subset D -> 'Fix_to(G * H) = 'Fix_to(G) :&: 'Fix_to(H).
Proof.
by move=> G H sGD sHD; rewrite -afix_gen_in ?mul_subG // genM_join afixYin.
Qed. 

Lemma sub_astab1_in : forall A x,
  A \subset D -> (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by move=> A x sAD; rewrite astabCin ?sub1set. Qed.

Lemma group_set_astabs : forall S, group_set 'N(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x Sx; rewrite inE act1.
rewrite !inE groupM ?(@astabs_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astabs_dom _ _ _ to S) ?astabs_act.
Qed.

Canonical Structure astabs_group S := group (group_set_astabs S).

Lemma astab_norm : forall S, 'N(S | to) \subset 'N('C(S | to)).
Proof.
move=> S; apply/subsetP=> a nSa; rewrite inE sub_conjg; apply/subsetP=> b cSb.
have [Da Db] := (astabs_dom nSa, astab_dom cSb).
rewrite mem_conjgV !inE groupJ //; apply/subsetP=> x Sx.
rewrite inE !actMin ?groupM ?groupV //.
by rewrite (astab_act cSb) ?actKVin ?astabs_act ?groupV.
Qed.

Lemma astab_normal : forall S, 'C(S | to) <| 'N(S | to).
Proof. by move=> S; rewrite /normal astab_sub astab_norm. Qed.

Lemma acts_sub_orbit : forall G S x,
  [acts G, on S | to] -> (orbit to G x \subset S) = (x \in S).
Proof.
move=> G S x; move/acts_act=> GactS.
apply/subsetP/idP=> [| Sx y]; first by apply; exact: orbit_refl.
by case/orbitP=> a Ga <-{y}; rewrite GactS.
Qed.

Lemma acts_orbit : forall G x, G \subset D -> [acts G, on orbit to G x | to].
Proof.
move=> G x; move/subsetP=> sGD; apply/subsetP=> a Ga; rewrite !inE sGD //.
apply/subsetP=> xb; case/imsetP=> b Gb ->{xb}.
by rewrite inE -actMin ?sGD // mem_imset ?groupM.
Qed.

Lemma acts_subnorm_fix : forall A, [acts 'N_D(A), on 'Fix_to(D :&: A) | to].
Proof.
move=> A; apply/subsetP=> a nAa; have [Da _] := setIP nAa; rewrite !inE Da.
apply/subsetP=> x Cx; rewrite inE; apply/afixP=> b DAb.
have [Db _]:= setIP DAb; rewrite -actMin // conjgCV  actMin ?groupJ ?groupV //.
by rewrite /= (afixP Cx) // memJ_norm // groupV (subsetP (normsGI _ _) _ nAa).
Qed.

Lemma atrans_orbit : forall G x, [transitive G, on orbit to G x | to].
Proof. move=> G x; apply: mem_imset; exact: orbit_refl. Qed.

Section OrbitStabilizer.

Variables (G : {group aT}) (x : rT).
Hypothesis sGD : G \subset D.
Let ssGD := subsetP sGD.

Lemma amove_act : forall a,
  a \in G -> amove to G x (to x a) = 'C_G[x | to] :* a.
Proof.
move=> a Ga; apply/setP => b; have Da := ssGD Ga.
rewrite mem_rcoset !(inE, sub1set) !groupMr ?groupV //.
by case Gb: (b \in G); rewrite //= actMin ?groupV ?ssGD ?(canF_eq (actKVin Da)).
Qed.

Lemma amove_orbit : amove to G x @: orbit to G x = rcosets 'C_G[x | to] G.
Proof.
apply/setP => Ha; apply/imsetP/rcosetsP=> [[y] | [a Ga ->]].
  by case/imsetP=> b Gb -> ->{Ha y}; exists b => //; rewrite amove_act.
by rewrite -amove_act //; exists (to x a); first exact: mem_orbit.
Qed.

Lemma amoveK :
  {in orbit to G x, cancel (amove to G x) (fun Ca => to x (repr Ca))}.
Proof.
move=> y; case/orbitP=> a Ga <-{y}; rewrite amove_act //= -[G :&: _]/(gval _).
case: repr_rcosetP => b; rewrite !(inE, sub1set); case/and3P=> Gb _ xbx.
by rewrite actMin ?ssGD ?(eqP xbx).
Qed.

Lemma orbit_stabilizer :
  orbit to G x = [set to x (repr Ca) | Ca <- rcosets 'C_G[x | to] G].
Proof.
rewrite -amove_orbit -imset_comp /=; apply/setP=> z.
by apply/idP/imsetP=> [xGz | [y xGy ->]]; first exists z; rewrite /= ?amoveK.
Qed.

Lemma act_reprK :
  {in rcosets 'C_G[x | to] G, cancel (to x \o repr) (amove to G x)}.
Proof.
move=> Ca; case/rcosetsP=> a Ga ->{Ca} /=; rewrite amove_act ?rcoset_repr //.
rewrite -[G :&: _]/(gval _); case: repr_rcosetP => b; case/setIP=> Gb _.
exact: groupM.
Qed.

End OrbitStabilizer.

Lemma card_orbit_in : forall G x,
  G \subset D -> #|orbit to G x| = #|G : 'C_G[x | to]|.
Proof.
move=> G x sGD; rewrite orbit_stabilizer 1?card_in_imset //.
exact: can_in_inj (act_reprK _).
Qed.

Lemma card_orbit_in_stab : forall G x,
  G \subset D -> (#|orbit to G x| * #|'C_G[x | to]|)%N = #|G|.
Proof. by move=> G x sGD; rewrite mulnC card_orbit_in ?LaGrange ?subsetIl. Qed.

Lemma acts_sum_card_orbit : forall G S,
  [acts G, on S | to] -> \sum_(T \in orbit to G @: S) #|T| = #|S|.
Proof.
move=> G S GactS; rewrite -sum1_card (partition_big_imset (orbit to G)) /=.
apply: eq_bigr => xS; case/imsetP=> x Sx ->{xS}; rewrite -sum1_card.
apply: eq_bigl=> y; apply/idP/andP=> [xGy|[_]].
  by rewrite (orbit_in_transl (acts_dom GactS) xGy) (acts_in_orbit _ xGy).
by move/eqP <-; exact: orbit_refl.
Qed.

Lemma astab_setact_in : forall S a,
  a \in D -> 'C(to^* S a | to) = 'C(S | to) :^ a.
Proof.
move=> S a Da; apply/setP=> b; rewrite mem_conjg !inE -mem_conjg conjGid //.
apply: andb_id2l => Db; rewrite sub_imset_pre; apply: eq_subset_r => x.
by rewrite !inE !actMin ?groupM ?groupV // invgK (canF_eq (actKVin Da)).
Qed.

Lemma astab1_act_in : forall x a, a \in D -> 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by move=> x a Da; rewrite -astab_setact_in // /setact imset_set1. Qed.

Theorem Frobenius_Cauchy : forall G S, [acts G, on S | to] ->
  \sum_(a \in G) #|'Fix_(S | to)[a]| = (#|orbit to G @: S| * #|G|)%N.
Proof.
move=> G S GactS; have sGD := acts_dom GactS.
transitivity (\sum_(a \in G) \sum_(x \in 'Fix_(S | to)[a]) 1%N).
  by apply: eq_bigr => a _; rewrite -sum1_card.
rewrite (exchange_big_dep (mem S)) /= => [|a x _]; last by case/setIP.
set orbG := orbit to G; rewrite (partition_big_imset orbG) -sum_nat_const /=.
apply: eq_bigr => X; case/imsetP=> x Sx ->{X}.
rewrite (eq_bigl (mem (orbG x))) => [|y] /=; last first.
  apply/andP/idP=> [[_]|xGy]; first by move/eqP <-; exact: orbit_refl.
  by rewrite /orbG (orbit_in_transl sGD xGy) (acts_in_orbit GactS xGy).
rewrite -(card_orbit_in_stab x sGD) -sum_nat_const.
apply: eq_bigr => y; rewrite orbit_in_sym //; case/imsetP=> a Ga defx.
rewrite defx astab1_act_in ?(subsetP sGD) //.
rewrite -{2}(conjGid Ga) -conjIg cardJg -sum1_card setIA (setIidPl sGD).
by apply: eq_bigl => b; rewrite !(sub1set, inE) -(acts_act GactS Ga) -defx Sx.
Qed.

Lemma atrans_dvd_index_in : forall G S,
  G \subset D -> [transitive G, on S | to] -> #|S| %| #|G : 'C_G(S | to)|.
Proof.
move=> G S sGD; case/imsetP=> x Sx defS; rewrite {1}defS card_orbit_in //.
by rewrite indexgS // setIS // astabS // sub1set.
Qed.

Lemma atrans_dvd_in : forall G S,
  G \subset D -> [transitive G, on S | to] -> #|S| %| #|G|.
Proof.
move=> G S sGD transG; apply: dvdn_trans (atrans_dvd_index_in sGD transG) _.
exact: dvdn_indexg.
Qed.

Lemma atransPin : forall G S,
     G \subset D -> [transitive G, on S | to] ->
  forall x, x \in S -> orbit to G x = S.
Proof. move=> G S sGD; case/imsetP=> x _ -> y; exact: orbit_in_transl. Qed.

Lemma atransP2in : forall G S,
    G \subset D -> [transitive G, on S | to] ->
  {in S &, forall x y, exists2 a, a \in G & y = to x a}.
Proof.
by move=> G S sGD transG x y; move/(atransPin sGD transG) <-; move/imsetP.
Qed.

Lemma atrans_acts_in : forall G S,
  G \subset D -> [transitive G, on S | to] -> [acts G, on S | to].
Proof.
move=> G S sGD transG; apply/subsetP=> a Ga; rewrite !inE (subsetP sGD) //.
by apply/subsetP=> x; move/(atransPin sGD transG) <-; rewrite inE mem_imset.
Qed.

Lemma subgroup_transitivePin : forall G H S x,
     x \in S -> H \subset G -> G \subset D -> [transitive G, on S | to] ->
  reflect ('C_G[x | to] * H = G) [transitive H, on S | to].
Proof.
move=> G H S x Sx sHG sGD trG; have sHD := subset_trans sHG sGD.
apply: (iffP idP) => [trH | defG].
  rewrite group_modr //; apply/setIidPl; apply/subsetP=> a Ga.
  have Sxa: to x a \in S by rewrite (acts_act (atrans_acts_in sGD trG)).
  have [b Hb xab]:= atransP2in sHD trH Sxa Sx.
  have Da := subsetP sGD a Ga; have Db := subsetP sHD b Hb.
  rewrite -(mulgK b a) mem_mulg ?groupV // !inE groupM //= sub1set inE.
  by rewrite actMin -?xab.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransPin sGD trG Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first exact: (subsetP sHG).
rewrite -defG; case/imset2P=> c b; case/setIP=> _ cxc Hb -> ->.
exists b; rewrite ?actMin ?(astab_dom cxc) ?(subsetP sHD) //.
by rewrite (astab_act cxc) ?inE.
Qed.

End PartialAction.

Implicit Arguments orbit1P [aT D rT to G x].
Implicit Arguments contra_orbit [aT D rT x y].
Prenex Implicits orbit1P.

Notation "''C' ( S | to )" := (astab_group to S) : subgroup_scope.
Notation "''C_' A ( S | to )" := (setI_group A 'C(S | to)) : subgroup_scope.
Notation "''C_' ( A ) ( S | to )" := (setI_group A 'C(S | to))
  (only parsing) : subgroup_scope.
Notation "''C' [ x | to ]" := (astab_group to [set x%g]) : subgroup_scope.
Notation "''C_' A [ x | to ]" := (setI_group A 'C[x | to]) : subgroup_scope.
Notation "''C_' ( A ) [ x | to ]" := (setI_group A 'C[x | to])
  (only parsing) : subgroup_scope.
Notation "''N' ( S | to )" := (astabs_group to S) : subgroup_scope.
Notation "''N_' A ( S | to )" := (setI_group A 'N(S | to)) : subgroup_scope.

Section TotalActions.
(* These lemmas are only established for total actions (domain = [set: rT]) *)

Variable (aT : finGroupType) (rT : finType).

Variable to : {action aT &-> rT}.

Implicit Types a b : aT.
Implicit Types x y z : rT.
Implicit Types A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Types S : {set rT}.

Lemma actM : forall x a b, to x (a * b) = to (to x a) b.
Proof. by move=> x a b; rewrite actMin ?inE. Qed.

Lemma actK : right_loop invg to.
Proof. by move=> a; apply: actKin; rewrite inE. Qed.

Lemma actKV : rev_right_loop invg to.
Proof. by move=> a; apply: actKVin; rewrite inE. Qed.

Lemma actX : forall x a n, to x (a ^+ n) = iter n (to^~ a) x.
Proof. by move=> x a; elim=> [|n /= <-]; rewrite ?act1 // -actM expgSr. Qed.

Lemma actCJ : forall a b x, to (to x a) b = to (to x b) (a ^ b).
Proof. by move=> a b x; rewrite !actM actK. Qed.

Lemma actCJV : forall a b x, to (to x a) b = to (to x (b ^ a^-1)) a.
Proof. by move=> a b x; rewrite (actCJ _ a) conjgKV. Qed.

Lemma orbit_sym : forall G x y, (y \in orbit to G x) = (x \in orbit to G y).
Proof. move=> G; apply: orbit_in_sym; exact: subsetT. Qed.

Lemma orbit_trans : forall G x y z,
  y \in orbit to G x -> z \in orbit to G y -> z \in orbit to G x.
Proof. move=> G x y z; apply: orbit_in_trans; exact: subsetT. Qed.

Lemma orbit_transl : forall G x y,
  y \in orbit to G x -> orbit to G y = orbit to G x.
Proof.
move=> G x y Gxy; apply/setP=> z; apply/idP/idP; apply: orbit_trans => //.
by rewrite orbit_sym.
Qed.

Lemma orbit_transr : forall G x y z,
  y \in orbit to G x -> (y \in orbit to G z) = (x \in orbit to G z).
Proof.
by move=> G x y z Gxy; rewrite orbit_sym (orbit_transl Gxy) orbit_sym.
Qed.

Lemma orbit_eq_mem : forall G x y,
  (orbit to G x == orbit to G y) = (x \in orbit to G y).
Proof.
move=> G x y; apply/eqP/idP=> [<-|]; [exact: orbit_refl | exact: orbit_transl].
Qed.

Lemma orbit_inv : forall A x y, (y \in orbit to A^-1 x) = (x \in orbit to A y).
Proof. by move=> A x y; rewrite orbit_inv_in ?subsetT. Qed.

Lemma orbit_lcoset : forall A a x, orbit to (a *: A) x = orbit to A (to x a). 
Proof. by move=> A a x; rewrite orbit_lcoset_in ?subsetT ?inE. Qed.

Lemma orbit_rcoset : forall A a x y,
  (to y a \in orbit to (A :* a) x) = (y \in orbit to A x).
Proof. by move=> A a x y; rewrite orbit_rcoset_in ?subsetT ?inE. Qed.

Lemma orbit_conjsg : forall A a x y,
  (to y a \in orbit to (A :^ a) (to x a)) = (y \in orbit to A x).
Proof. by move=> A a x y; rewrite orbit_conjsg_in ?subsetT ?inE. Qed.

Lemma astabP : forall S a,
  reflect (forall x, x \in S -> to x a = x) (a \in 'C(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [cSa x|cSa]; first exact: astab_act.
by rewrite !inE; apply/subsetP=> x Sx; rewrite inE cSa.
Qed.

Lemma astab1P : forall x a, reflect (to x a = x) (a \in 'C[x | to]).
Proof. by move=> x a; rewrite !inE sub1set inE; exact: eqP. Qed.

Lemma sub_astab1 : forall A x, (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by move=> A x; rewrite sub_astab1_in ?subsetT. Qed.

Lemma astabC : forall A S, (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof. by move=> A S; rewrite astabCin ?subsetT. Qed.

Lemma afix_cycle : forall a, 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by move=> a; rewrite afix_cycle_in ?inE. Qed.

Lemma afix_gen : forall A, 'Fix_to(<<A>>) = 'Fix_to(A).
Proof. by move=> a; rewrite afix_gen_in ?subsetT. Qed.

Lemma afixM : forall G H, 'Fix_to(G * H) = 'Fix_to(G) :&: 'Fix_to(H).
Proof. by move=> G H; rewrite afixMin ?subsetT. Qed.

Lemma astabsP : forall S a,
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
by rewrite !inE; apply/subsetP=> x; rewrite inE nSa.
Qed.

Lemma card_orbit : forall G x, #|orbit to G x| = #|G : 'C_G[x | to]|.
Proof. by move=> G x; rewrite card_orbit_in ?subsetT. Qed.

Lemma dvdn_orbit : forall G x, #|orbit to G x| %| #|G|.
Proof. by move=> G x; rewrite card_orbit dvdn_indexg. Qed.

Lemma card_orbit_stab : forall G x,
  (#|orbit to G x| * #|'C_G[x | to]|)%N = #|G|.
Proof. by move=> G x; rewrite mulnC card_orbit LaGrange ?subsetIl. Qed.

Lemma actsP : forall A S, reflect {acts A, on S | to} [acts A, on S | to].
Proof.
move=> A S; apply: (iffP idP) => [nSA x|nSA]; first exact: acts_act.
by apply/subsetP=> a Aa; rewrite !inE; apply/subsetP=> x; rewrite inE nSA.
Qed.
Implicit Arguments actsP [A S].

Lemma setact_orbit : forall A x b,
  to^* (orbit to A x) b = orbit to (A :^ b) (to x b).
Proof.
move=> A x b; apply/setP=> y; apply/idP/idP.
  case/imsetP=> xa; case/imsetP=> a Aa -> ->{xa y}.
  by rewrite actCJ mem_orbit ?memJ_conjg.
case/imsetP=> ab; case/imsetP=> a Aa -> ->{ab y}.
by rewrite -actCJ mem_setact ?mem_orbit.
Qed.

Lemma astab_setact : forall S a, 'C(to^* S a | to) = 'C(S | to) :^ a.
Proof.
move=> S a; apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_act : forall x a, 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by move=> x a; rewrite -astab_setact /setact imset_set1. Qed.

Lemma atransP : forall G S, [transitive G, on S | to] ->
  forall x, x \in S -> orbit to G x = S.
Proof. move=> G S; case/imsetP=> x _ -> y; exact: orbit_transl. Qed.

Lemma atransP2 : forall G S, [transitive G, on S | to] ->
  {in S &, forall x y, exists2 a, a \in G & y = to x a}.
Proof. by move=> G S GtrS x y; move/(atransP GtrS) <-; move/imsetP. Qed.

Lemma atrans_acts : forall G S,
  [transitive G, on S | to] -> [acts G, on S | to].
Proof.
move=> G S GtrS; apply/subsetP=> a Ga; rewrite !inE.
by apply/subsetP=> x; move/(atransP GtrS) <-; rewrite inE mem_imset.
Qed.

Lemma atrans_supgroup : forall G H S,
   G \subset H -> [transitive G, on S | to] ->
    [transitive H, on S | to] = [acts H, on S | to].
Proof.
move=> G H S sGH trG; apply/idP/idP=> [|actH]; first exact: atrans_acts.
case/imsetP: trG => x Sx defS; apply/imsetP; exists x => //.
by apply/eqP; rewrite eqEsubset acts_sub_orbit ?Sx // defS imsetS.
Qed.

Lemma atrans_acts_card : forall G S,
  [transitive G, on S | to] =
     [acts G, on S | to] && (#|orbit to G @: S| == 1%N).
Proof.
move=> G S; apply/idP/andP=> [GtrS | [nSG]].
  split; first exact: atrans_acts.
  rewrite ((_ @: S =P [set S]) _) ?cards1 // eqEsubset sub1set.
  apply/andP; split=> //; apply/subsetP=> X; case/imsetP=> x Sx ->.
  by rewrite inE (atransP GtrS).
rewrite eqn_leq andbC lt0n; case/andP.
case/existsP=> X; case/imsetP=> x Sx X_Gx.
rewrite (cardD1 X) {X}X_Gx mem_imset // ltnS leqn0; move/eqP=> GtrS.
apply/imsetP; exists x => //; apply/eqP.
rewrite eqEsubset acts_sub_orbit // Sx andbT.
apply/subsetP=> y Sy; have:= card0_eq GtrS (orbit to G y).
rewrite !inE /= mem_imset // andbT; move/eqP <-; exact: orbit_refl.
Qed.

Lemma atrans_dvd : forall G S, [transitive G, on S | to] -> #|S| %| #|G|.
Proof. by move=> G S; case/imsetP=> x _ ->; exact: dvdn_orbit. Qed.

(* Aschbacher 5.2 *)
Lemma acts_fix_norm : forall A B,
  A \subset 'N(B) -> [acts A, on 'Fix_to(B) | to].
Proof.
move=> A B nAB; have:= acts_subnorm_fix to B; rewrite !setTI.
exact: subset_trans.
Qed.

Lemma faithfulP : forall A S,
  reflect (forall a, a \in A -> {in S, to^~ a =1 id} -> a = 1)
          [faithful A, on S | to].
Proof.
move=> A S; apply: (iffP subsetP) => [Cto1 a Aa Ca | Cto1 a].
  apply/set1P; rewrite Cto1 // inE Aa; exact/astabP.
case/setIP=> Aa; move/astabP=> Ca; apply/set1P; exact: Cto1.
Qed.

(* This is the first part of Aschbacher (5.7) *)
Lemma astab_trans_gcore : forall G S u,
  [transitive G, on S | to] -> u \in S -> 'C(S | to) = gcore 'C[u | to] G.
Proof.
move=> G S u transG Su; apply/eqP; rewrite eqEsubset.
rewrite gcore_max ?astabS ?sub1set //=; last first.
  exact: subset_trans (atrans_acts transG) (astab_norm _ _).
apply/subsetP=> x cSx; apply/astabP=> uy.
case/(atransP2 transG Su) => y Gy ->{uy}.
by apply/astab1P; rewrite astab1_act (bigcapP cSx).
Qed.

(* Aschbacher 5.20 *)
Theorem subgroup_transitiveP : forall G H S x,
     x \in S -> H \subset G -> [transitive G, on S | to] ->
  reflect ('C_G[x | to] * H = G) [transitive H, on S | to].
Proof. by move=> G H S x Sx sHG; exact: subgroup_transitivePin (subsetT G). Qed.

(* Aschbacher 5.21 *)
Lemma trans_subnorm_fixP : forall x G H S,
  let C := 'C_G[x | to] in let T := 'Fix_(S | to)(H) in
    [transitive G, on S | to] -> x \in S -> H \subset C ->
  reflect ((H :^: G) ::&: C = H :^: C) [transitive 'N_G(H), on T | to].
Proof.
move=> x G H S C T trGS Sx sHC; have actGS := acts_act (atrans_acts trGS).
have:= sHC; rewrite subsetI sub_astab1; case/andP=> sHG cHx.
have Tx: x \in T by rewrite inE Sx.
apply: (iffP idP) => [trN | trC].
  apply/setP=> Ha; apply/setIdP/imsetP=> [[]|[a Ca ->{Ha}]]; last first.
    by rewrite conj_subG //; case/setIP: Ca => Ga _; rewrite mem_imset.
  case/imsetP=> a Ga ->{Ha}; rewrite subsetI !sub_conjg; case/andP=> _ sHCa.
  have Txa: to x a^-1 \in T.
    by rewrite inE -sub_astab1 astab1_act actGS ?Sx ?groupV.
  have [b] := atransP2 trN Tx Txa; case/setIP=> Gb nHb cxba.
  exists (b * a); last by rewrite conjsgM (normP nHb).
  by rewrite inE groupM //; apply/astab1P; rewrite actM -cxba actKV.
apply/imsetP; exists x => //; apply/setP=> y; apply/idP/idP=> [Ty|].
  have [Sy cHy]:= setIP Ty; have [a Ga defy] := atransP2 trGS Sx Sy.
  have: H :^ a^-1 \in H :^: C.
    rewrite -trC inE subsetI mem_imset 1?conj_subG ?groupV // sub_conjgV.
    by rewrite -astab1_act -defy sub_astab1.
  case/imsetP=> b; case/setIP=> Gb; move/astab1P=> cxb defHb.
  rewrite defy -{1}cxb -actM mem_orbit // inE groupM //.
  by apply/normP; rewrite conjsgM -defHb conjsgKV.
case/imsetP=> a; case/setIP=> Ga nHa ->{y}.
by rewrite inE actGS // Sx (acts_act (acts_fix_norm _) nHa).
Qed.

End TotalActions.

Implicit Arguments astabP [aT rT to S a].
Implicit Arguments astab1P [aT rT to x a].
Implicit Arguments astabsP [aT rT to S a].
Implicit Arguments atransP [aT rT to G S].
Implicit Arguments actsP [aT rT to A S].
Implicit Arguments faithfulP [aT rT to A S].
Prenex Implicits astabP astab1P astabsP atransP actsP faithfulP.

Section Restrict.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Variables (to : action D rT) (A : {set aT}).

Definition ract of A \subset D := act to.

Variable sAD : A \subset D.

Lemma ract_is_action : is_action A (ract sAD).
Proof.
rewrite /ract; case: to => f [injf fM].
split=> // x; exact: (sub_in2 (subsetP sAD)).
Qed.

Canonical Structure raction := Action ract_is_action.

Lemma ractE : raction =1 to. Proof. by []. Qed.

(* Other properties of raction need rT : finType; we defer them *)
(* until after the definition of actperm.                       *)

End Restrict.

Notation "to \ sAD" := (raction to sAD) (at level 50) : action_scope.

Section ActBy.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).

Definition actby_cond (A : {set aT}) R (to : action D rT) : Prop :=
  [acts A, on R | to].

Definition actby A R to of actby_cond A R to :=
  fun x a => if (x \in R) && (a \in A) then to x a else x.

Variables (A : {group aT}) (R : {set rT}) (to : action D rT).
Hypothesis nRA : actby_cond A R to.

Lemma actby_is_action : is_action A (actby nRA).
Proof.
rewrite /actby; split=> [a x y | x a b Aa Ab /=]; last first.
  rewrite Aa Ab groupM // !andbT actMin ?(subsetP (acts_dom nRA)) //.
  by case Rx: (x \in R); rewrite ?(acts_act nRA) ?Rx.
case Aa: (a \in A); rewrite ?andbF ?andbT //.
case Rx: (x \in R); case Ry: (y \in R) => // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy (acts_act nRA Aa) Rx in Ry.
by rewrite eqxy (acts_act nRA Aa) Ry in Rx.
Qed.

Canonical Structure action_by := Action actby_is_action.
Local Notation "<[nRA]>" := action_by : action_scope.

Lemma actbyE : forall x a, x \in R -> a \in A -> <[nRA]>%act x a = to x a.
Proof. by rewrite /= /actby => x a -> ->. Qed.

Lemma afix_actby : forall B, 'Fix_<[nRA]>(B) = ~: R :|: 'Fix_to(A :&: B).
Proof.
move=> B; apply/setP=> x; rewrite !inE /= /actby.
case: (x \in R); last by apply/subsetP=> a _; rewrite !inE.
apply/subsetP/subsetP=> [cBx a | cABx a Ba]; rewrite !inE.
  by case/andP=> Aa; move/cBx; rewrite inE Aa.
by case: ifP => //= Aa; have:= cABx a; rewrite !inE Aa => ->.
Qed.

Lemma astab_actby : forall S, 'C(S | <[nRA]>) = 'C_A(R :&: S | to).
Proof.
move=> S; apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> cRSa x => [|Sx].
  by case/setIP=> Rx; move/cRSa; rewrite !inE actbyE.
by have:= cRSa x; rewrite !inE /= /actby Aa Sx; case: (x \in R) => //; apply.
Qed.

Lemma astabs_actby : forall S, 'N(S | <[nRA]>) = 'N_A(R :&: S | to).
Proof.
move=> S; apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> nRSa x => [|Sx].
  by case/setIP=> Rx; move/nRSa; rewrite !inE actbyE ?(acts_act nRA) ?Rx.
have:= nRSa x; rewrite !inE /= /actby Aa Sx ?(acts_act nRA) //.
by case: (x \in R) => //; apply.
Qed.

Lemma acts_actby : forall (B : {set aT}) S,
  [acts B, on S | <[nRA]>] = (B \subset A) && [acts B, on R :&: S | to].
Proof. by move=> B S; rewrite astabs_actby subsetI. Qed.

End ActBy.

Notation "<[ nRA ] >" := (action_by nRA) : action_scope.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subFinType sP) (to : action D rT).
Implicit Type A : {set aT}.
Implicit Type u : sT.
Implicit Type S : {set sT}.

Definition subact_dom := 'N([set x | sP x] | to).
Canonical Structure subact_dom_group := [group of subact_dom].

Implicit Type Na : {a | a \in subact_dom}.
Lemma sub_act_proof : forall u Na, sP (to (val u) (val Na)).
Proof. by move=> u [a] /=; move/(astabs_act (val u)); rewrite !inE valP. Qed.

Definition subact u a :=
  if insub a is Some Na then Sub _ (sub_act_proof u Na) else u.

Lemma val_subact : forall u a,
  val (subact u a) = if a \in subact_dom then to (val u) a else val u.
Proof.
move=> u a; rewrite /subact -if_neg.
by case: insubP => [Na|] -> //=; rewrite SubK => ->.
Qed.

Lemma subact_is_action : is_action subact_dom subact.
Proof.
split=> [a u v eq_uv | u a b Na Nb]; apply: val_inj.
  move/(congr1 val): eq_uv; rewrite !val_subact.
  by case: (a \in _); first move/act_inj.
have Da := astabs_dom Na; have Db := astabs_dom Nb.
by rewrite !val_subact Na Nb groupM ?actMin.
Qed.

Canonical Structure subaction := Action subact_is_action.

Lemma astab_subact : forall S,
  'C(S | subaction) = subact_dom :&: 'C(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [cSa u | cSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}.
  by have:= cSa x Sx; rewrite inE -val_eqE val_subact sDa.
by have:= cSa _ (mem_imset val Sx); rewrite inE -val_eqE val_subact sDa.
Qed.

Lemma astabs_subact : forall S,
  'N(S | subaction) = subact_dom :&: 'N(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [nSa u | nSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}; have:= nSa x Sx; rewrite inE; move/(mem_imset val).
  by rewrite val_subact sDa.
have:= nSa _ (mem_imset val Sx); rewrite inE; case/imsetP=> y Sy def_y.
by rewrite ((_ a =P y) _) // -val_eqE val_subact sDa def_y.
Qed.

Lemma afix_subact : forall A,
  A \subset subact_dom -> 'Fix_subaction(A) = val @^-1: 'Fix_to(A).
Proof.
move=> A; move/subsetP=> sAD; apply/setP=> u.
rewrite !inE !(sameP setIidPl eqP); congr (_ == A).
apply/setP=> a; rewrite !inE; apply: andb_id2l => Aa.
by rewrite -val_eqE val_subact sAD.
Qed.

End SubAction.

Notation "to ^?" := (subaction _ to)
  (at level 2, format "to ^?") : action_scope.

Section QuotientAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finGroupType).
Variables (to : action D rT) (H : {group rT}).

Definition qact_dom := 'N(rcosets H 'N(H) | to^*).
Canonical Structure qact_dom_group := [group of qact_dom].

Local Notation subdom := (subact_dom (coset_range H)  to^*).
Fact qact_subdomE : subdom = qact_dom.
Proof. by congr 'N(_|_); apply/setP=> Hx; rewrite !inE genGid. Qed.
Lemma qact_proof : qact_dom \subset subdom.
Proof. by rewrite qact_subdomE. Qed.

Definition qact : coset_of H -> aT -> coset_of H := act (to^*^? \ qact_proof).

Canonical Structure quotient_action := [action of qact].

Lemma acts_qact_dom : [acts qact_dom, on 'N(H) | to].
Proof.
apply/subsetP=> a nNa; rewrite !inE (astabs_dom nNa); apply/subsetP=> x Nx.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
rewrite inE -(astabs_act _ nNa); case/rcosetsP=> y Ny defHy.
have: to x a \in H :* y by rewrite -defHy (mem_imset (to^~a)) ?rcoset_refl.
by apply: subsetP; rewrite mul_subG ?sub1set ?normG.
Qed.

Lemma qactEcond : forall x a,
    x \in 'N(H) ->
  quotient_action (coset H x) a =
     (if a \in qact_dom then coset H (to x a) else coset H x).
Proof.
move=> x a Nx; apply: val_inj; rewrite val_subact //= qact_subdomE.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
case nNa: (a \in _); rewrite // -(astabs_act _ nNa).
rewrite !val_coset ?(acts_act acts_qact_dom nNa) //=.
case/rcosetsP=> y Ny defHy; rewrite defHy; apply: rcoset_transl.
by rewrite rcoset_sym -defHy (mem_imset (_^~_)) ?rcoset_refl.
Qed.

Lemma qactE : forall x a,
    x \in 'N(H) -> a \in qact_dom ->
  quotient_action (coset H x) a = coset H (to x a).
Proof. by move=> x a Nx nNa; rewrite qactEcond ?nNa. Qed.

Lemma acts_quotient : forall (A : {set aT}) (B : {set rT}),
   A \subset 'N_qact_dom(B | to) -> [acts A, on B / H | quotient_action].
Proof.
move=> A B nBA; apply: subset_trans {A}nBA _; apply/subsetP=> a.
case/setIP=> dHa nBa; rewrite inE dHa inE; apply/subsetP=> Hx.
case/morphimP=> x nHx Bx ->; rewrite inE /= qactE //.
by rewrite mem_morphim ?(acts_act acts_qact_dom) ?(astabs_act _ nBa).
Qed.

Lemma astabs_quotient : forall G : {group rT},
   H <| G -> 'N(G / H | quotient_action) = 'N_qact_dom(G | to).
Proof.
move=> G nsHG; have [_ nHG] := andP nsHG.
apply/eqP; rewrite eqEsubset acts_quotient // andbT.
apply/subsetP=> a nGa; have dHa := astabs_dom nGa; have [Da _]:= setIdP dHa.
rewrite inE dHa 2!inE Da; apply/subsetP=> x Gx; have nHx := subsetP nHG x Gx.
rewrite -(quotientGK nsHG) 2!inE (acts_act acts_qact_dom) ?nHx //= inE.
by rewrite -qactE // (astabs_act _ nGa) mem_morphim.
Qed.

End QuotientAction.

Notation "to / H" := (quotient_action to H) : action_scope.

Section ModAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.
Implicit Type G : {group aT}.
Implicit Type S : {set rT}.

Section GenericMod.

Variable H : {group aT}.

Local Notation dom := 'N_D(H).
Local Notation range := 'Fix_to(D :&: H).
Let acts_dom : {acts dom, on range | to} := acts_act (acts_subnorm_fix to H).

Definition modact x (Ha : coset_of H) :=
  if x \in range then to x (repr (D :&: Ha)) else x.

Lemma modactEcond : forall x a,
  a \in dom -> modact x (coset H a) = (if x \in range then to x a else x).
Proof.
move=> x a; case/setIP=> Da Na; case: ifP => Cx; rewrite /modact Cx //.
rewrite val_coset // -group_modr ?sub1set //.
case: (repr _) / (repr_rcosetP (D :&: H) a) => a' Ha'.
by rewrite actMin ?(afixP Cx _ Ha') //; case/setIP: Ha'.
Qed.

Lemma modactE : forall x a,
  a \in D -> a \in 'N(H) -> x \in range ->  modact x (coset H a) = to x a.
Proof. by move=> x a Da Na Rx; rewrite modactEcond ?Rx // inE Da. Qed.

Lemma modact_is_action : is_action (D / H) modact.
Proof.
split=> [Ha x y | x Ha Hb]; last first.
  case/morphimP=> a Na Da ->{Ha}; case/morphimP=> b Nb Db ->{Hb}.
  rewrite -morphM //= !modactEcond // ?groupM ?(introT setIP _) //.
  by case: ifP => Cx; rewrite ?(acts_dom, Cx, actMin, introT setIP _).
case: (set_0Vmem (D :&: Ha)) => [Da0 | [a]].
  by rewrite /modact Da0 repr_set0 !act1 !if_same.
case/setIP=> Da NHa; have Na := subsetP (coset_norm _) _ NHa.
have NDa: a \in 'N_D(H) by rewrite inE Da.
rewrite -(coset_mem NHa) !modactEcond //.
do 2![case: ifP]=> Cy Cx // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy acts_dom ?Cx in Cy.
by rewrite eqxy acts_dom ?Cy in Cx.
Qed.

Canonical Structure mod_action := Action modact_is_action.

Section Stabilizers.

Variable S : {set rT}.
Hypothesis cSH : H \subset 'C(S | to).

Let fixSH : S \subset 'Fix_to(D :&: H).
Proof. by rewrite -astabCin ?subsetIl // subIset ?cSH ?orbT. Qed.

Lemma astabs_mod : 'N(S | mod_action) = 'N(S | to) / H.
Proof.
apply/setP=> Ha; apply/idP/morphimP=> [nSa | [a nHa nSa ->]].
  case/morphimP: (astabs_dom nSa) => a nHa Da defHa; exists a => //.
  rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by have:= Sx; rewrite -(astabs_act x nSa) defHa /= modactE ?(subsetP fixSH).
have Da := astabs_dom nSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astabs_act x nSa) ?(subsetP fixSH).
Qed.

Lemma astab_mod : 'C(S | mod_action) = 'C(S | to) / H.
Proof.
apply/setP=> Ha; apply/idP/morphimP=> [cSa | [a nHa cSa ->]].
  case/morphimP: (astab_dom cSa) => a nHa Da defHa; exists a => //.
  rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by rewrite -{2}[x](astab_act cSa) // defHa /= modactE ?(subsetP fixSH).
have Da := astab_dom cSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astab_act cSa) ?(subsetP fixSH).
Qed.

End Stabilizers.

Lemma afix_mod : forall G S,
    H \subset 'C(S | to) -> G \subset 'N_D(H) ->
  'Fix_(S | mod_action)(G / H) = 'Fix_(S | to)(G).
Proof.
move=> G S cSH; rewrite subsetI; case/andP=> sGD nHG.
apply/eqP; rewrite eqEsubset !subsetI !subsetIl /= -!astabCin ?quotientS //.
have cfixH: forall F, H \subset 'C(S :&: F | to).
  by move=> F; rewrite (subset_trans cSH) // astabS ?subsetIl.
rewrite andbC astab_mod ?quotientS //=; last by rewrite astabCin ?subsetIr.
by rewrite -(quotientSGK nHG) //= -astab_mod // astabCin ?quotientS ?subsetIr.
Qed.

End GenericMod.

Lemma modact_faithful : forall G S,
  [faithful G / 'C_G(S | to), on S | mod_action 'C_G(S | to)].
Proof.
move=> G S; rewrite /faithful astab_mod ?subsetIr //=.
by rewrite -quotientIG ?subsetIr ?trivg_quotient.
Qed.

End ModAction.

Notation "to %% H" := (mod_action to H) : action_scope.

Section ActPerm.
(* Morphism to permutations induced by an action. *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.

Definition actperm a := perm (act_inj to a).

Lemma actpermM : {in D &, {morph actperm : a b / a * b}}.
Proof. by move=> a b Da Db; apply/permP=> x; rewrite permM !permE actMin. Qed.

Canonical Structure actperm_morphism := Morphism actpermM.

Lemma actpermE : forall a x, actperm a x = to x a.
Proof. by move=> a x; rewrite permE. Qed.

Lemma actpermK : forall x a, aperm x (actperm a) = to x a.
Proof. move=> x a; exact: actpermE. Qed.

Lemma ker_actperm : 'ker actperm = 'C(setT | to).
Proof.
congr (_ :&: _); apply/setP=> a; rewrite !inE /=.
apply/eqP/subsetP=> [a1 x _ | a1]; first by rewrite inE -actpermE a1 perm1.
by apply/permP=> x; apply/eqP; have:= a1 x; rewrite !inE actpermE perm1 => ->.
Qed.

End ActPerm.

Section RestrictActionTheory.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variables (to : action D rT).

Lemma faithful_isom : forall (A : {group aT}) S (nSA : actby_cond A S to),
   [faithful A, on S | to] -> isom A (actperm <[nSA]> @* A) (actperm <[nSA]>).
Proof.
by move=> A S nSA ffulAS; apply/isomP; rewrite ker_actperm astab_actby setIT.
Qed.

Variables (A : {set aT}) (sAD : A \subset D).

Lemma ractpermE : actperm (to \ sAD) =1 actperm to.
Proof. by move=> a; apply/permP=> x; rewrite !permE. Qed.

Lemma afix_ract : forall B, 'Fix_(to \ sAD)(B) = 'Fix_to(B). Proof. by []. Qed.

Lemma astab_ract : forall S, 'C(S | to \ sAD) = 'C_A(S | to).
Proof. by move=> S; rewrite setIA (setIidPl sAD). Qed.

Lemma astabs_ract : forall S, 'N(S | to \ sAD) = 'N_A(S | to).
Proof. by move=> S; rewrite setIA (setIidPl sAD). Qed.

Lemma acts_ract : forall (B : {set aT}) S,
  [acts B, on S | to \ sAD] = (B \subset A) && [acts B, on S | to].
Proof. by move=> B S; rewrite astabs_ract subsetI. Qed.

End RestrictActionTheory.

Section MorphAct.
(* Action induced by a morphism to permutations. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable phi : {morphism D >-> {perm rT}}.

Definition mact x a := phi a x.

Lemma mact_is_action : is_action D mact.
Proof.
split=> [a x y | x a b Da Db]; first exact: perm_inj.
by rewrite /mact morphM //= permM.
Qed.

Canonical Structure morph_action := Action mact_is_action.

Lemma mactE : forall x a, morph_action x a = phi a x. Proof. by []. Qed.

Lemma injm_faithful : 'injm phi -> [faithful D, on setT | morph_action].
Proof.
move/injmP=> phi_inj; apply/subsetP=> a; case/setIP=> Da.
move/astab_act=> a1; apply/set1P; apply: phi_inj => //.
by apply/permP=> x; rewrite morph1 perm1 -mactE a1 ?inE.
Qed.

Lemma perm_mact : forall a, actperm morph_action a = phi a.
Proof. by move=> a; apply/permP=> x; rewrite permE. Qed.

End MorphAct.

Notation "<< phi >>" := (morph_action phi) : action_scope.

Section CompAct.

Variables (gT aT : finGroupType) (rT : finType).
Variables (D : {set aT}) (to : action D rT).
Variables (B : {set gT}) (f : {morphism B >-> aT}).

Definition comp_act x e := to x (f e).
Lemma comp_is_action : is_action (f @*^-1 D) comp_act.
Proof.
split=> [e | x e1 e2]; first exact: act_inj.
case/morphpreP=> Be1 Dfe1; case/morphpreP=> Be2 Dfe2.
by rewrite /comp_act morphM ?actMin.
Qed.
Canonical Structure comp_action := Action comp_is_action.

Lemma comp_actE : forall x e, comp_action x e = to x (f e). Proof. by []. Qed.

Lemma afix_comp : forall A : {set gT},
  A \subset B -> 'Fix_comp_action(A) = 'Fix_to(f @* A).
Proof.
move=> A sAB; apply/setP=> x; rewrite !inE /morphim (setIidPr sAB).
apply/subsetP/subsetP=> [cAx fa | cfAx a Aa].
  by case/imsetP=> a Aa ->; move/cAx: Aa; rewrite !inE.
by rewrite inE; move/(_ (f a)): cfAx; rewrite inE mem_imset // => ->.
Qed.

Lemma astab_comp : forall S, 'C(S | comp_action) = f @*^-1 'C(S | to).
Proof. by move=> S; apply/setP=> x; rewrite !inE -andbA. Qed.

Lemma astabs_comp : forall S, 'N(S | comp_action) = f @*^-1 'N(S | to).
Proof. by move=> S; apply/setP=> x; rewrite !inE -andbA. Qed.

End CompAct.

Notation "to \o f" := (comp_action to f) : action_scope.

Section PermAction.
(*  Natural action of permutation groups.                        *)

Variable rT : finType.
Local Notation gT := {perm rT}.
Implicit Types a b c : gT.

Lemma aperm_is_action : is_action setT (@aperm rT).
Proof.
by apply: is_total_action => [x|x a b]; rewrite apermE (perm1, permM).
Qed.

Canonical Structure perm_action := Action aperm_is_action.

Lemma pcycleE : forall a, pcycle a = orbit perm_action <[a]>%g.
Proof. by []. Qed.

Lemma perm_act1P : forall a, reflect (forall x, aperm x a = x) (a == 1).
Proof.
move=> a; apply: (iffP eqP) => [-> x | a1]; first exact: act1.
by apply/permP=> x; rewrite -apermE a1 perm1.
Qed.

Lemma perm_faithful : forall A, [faithful A, on setT | perm_action].
Proof.
move=> A; apply/subsetP=> a; case/setIP => Da crTa.
by apply/set1P; apply/permP=> x; rewrite -apermE perm1 (astabP crTa) ?inE.
Qed.

Lemma actperm_id : forall p, actperm perm_action p = p.
Proof. by move=> p; apply/permP=> x; rewrite permE. Qed.

End PermAction.

Implicit Arguments perm_act1P [rT a].
Prenex Implicits perm_act1P.

Notation "'P" := (perm_action _) (at level 0) : action_scope.

Section ActpermOrbits.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Lemma orbit_morphim_actperm : forall A : {set aT},
  A \subset D -> orbit 'P (actperm to @* A) =1 orbit to A.
Proof.
move=> A sAD x; rewrite morphimEsub // /orbit -imset_comp.
by apply: eq_imset => a //=; rewrite actpermK.
Qed.

Lemma pcycle_actperm : forall a : aT,
  a \in D -> pcycle (actperm to a) =1 orbit to <[a]>.
Proof.
move=> a Da x.
by rewrite pcycleE -orbit_morphim_actperm ?cycle_subG ?morphim_cycle.
Qed.

End ActpermOrbits.

Section RestrictPerm.

Variables (T : finType) (S : {set T}).

Definition restr_perm := actperm (<[subxx 'N(S | 'P)]>).
Canonical Structure restr_perm_morphism := [morphism of restr_perm].

Lemma restr_perm_on : forall p, perm_on S (restr_perm p).
Proof.
move=> ?; apply/subsetP=> x; apply: contraR => notSx.
by rewrite permE /= /actby (negPf notSx).
Qed.

Lemma triv_restr_perm : forall p, p \notin 'N(S | 'P) -> restr_perm p = 1.
Proof.
move=> p not_nSp; apply/permP=> x.
by rewrite !permE /= /actby (negPf not_nSp) andbF.
Qed.

Lemma restr_permE : {in 'N(S | 'P) & S, forall p, restr_perm p =1 p}.
Proof. by move=> ? x nSp Sx; rewrite /= actpermE actbyE. Qed.

Lemma ker_restr_perm : 'ker restr_perm = 'C(S | 'P).
Proof. by rewrite ker_actperm astab_actby setIT (setIidPr (astab_sub _ _)). Qed.

Lemma im_restr_perm : forall p, restr_perm p @: S = S.
Proof. by move=> p; exact: im_perm_on (restr_perm_on p). Qed.

End RestrictPerm.

Section AutIn.

Variable gT : finGroupType.

Definition Aut_in A (B : {set gT}) := 'N_A(B | 'P) / 'C_A(B | 'P).

Variables G H : {group gT}.
Hypothesis sHG: H \subset G.

Lemma Aut_restr_perm : forall a, a \in Aut G -> restr_perm H a \in Aut H.
Proof.
move=> a AutGa.
case nHa: (a \in 'N(H | 'P)); last by rewrite triv_restr_perm ?nHa ?group1.
rewrite inE restr_perm_on; apply/morphicP=> x y Hx Hy /=.
by rewrite !restr_permE ?groupM // -(autmE AutGa) morphM ?(subsetP sHG).
Qed.

Lemma restr_perm_Aut : restr_perm H @* Aut G \subset Aut H.
Proof.
by apply/subsetP=> a'; case/morphimP=> a _ AutGa ->{a'}; exact: Aut_restr_perm.
Qed.

Lemma Aut_in_isog : Aut_in (Aut G) H \isog restr_perm H @* Aut G.
Proof.
rewrite /Aut_in -ker_restr_perm kerE -morphpreIdom -morphimIdom -kerE /=.
by rewrite setIA (setIC _ (Aut G)) first_isog_loc ?subsetIr.
Qed.

Lemma Aut_sub_fullP :
  reflect (forall h : {morphism H >-> gT}, 'injm h -> h @* H = H ->
             exists g : {morphism G >-> gT},
             [/\ 'injm g, g @* G = G & {in H, g =1 h}])
          (Aut_in (Aut G) H \isog Aut H).
Proof.
rewrite (isog_transl _ Aut_in_isog) /=; set rG := _ @* _.
apply: (iffP idP) => [iso_rG h injh hH| AutHinG].
  have: aut injh hH \in rG; last case/morphimP=> g nHg AutGg def_g.
    suffices ->: rG = Aut H by exact: Aut_aut.
    by apply/eqP; rewrite eqEcard restr_perm_Aut /= (card_isog iso_rG).
  exists (autm_morphism AutGg); rewrite injm_autm im_autm; split=> // x Hx.
  by rewrite -(autE injh hH Hx) def_g actpermE actbyE.
suffices ->: rG = Aut H by exact: isog_refl.
apply/eqP; rewrite eqEsubset restr_perm_Aut /=.
apply/subsetP=> h AutHh; have hH := im_autm AutHh.
have [g [injg gG eq_gh]] := AutHinG _ (injm_autm AutHh) hH.
have [Ng AutGg]: aut injg gG \in 'N(H | 'P) /\ aut injg gG \in Aut G.
  rewrite Aut_aut !inE; split=> //; apply/subsetP=> x Hx.
  by rewrite inE /= /aperm autE ?(subsetP sHG) // -hH eq_gh ?mem_morphim.
apply/morphimP; exists (aut injg gG) => //; apply: (eq_Aut AutHh) => [|x Hx].
  by rewrite (subsetP restr_perm_Aut) // mem_morphim.
by rewrite restr_permE //= /aperm autE ?eq_gh ?(subsetP sHG).
Qed.

End AutIn.

Section InjmAutIn.

Variables (gT rT : finGroupType) (D G H : {group gT}) (f : {morphism D >-> rT}).
Hypotheses (injf : 'injm f) (sGD : G \subset D) (sHG : H \subset G).
Let sHD := subset_trans sHG sGD.
Local Notation fGisom := (Aut_isom injf sGD).
Local Notation fHisom := (Aut_isom injf sHD).
Local Notation inH := (restr_perm H).
Local Notation infH := (restr_perm (f @* H)).

Lemma astabs_Aut_isom : forall a,
  a \in Aut G -> (fGisom a \in 'N(f @* H | 'P)) = (a \in 'N(H | 'P)).
Proof.
move=> a AutGa; rewrite !inE sub_morphim_pre // subsetI sHD /= /aperm.
rewrite !(sameP setIidPl eqP) !eqEsubset !subsetIl; apply: eq_subset_r => x.
rewrite !inE; apply: andb_id2l => Hx; have Gx: x \in G := subsetP sHG x Hx.
have Dax: a x \in D by rewrite (subsetP sGD) // Aut_closed.
by rewrite Aut_isomE // -!sub1set -morphim_set1 // injmSK ?sub1set.
Qed.

Lemma isom_restr_perm : forall a,
  a \in Aut G -> fHisom (inH a) = infH (fGisom a).
Proof.
move=> a AutGa; case nHa: (a \in 'N(H | 'P)); last first.
  by rewrite !triv_restr_perm ?astabs_Aut_isom ?nHa ?morph1.
apply: (eq_Aut (Aut_Aut_isom injf sHD _)) => [|fx Hfx /=].
  by rewrite (Aut_restr_perm (morphimS f sHG)) ?Aut_Aut_isom.
have [x Dx Hx def_fx] := morphimP Hfx; have Gx := subsetP sHG x Hx.
rewrite {1}def_fx Aut_isomE ?(Aut_restr_perm sHG) //.
by rewrite !restr_permE ?astabs_Aut_isom // def_fx Aut_isomE.
Qed.

Lemma restr_perm_isom : isom (inH @* Aut G) (infH @* Aut (f @* G)) fHisom.
Proof.
apply: sub_isom; rewrite ?restr_perm_Aut ?injm_Aut_isom //=.
rewrite -(im_Aut_isom injf sGD) -!morphim_comp.
apply: eq_in_morphim; last exact: isom_restr_perm.
apply/setP=> a; rewrite 2!in_setI; apply: andb_id2r => AutGa.
rewrite /= inE andbC inE (Aut_restr_perm sHG) //=.
by symmetry; rewrite inE AutGa inE astabs_Aut_isom.
Qed.

Lemma injm_Aut_sub : Aut_in (Aut (f @* G)) (f @* H) \isog Aut_in (Aut G) H.
Proof.
do 2!rewrite isog_sym (isog_transl _ (Aut_in_isog _ _)).
by rewrite isog_sym (isom_isog _ _ restr_perm_isom) // restr_perm_Aut.
Qed.

Lemma injm_Aut_full :
  (Aut_in (Aut (f @* G)) (f @* H) \isog Aut (f @* H))
      = (Aut_in (Aut G) H \isog Aut H).
Proof.
by rewrite (isog_transl _ injm_Aut_sub) (isog_transr _ (injm_Aut injf sHD)).
Qed.

End InjmAutIn.

Section GroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Local Notation actT := (action D rT).

Definition is_groupAction (to : actT) :=
  {in D, forall a, actperm to a \in Aut R}.

Structure groupAction := GroupAction {gact :> actT; _ : is_groupAction gact}.

Definition clone_groupAction to :=
  let: GroupAction _ toA := to return {type of GroupAction for to} -> _ in
  fun k => k toA : groupAction.

End GroupAction.

Delimit Scope groupAction_scope with gact.
Bind Scope groupAction_scope with groupAction.
Arguments Scope gact [_ _ group_scope group_scope groupAction_scope].

Notation "[ 'groupAction' 'of' to ]" :=
     (clone_groupAction (@GroupAction _ _ _ _ to))
  (at level 0, format "[ 'groupAction'  'of'  to ]") : form_scope.

Section GroupActionDefs.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.
Implicit Type to : groupAction D R.

Definition gact_range of groupAction D R := R.

Definition gacent to A := 'Fix_(R | to)(D :&: A).

Definition acts_on_group A S to := [acts A, on S | to] /\ S \subset R.

Coercion actby_cond_group A S to : acts_on_group A S to -> actby_cond A S to :=
  @proj1 _ _.

Definition acts_irreducibly A S to :=
  [min S of G | (G :!=: 1) && [acts A, on G | to]].

End GroupActionDefs.

Notation "''C_' ( | to ) ( A )" := (gacent to A)
  (at level 8, format "''C_' ( | to ) ( A )") : group_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))
  (at level 8, format "''C_' ( G  |  to ) ( A )") : group_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a])
  (at level 8, format "''C_' ( | to ) [ a ]") : group_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a])
  (at level 8, format "''C_' ( G  |  to ) [ a ]") : group_scope.

Notation "{ 'acts' A , 'on' 'group' G | to }" := (acts_on_group A G to)
  (at level 0, format "{ 'acts'  A ,  'on'  'group'  G  |  to }") : form_scope.

Section RawGroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Variable to : groupAction D R.

Lemma actperm_Aut : is_groupAction R to. Proof. by case: to. Qed.

Lemma im_actperm_Aut : actperm to @* D \subset Aut R.
Proof. apply/subsetP=> pa; case/morphimP=> a _ Da ->; exact: actperm_Aut. Qed.

Lemma gact_out : forall x a, a \in D -> x \notin R -> to x a = x.
Proof. by move=> x a Da Rx; rewrite -actpermE (out_Aut _ Rx) ?actperm_Aut. Qed.

Lemma gactM : {in D, forall a, {in R &, {morph to^~ a : x y / x * y}}}.
Proof.
move=> a Da /= x y; rewrite -!(actpermE to); apply: morphicP x y.
by rewrite Aut_morphic ?actperm_Aut.
Qed.

Lemma actmM : forall a, {in R &, {morph actm to a : x y / x * y}}.
Proof. rewrite /actm => a; case: ifP => //; exact: gactM. Qed.

Canonical Structure act_morphism a := Morphism (actmM a).

Lemma morphim_actm :
  {in D, forall a (S : {set rT}), S \subset R -> actm to a @* S = to^* S a}.
Proof. by move=> a Da /= S ?; rewrite /morphim /= actmEfun ?(setIidPr _). Qed.

Variables (a : aT) (A B : {set aT}) (S : {set rT}).

Lemma gacentIdom : 'C_(|to)(D :&: A) = 'C_(|to)(A).
Proof. by rewrite /gacent setIA setIid. Qed.

Lemma gacentIim : 'C_(R | to)(A) = 'C_(|to)(A).
Proof. by rewrite setIA setIid. Qed.

Lemma gacentS : A \subset B -> 'C_(|to)(B) \subset 'C_(|to)(A).
Proof. by move=> sAB; rewrite !(setIS, afixS). Qed.  

Lemma gacentU : 'C_(|to)(A :|: B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof. by rewrite -setIIr -afixU -setIUr. Qed.

Hypotheses (Da : a \in D) (sAD : A \subset D) (sSR : S \subset R).

Lemma gacentE : 'C_(|to)(A) = 'Fix_(R | to)(A).
Proof. by rewrite -{2}(setIidPr sAD). Qed.

Lemma gacent1E : 'C_(|to)[a] = 'Fix_(R | to)[a].
Proof. by rewrite /gacent [D :&: _](setIidPr _) ?sub1set. Qed.

Lemma subgacentE : 'C_(S | to)(A) = 'Fix_(S | to)(A).
Proof. by rewrite gacentE setIA (setIidPl sSR). Qed.

Lemma subgacent1E : 'C_(S | to)[a] = 'Fix_(S | to)[a].
Proof. by rewrite gacent1E setIA (setIidPl sSR). Qed.

End RawGroupAction.

Section GroupActionTheory.

Variables aT rT : finGroupType.
Variables (D : {group aT}) (R : {group rT}) (to : groupAction D R).
Implicit Type A B : {set aT}.
Implicit Types G H : {group aT}.
Implicit Type S : {set rT}.
Implicit Types M N : {group rT}.

Lemma gact1 : {in D, forall a, to 1 a = 1}.
Proof. by move=> a Da; rewrite /= -actmE ?morph1. Qed.

Lemma gactV : {in D, forall a, {in R, {morph to^~ a : x / x^-1}}}.
Proof. by move=> a Da /= x Rx; move; rewrite -!actmE ?morphV. Qed.

Lemma gactX : {in D, forall a n, {in R, {morph to^~ a : x / x ^+ n}}}.
Proof. by move=> a Da /= n x Rx; rewrite -!actmE // morphX. Qed.

Lemma gactJ : {in D, forall a, {in R &, {morph to^~ a : x y / x ^ y}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphJ. Qed.

Lemma gactR : {in D, forall a, {in R &, {morph to^~ a : x y / [~ x, y]}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphR. Qed.

Lemma gact_stable : {acts D, on R | to}.
Proof.
apply: acts_act; apply/subsetP=> a Da; rewrite !inE Da.
apply/subsetP=> x; rewrite inE; apply: contraLR => R'xa.
by rewrite -(actKin to Da x) gact_out ?groupV.
Qed.

Lemma group_set_gacent : forall A, group_set 'C_(|to)(A).
Proof.
move=> A; apply/group_setP; split=> [|x y].
  rewrite !inE group1; apply/subsetP=> a; case/setIP=> Da _.
  by rewrite inE gact1.
case/setIP=> Rx; move/afixP=> cAx; case/setIP=> Ry; move/afixP=> cAy.
rewrite inE groupM //; apply/afixP=> a Aa.
by rewrite gactM ?cAx ?cAy //; case/setIP: Aa.
Qed.

Canonical Structure gacent_group A := Group (group_set_gacent A).

Lemma gacent1 : 'C_(|to)(1) = R.
Proof. by rewrite /gacent (setIidPr (sub1G _)) afix1 setIT. Qed.

Lemma gacent_gen : forall A, A \subset D -> 'C_(|to)(<<A>>) = 'C_(|to)(A).
Proof.
by move=> A sAD; rewrite /gacent ![D :&: _](setIidPr _) ?gen_subG ?afix_gen_in.
Qed.

Lemma gacentD1 : forall A, 'C_(|to)(A^#) = 'C_(|to)(A).
Proof.
move=> A; rewrite -gacentIdom -gacent_gen ?subsetIl // setDE setIA -setDE.
by rewrite genD1 ?group1 // gacent_gen ?subsetIl // gacentIdom.
Qed.

Lemma gacent_cycle : forall a, a \in D -> 'C_(|to)(<[a]>) = 'C_(|to)[a].
Proof. by move=> a Da; rewrite gacent_gen ?sub1set. Qed.

Lemma gacentY : forall A B,
  A \subset D -> B \subset D -> 'C_(|to)(A <*> B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof. by move=> A B sAD sBD; rewrite gacent_gen ?gacentU // subUset sAD. Qed.

Lemma gacentM : forall G H,
  G \subset D -> H \subset D -> 'C_(|to)(G * H) = 'C_(|to)(G) :&: 'C_(|to)(H).
Proof.
by move=> G H sGD sHB; rewrite -gacent_gen ?mul_subG // genM_join gacentY.
Qed.

Lemma astab1 : 'C(1 | to) = D.
Proof. 
by apply/setP=> x; rewrite ?(inE, sub1set) andb_idr //; move/gact1=> ->. 
Qed.

Lemma astab_range : 'C(R | to) = 'C(setT | to).
Proof.
apply/eqP; rewrite eqEsubset andbC astabS ?subsetT //=.
apply/subsetP=> a cRa; have Da := astab_dom cRa; rewrite !inE Da.
apply/subsetP=> x; rewrite -(setUCr R) !inE.
by case/orP=> ?; [rewrite (astab_act cRa) | rewrite gact_out].
Qed.

Lemma gacentC : forall A S,
    A \subset D -> S \subset R ->
  (S \subset 'C_(|to)(A)) = (A \subset 'C(S | to)).
Proof.
by move=> A S sAD sSR; rewrite subsetI sSR astabCin // (setIidPr sAD).
Qed.

Lemma astab_gen : forall S, S \subset R -> 'C(<<S>> | to) = 'C(S | to).
Proof.
move=> S sSR; apply/setP=> a; case Da: (a \in D); last by rewrite !inE Da.
by rewrite -!sub1set -!gacentC ?sub1set ?gen_subG.
Qed.

Lemma astabM : forall M N,
  M \subset R -> N \subset R -> 'C(M * N | to) = 'C(M | to) :&: 'C(N | to).
Proof.
move=> M N sMR sNR; rewrite -astabU -astab_gen ?mul_subG // genM_join.
by rewrite astab_gen // subUset sMR.
Qed.

Lemma astabs1 : 'N(1 | to) = D.
Proof. by rewrite astabs_set1 astab1. Qed.

Lemma astabs_range : 'N(R | to) = D.
Proof.
apply/setIidPl; apply/subsetP=> a Da; rewrite inE.
by apply/subsetP=> x Rx; rewrite inE gact_stable.
Qed.

Lemma astabsD1 : forall S, 'N(S^# | to) = 'N(S | to).
Proof.
move=> S; case S1: (1 \in S); last first.
  by rewrite (setDidPl _) // disjoint_sym disjoints_subset sub1set inE S1.
apply/eqP; rewrite eqEsubset andbC -{1}astabsIdom -{1}astabs1 setIC astabsD /=.
by rewrite -{2}(setD1K S1) -astabsIdom -{1}astabs1 astabsU.
Qed.

Lemma gacts_range : forall A, A \subset D -> {acts A, on group R | to}.
Proof. by move=> A sAD; split; rewrite ?astabs_range. Qed.

Lemma acts_subnorm_gacent : forall A,
  A \subset D -> [acts 'N_D(A), on 'C_(| to)(A) | to].
Proof.
move=> A sAD; rewrite gacentE // actsI ?astabs_range ?subsetIl //.
by rewrite -{2}(setIidPr sAD) acts_subnorm_fix.
Qed.

Lemma acts_subnorm_subgacent : forall A B S,
  A \subset D -> [acts B, on S | to] -> [acts 'N_B(A), on 'C_(S | to)(A) | to].
Proof.
move=> A B S sAD actsB; rewrite actsI //; first by rewrite subIset ?actsB.
by rewrite (subset_trans _ (acts_subnorm_gacent sAD)) ?setSI ?(acts_dom actsB).
Qed.

Lemma acts_gen : forall A S,
  S \subset R -> [acts A, on S | to] -> [acts A, on <<S>> | to].
Proof.
move=> A S sSR actsA; apply: {A}subset_trans actsA _.
apply/subsetP=> a nSa; have Da := astabs_dom nSa; rewrite !inE Da.
apply: subset_trans (_ : <<S>> \subset actm to a @*^-1 <<S>>) _.
  rewrite gen_subG subsetI sSR; apply/subsetP=> x Sx.
  by rewrite inE /= actmE ?mem_gen // astabs_act.
by apply/subsetP=> x; rewrite !inE; case/andP=> Rx; rewrite /= actmE.
Qed.

Lemma acts_joing : forall A M N,
    M \subset R -> N \subset R -> [acts A, on M | to] -> [acts A, on N | to] ->
  [acts A, on M <*> N | to].
Proof.
by move=> A M N sMR sNR nMA nNA; rewrite acts_gen ?actsU // subUset sMR.
Qed.

Lemma injm_actm : forall a, 'injm (actm to a).
Proof.
move=> a; apply/injmP=> x y Rx Ry; rewrite /= /actm; case: ifP => Da //.
exact: act_inj.
Qed.

Lemma im_actm : forall a, actm to a @* R = R.
Proof.
move=> a; apply/eqP; rewrite eqEcard (card_injm (injm_actm a)) // leqnn andbT.
apply/subsetP=> xa; case/morphimP=> x Rx _ ->{xa} /=.
by rewrite /actm; case: ifP => // Da; rewrite gact_stable.
Qed.

Lemma acts_char : forall G M, G \subset D -> M \char R -> [acts G, on M | to].
Proof.
move=> G M sGD; case/charP=> sMR charM.
apply/subsetP=> a Ga; have Da := subsetP sGD a Ga; rewrite !inE Da.
apply/subsetP=> x Mx; have Rx := subsetP sMR x Mx.
by rewrite inE -(charM _ (injm_actm a) (im_actm a)) -actmE // mem_morphim.
Qed.

Lemma gacts_char : forall G M,
  G \subset D -> M \char R -> {acts G, on group M | to}.
Proof. by move=> G M sGD charM; split; rewrite (acts_char, char_sub). Qed.

Section Restrict.

Variables (A : {group aT}) (sAD : A \subset D).

Lemma ract_is_groupAction : is_groupAction R (to \ sAD).
Proof. by move=> a Aa /=; rewrite ractpermE actperm_Aut ?(subsetP sAD). Qed.

Canonical Structure ract_groupAction := GroupAction ract_is_groupAction.

Lemma gacent_ract : forall B, 'C_(|ract_groupAction)(B) = 'C_(|to)(A :&: B).
Proof. by move=> B; rewrite /gacent afix_ract setIA (setIidPr sAD). Qed.

End Restrict.

Section ActBy.

Variables (A : {group aT}) (G : {group rT}) (nGAg : {acts A, on group G | to}).

Lemma actby_is_groupAction : is_groupAction G <[nGAg]>.
Proof.
move=> a Aa; rewrite /= inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR => Gx.
  by rewrite actpermE /= /actby (negbTE Gx).
apply/morphicP=> x y Gx Gy; rewrite !actpermE /= /actby Aa groupM ?Gx ?Gy //=.
by case nGAg; move/acts_dom; do 2!move/subsetP=> ?; rewrite gactM; auto.
Qed.

Canonical Structure actby_groupAction := GroupAction actby_is_groupAction.

Lemma gacent_actby : forall B,
  'C_(|actby_groupAction)(B) = 'C_(G | to)(A :&: B).
Proof.
move=> B; rewrite /gacent afix_actby !setIA setIid setIUr setICr set0U.
by have [nAG sGR] := nGAg; rewrite (setIidPr (acts_dom nAG)) (setIidPl sGR).
Qed.

End ActBy.

Section Quotient.

Variable H : {group rT}.

Lemma acts_qact_dom_norm : {acts qact_dom to H, on 'N(H) | to}.
Proof.
move=> a HDa /= x; rewrite {2}(('N(H) =P to^~ a @^-1: 'N(H)) _) ?inE {x}//.
rewrite eqEcard (card_preimset _ (act_inj _ _)) leqnn andbT.
apply/subsetP=> x Nx; rewrite inE; move/(astabs_act (H :* x)): HDa.
rewrite mem_rcosets mulSGid ?normG // Nx; case/rcosetsP=> y Ny defHy.
have: H :* y \subset 'N(H) by rewrite mul_subG ?sub1set ?normG.
move/subsetP; apply; rewrite -defHy; apply: mem_imset; exact: rcoset_refl.
Qed.

Lemma qact_is_groupAction : is_groupAction (R / H) (to / H).
Proof.
move=> a HDa /=; have Da := astabs_dom HDa.
rewrite inE; apply/andP; split.
  apply/subsetP=> Hx /=; case: (cosetP Hx) => x Nx ->{Hx}.
  apply: contraR => R'Hx; rewrite actpermE qactE // gact_out //.
  by apply: contra R'Hx; apply: mem_morphim.
apply/morphicP=> Hx Hy; rewrite !actpermE.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM ?qactE ?groupM ?gactM // morphM ?acts_qact_dom_norm.
Qed.

Canonical Structure quotient_groupAction := GroupAction qact_is_groupAction.

Lemma qact_domE : H \subset R -> qact_dom to H = 'N(H | to).
Proof.
move=> sHR; apply/setP=> a; apply/idP/idP=> nHa; have Da := astabs_dom nHa.
  rewrite !inE Da; apply/subsetP=> x Hx; rewrite inE.
  have: to^~ a @: H \in rcosets H 'N(H).
    by rewrite (astabs_act _ nHa) -{1}(mulg1 H) -rcosetE mem_imset ?group1.
  case/rcosetsP=> y Ny defHy; rewrite -(rcoset1 H).
  by rewrite (@rcoset_transl _ H 1 y) -defHy -1?(gact1 Da) mem_setact.
rewrite !inE Da; apply/subsetP=> Hx; rewrite inE; case/rcosetsP=> x Nx ->{Hx}.
apply/imsetP; exists (to x a).
  case Rx: (x \in R); last by rewrite gact_out ?Rx.
  rewrite inE; apply/subsetP=> ya; case/imsetP=> y Hy ->{ya}.
  rewrite -(actKVin to Da y) -gactJ // ?(subsetP sHR, astabs_act, groupV) //.
  by rewrite memJ_norm // astabs_act ?groupV.
apply/eqP; rewrite rcosetE eqEcard.
rewrite (card_imset _ (act_inj _ _)) !card_rcoset leqnn andbT.
apply/subsetP=> ya; case/imsetP=> y; rewrite !mem_rcoset=> Hxy ->{ya}.
have Rxy := subsetP sHR _ Hxy; rewrite -(mulgKV x y).
case Rx: (x \in R); last by rewrite !gact_out ?mulgK // 1?groupMl ?Rx.
by rewrite -gactV // -gactM 1?groupMr ?groupV // mulgK astabs_act.
Qed.

End Quotient.

Section Mod.

Variable H : {group aT}.

Lemma modact_is_groupAction : is_groupAction 'C_(|to)(H) (to %% H).
Proof.
move=> Ha; case/morphimP=> a Na Da ->.
have NDa: a \in 'N_D(H) by exact/setIP.
rewrite inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR.
  rewrite inE andbC actpermE /= modactEcond //.
  by case: ifP => // E Rx; rewrite ?E in Rx; rewrite gact_out.
apply/morphicP=> x y; case/setIP=> Rx cHx; case/setIP=> Ry cHy.
rewrite /= !actpermE /= !modactE ?gactM //.
suff: x * y \in 'C_(|to)(H) by case/setIP.
rewrite groupM //; exact/setIP.
Qed.

Canonical Structure mod_groupAction := GroupAction modact_is_groupAction.

Lemma modgactE : forall x a,
  H \subset 'C(R | to) -> a \in 'N_D(H) -> (to %% H)%act x (coset H a) = to x a.
Proof.
move=> x a cRH NDa; have [Da Na] := setIP NDa.
case Rx: (x \in R).
  rewrite /= modactE //.
  by apply/afixP=> b; case/setIP=> _; move/(subsetP cRH); move/astab_act->.
rewrite gact_out ?inE ?Rx //= /modact; case: ifP => // _.
rewrite gact_out ?Rx //.
have sHaD: coset H a \subset D.
  rewrite val_coset // mul_subG ?sub1set //.
  by apply: subset_trans cRH _; apply/subsetP=> b; case/setIdP.
by rewrite (setIidPr _) // (subsetP sHaD) // mem_repr_coset.
Qed.

Lemma gacent_mod : forall G M,
    H \subset 'C(M | to) -> G \subset 'N(H) ->
 'C_(M | mod_groupAction)(G / H) = 'C_(M | to)(G).
Proof.
move=> G M cMH nHG; rewrite -gacentIdom gacentE ?subsetIl // setICA.
have sHD: H \subset D by rewrite (subset_trans cMH) ?subsetIl.
rewrite -quotientGI // afix_mod ?setIS // setICA -gacentIim (setIC R) -setIA.
rewrite -gacentE ?subsetIl // gacentIdom setICA (setIidPr _) //.
by rewrite gacentC // ?(subset_trans cMH) ?astabS ?subsetIl // setICA subsetIl.
Qed.

Lemma acts_irr_mod : forall G M,
    H \subset 'C(M | to) -> G \subset 'N(H) -> acts_irreducibly G M to ->
  acts_irreducibly (G / H) M mod_groupAction.
Proof.
move=> G M cMH nHG; case/mingroupP; case/andP=> ntM nMG minM.
apply/mingroupP; rewrite ntM astabs_mod ?quotientS //; split=> // L modL ntL.
have cLH: H \subset 'C(L | to) by rewrite (subset_trans cMH) ?astabS //.
apply: minM => //; case/andP: modL => ->; rewrite astabs_mod ?quotientSGK //.
by rewrite (subset_trans cLH) ?astab_sub.
Qed.
  
End Mod.

Lemma modact_coset_astab : forall x a,
  a \in D -> (to %% 'C(R | to))%act x (coset _ a) = to x a.
Proof.
move=> x a Da; apply: modgactE => {x}//.
rewrite !inE Da; apply/subsetP=> ca; case/imsetP=> c Cc ->{ca}.
have Dc := astab_dom Cc; rewrite !inE groupJ //.
apply/subsetP=> x Rx; rewrite inE conjgE !actMin ?groupM ?groupV //.
by rewrite (astab_act Cc) ?actKVin // gact_stable ?groupV.
Qed.

Lemma acts_irr_mod_astab : forall G M,
    acts_irreducibly G M to ->
  acts_irreducibly (G / 'C_G(M | to)) M (mod_groupAction _).
Proof.
move=> G M irrG; have [_ nMG] := andP (mingroupp irrG).
apply: acts_irr_mod irrG; first exact: subsetIr.
by rewrite normsI ?normG // (subset_trans nMG) // astab_norm.
Qed.
  
Section CompAct.

Variables (gT : finGroupType) (G : {group gT}) (f : {morphism G >-> aT}).

Lemma comp_is_groupAction : is_groupAction R (comp_action to f).
Proof.
move=> a; case/morphpreP=> Ba Dfa; apply: etrans (actperm_Aut to Dfa).
by congr (_ \in Aut R); apply/permP=> x; rewrite !actpermE.
Qed.
Canonical Structure comp_groupAction := GroupAction comp_is_groupAction.

Lemma gacent_comp : forall U, 'C_(|comp_groupAction)(U) = 'C_(|to)(f @* U).
Proof.
move=> U; rewrite /gacent afix_comp ?subIset ?subxx //.
by rewrite -(setIC U) (setIC D) morphim_setIpre.
Qed.

End CompAct.

End GroupActionTheory.

Notation "''C_' ( | to ) ( A )" := (gacent_group to A) : subgroup_scope.
Notation "''C_' ( G | to ) ( A )" :=
  (setI_group G 'C_(|to)(A)) : subgroup_scope.
Notation "''C_' ( | to ) [ a ]" := (gacent_group to [set a%g]) : subgroup_scope.
Notation "''C_' ( G | to ) [ a ]" :=
  (setI_group G 'C_(|to)[a]) : subgroup_scope.

Notation "to \ sAD" := (ract_groupAction to sAD) : groupAction_scope.
Notation "<[ nGA ] >" := (actby_groupAction nGA) : groupAction_scope.
Notation "to / H" := (quotient_groupAction to H) : groupAction_scope.
Notation "to %% H" := (mod_groupAction to H) : groupAction_scope.
Notation "to \o f" := (comp_groupAction to f) : groupAction_scope.

(* Conjugation and right translation actions. *)

Section InternalActionDefs.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

(* This is not a Canonical Structure because it is seldom used, and it would *)
(* cause too many spurious matches (any group product would be viewed as an  *)
(* action!).                                                                 *)
Definition mulgr_action := TotalAction (@mulg1 gT) (@mulgA gT).

Canonical Structure conjg_action := TotalAction (@conjg1 gT) (@conjgM gT).

Lemma conjg_is_groupAction : is_groupAction setT conjg_action.
Proof.
move=> a _; rewrite /= inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= conjMg.
Qed.

Canonical Structure conjg_groupAction := GroupAction conjg_is_groupAction.

Lemma rcoset_is_action : is_action setT (@rcoset gT).
Proof.
by apply: is_total_action => [A|A x y]; rewrite !rcosetE (mulg1, rcosetM).
Qed.

Canonical Structure rcoset_action := Action rcoset_is_action.

Canonical Structure conjsg_action := TotalAction (@conjsg1 gT) (@conjsgM gT).

Lemma conjG_is_action : is_action setT (@conjG_group gT).
Proof.
apply: is_total_action => [G | G x y]; apply: val_inj; rewrite /= ?act1 //.
exact: actM.
Qed.

Definition conjG_action := Action conjG_is_action.

End InternalActionDefs.

Notation "'R" := (@mulgr_action _) (at level 0) : action_scope.
Notation "'Rs" := (@rcoset_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_groupAction _) (at level 0) : groupAction_scope.
Notation "'Js" := (@conjsg_action _) (at level 0) : action_scope.
Notation "'JG" := (@conjG_action _) (at level 0) : action_scope.
Notation "'Q" := ('J / _)%act (at level 0) : action_scope.
Notation "'Q" := ('J / _)%gact (at level 0) : groupAction_scope.

Section InternalGroupAction.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.
Implicit Type x : gT.

(*  Various identities for actions on groups. *)

Lemma orbitR : forall G x, orbit 'R G x = x *: G.
Proof. by move=> G x; rewrite -lcosetE. Qed.

Lemma astab1R : forall x, 'C[x | 'R] = 1.
Proof.
move=> x; apply/trivgP; apply/subsetP=> y cxy.
by rewrite -(mulKg x y) [x * y](astab1P cxy) mulVg set11.
Qed.

Lemma astabR : forall G, 'C(G | 'R) = 1.
Proof.
move=> G; apply/trivgP; apply/subsetP=> x cGx.
by rewrite -(mul1g x) [1 * x](astabP cGx) group1.
Qed.

Lemma astabsR : forall G, 'N(G | 'R) = G.
Proof.
move=> G; apply/setP=> x; rewrite !inE -setactVin ?inE //=.
by rewrite -groupV -{1 3}(mulg1 G) rcoset_sym -sub1set -mulGS -!rcosetE.
Qed.

Lemma atransR : forall G, [transitive G, on G | 'R].
Proof. by move=> G; rewrite /atrans -{1}(mul1g G) -orbitR mem_imset. Qed.

Lemma faithfulR : forall G, [faithful G, on G | 'R].
Proof. by move=> G; rewrite /faithful astabR subsetIr. Qed.

Definition Cayley_repr G := actperm <[atrans_acts (atransR G)]>.

Theorem Cayley_isom : forall G, isom G (Cayley_repr G @* G) (Cayley_repr G).
Proof. move=> G; exact: faithful_isom (faithfulR G). Qed.

Theorem Cayley_isog : forall G, G \isog Cayley_repr G @* G.
Proof. move=> G; exact: isom_isog (Cayley_isom G). Qed.

Lemma orbitJ : forall G x, orbit 'J G x = x ^: G. Proof. by []. Qed.

Lemma afixJ : forall A, 'Fix_'J(A) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma astabJ : forall A, 'C(A |'J) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma astab1J : forall x, 'C[x |'J] = 'C[x].
Proof. by move=> x; rewrite astabJ cent_set1. Qed.

Lemma astabsJ : forall A, 'N(A | 'J) = 'N(A).
Proof.
by move=> A; apply/setP=> x; rewrite -2!groupV !inE -conjg_preim -sub_conjg.
Qed.

Lemma setactJ : forall A x, 'J^*%act A x = A :^ x. Proof. by []. Qed.

Lemma gacentJ : forall A, 'C_(|'J)(A) = 'C(A).
Proof. by move=> A; rewrite gacentE ?setTI ?subsetT ?afixJ. Qed.

Lemma orbitRs : forall G A, orbit 'Rs G A = rcosets A G. Proof. by []. Qed.

Lemma sub_afixRs_norms : forall G x A,
 (G :* x \in 'Fix_'Rs(A)) = (A \subset G :^ x).
Proof.
move=> G x A; rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite eqEcard card_rcoset leqnn andbT mulgA (conjgCV x) mulgK.
by rewrite -{2 3}(mulGid G) mulGS sub1set -mem_conjg.
Qed.

Lemma sub_afixRs_norm : forall G x, (G :* x \in 'Fix_'Rs(G)) = (x \in 'N(G)).
Proof. by move=> G x; rewrite sub_afixRs_norms -groupV inE sub_conjgV. Qed.

Lemma afixRs_rcosets : forall A G,
  'Fix_(rcosets G A | 'Rs)(G) = rcosets G 'N_A(G).
Proof.
move=> A G; apply/setP=> Gx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Ax ->{Gx}; rewrite sub_afixRs_norm => Nx.
  by exists x; rewrite // inE Ax.
by case/setIP=> Ax Nx ->; rewrite -{1}rcosetE mem_imset // sub_afixRs_norm.
Qed.

Lemma astab1Rs : forall G, 'C[G : {set gT} | 'Rs] = G.
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE ?rcoset_refl ?rcoset_id.
Qed.

Lemma actsRs_rcosets : forall H G, [acts G, on rcosets H G | 'Rs].
Proof. by move=> H G; rewrite -orbitRs acts_orbit ?subsetT. Qed.

Lemma transRs_rcosets : forall H G, [transitive G, on rcosets H G | 'Rs].
Proof. by move=> H G; rewrite -orbitRs atrans_orbit. Qed.

(* This is the second part of Aschbacher (5.7) *)
Lemma astabRs_rcosets : forall H G, 'C(rcosets H G | 'Rs) = gcore H G.
Proof.
move=> H G; have transGH := transRs_rcosets H G.
by rewrite (astab_trans_gcore transGH (orbit_refl _ G _)) astab1Rs.
Qed.

Lemma orbitJs : forall G A, orbit 'Js G A = A :^: G. Proof. by []. Qed.

Lemma astab1Js : forall A, 'C[A | 'Js] = 'N(A).
Proof. by move=> A; apply/setP=> x; apply/astab1P/normP. Qed.

Lemma card_conjugates : forall A G, #|A :^: G| = #|G : 'N_G(A)|.
Proof. by move=> A G; rewrite card_orbit astab1Js. Qed.

Lemma afixJG : forall G A, (G \in 'Fix_'JG(A)) = (A \subset 'N(G)).
Proof.
by move=> G A; apply/afixP/normsP=> nG x Ax; apply/eqP; move/eqP: (nG x Ax).
Qed.

Lemma astab1JG : forall G, 'C[G | 'JG] = 'N(G).
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/normP; [move/(congr1 val) | move/group_inj].
Qed.

Lemma dom_qactJ : forall H, qact_dom 'J H = 'N(H).
Proof. by move=> H; rewrite qact_domE ?subsetT ?astabsJ. Qed.

Lemma qactJ : forall H (Hy : coset_of H) x,
  'Q%act Hy x = if x \in 'N(H) then Hy ^ coset H x else Hy.
Proof.
move=> H Hy; case: (cosetP Hy) => y Ny ->{Hy} x.
by rewrite qactEcond // dom_qactJ; case Nx: (x \in 'N(H)); rewrite ?morphJ.
Qed.

Lemma actsQ : forall A B H,
  A \subset 'N(H) -> A \subset 'N(B) -> [acts A, on B / H | 'Q].
Proof.
by move=> A B H nHA nBA; rewrite acts_quotient // subsetI dom_qactJ nHA astabsJ.
Qed. 

Lemma astabsQ : forall G H, H <| G -> 'N(G / H | 'Q) = 'N(H) :&: 'N(G).
Proof. by move=> G H nsHG; rewrite astabs_quotient // dom_qactJ astabsJ. Qed. 

Lemma astabQ : forall H Abar, 'C(Abar |'Q) = coset H @*^-1 'C(Abar).
Proof.
move=> H Abar; apply/setP=> x; rewrite inE /= dom_qactJ morphpreE in_setI /=.
case Nx: (x \in 'N(H)) => //=; rewrite !inE -sub1set centsC cent_set1.
congr (Abar \subset (_ : {set _})) => {Abar}.
apply/setP=> Hy; rewrite inE qactJ Nx (sameP eqP conjg_fixP).
by rewrite (sameP cent1P eqP) (sameP commgP eqP).
Qed.

Lemma sub_astabQ : forall A H Bbar,
  (A \subset 'C(Bbar | 'Q)) = (A \subset 'N(H)) && (A / H \subset 'C(Bbar)).
Proof.
move=> A H Bbar; rewrite astabQ -morphpreIdom subsetI.
by case nHA: (A \subset 'N(H)) => //=; rewrite -sub_quotient_pre.
Qed.

Lemma sub_astabQR : forall A B H,
     A \subset 'N(H) -> B \subset 'N(H) ->
  (A \subset 'C(B / H | 'Q)) = ([~: A, B] \subset H).
Proof.
move=> A B H nHA nHB; rewrite sub_astabQ nHA /= (sameP commG1P eqP).
by rewrite eqEsubset sub1G andbT -quotientR // quotient_sub1 // comm_subG.
Qed.

Lemma astabQR : forall A H, A \subset 'N(H) ->
  'C(A / H | 'Q) = [set x \in 'N(H) | [~: [set x], A] \subset H].
Proof.
move=> A H nHA; apply/setP=> x; rewrite astabQ -morphpreIdom 2!inE -astabQ.
by case nHx: (x \in _); rewrite //= -sub1set sub_astabQR ?sub1set.
Qed.

Lemma quotient_astabQ : forall H Abar, 'C(Abar | 'Q) / H = 'C(Abar).
Proof. by move=> H Abar; rewrite astabQ cosetpreK. Qed.

Section CardClass.

Variable G : {group gT}.

Lemma index_cent1 : forall x, #|G : 'C_G[x]| = #|x ^: G|.
Proof. by move=> x; rewrite -astab1J -card_orbit. Qed.

Lemma sum_card_class : \sum_(C \in classes G) #|C| = #|G|.
Proof. apply: acts_sum_card_orbit; apply/actsP=> x Gx y; exact: groupJr. Qed.

Lemma class_formula : \sum_(C \in classes G) #|G : 'C_G[repr C]| = #|G|.
Proof.
rewrite -sum_card_class; apply: eq_bigr => C; case/imsetP=> x Gx ->.
have: x \in x ^: G by rewrite -{1}(conjg1 x) mem_imset.
by move/mem_repr; case/imsetP=> y Gy ->; rewrite index_cent1 classGidl.
Qed.

Lemma card_classes_abelian : abelian G -> #|classes G| = #|G|.
Proof.
move=> cGG; rewrite -sum_card_class -sum1_card; apply: eq_bigr => xG.
case/imsetP=> x Gx ->; rewrite (@eq_card1 _ x) // => y.
apply/idP/eqP=> [| ->]; last by rewrite class_refl.
by case/imsetP=> z Gz ->; rewrite conjgE (centsP cGG x) ?mulKg.
Qed.

End CardClass.

(* This is proved by more elementary means in groups.v
Lemma index2_normal : forall G H, H \subset G -> #|G : H| = 2 -> H <| G.
Proof.
move=> G H sHG indexHG; rewrite /normal sHG; apply/subsetP=> x Gx.
case Hx: (x \in H); first by rewrite inE conjGid.
have defHx: [set H :* x] = rcosets H G :\ gval H.
  apply/eqP; rewrite eqEcard sub1set !inE cards1 -rcosetE mem_orbit //=.
  rewrite (sameP eqP afix1P) -sub_astab1 astab1Rs sub1set Hx /=.
  by rewrite -ltnS -indexHG [#|G : H|](cardsD1 (gval H)) orbit_refl.
rewrite -sub_afixRs_norm -sub_astab1 -astabs_set1 defHx.
by rewrite actsD ?astabs_set1 ?astab1Rs // (subset_trans sHG) ?actsRs_rcosets.
Qed.
*)

End InternalGroupAction.

Lemma gacentQ : forall (gT : finGroupType) (H : {group gT}) (A : {set gT}),
  'C_(|'Q)(A) = 'C(A / H).
Proof.
move=> gT H A; apply/setP=> Hx; case: (cosetP Hx) => x Nx ->{Hx}.
rewrite -sub_cent1 -astab1J astabC sub1set -(quotientInorm H A).
have defD: qact_dom 'J H = 'N(H) by rewrite qact_domE ?subsetT ?astabsJ.
rewrite !(inE, mem_quotient) //= defD setIC.
apply/subsetP/subsetP=> [cAx Ha | cAx a Aa].
  case/morphimP=> a Na Aa ->{Ha}.
  by move/cAx: Aa; rewrite !inE qactE ?defD ?morphJ.
have [_ Na] := setIP Aa; move/implyP: (cAx (coset H a)); rewrite mem_morphim //.
by rewrite !inE qactE ?defD ?morphJ.
Qed.

Section AutAct.

Variable (gT : finGroupType) (G : {set gT}).

Definition autact := act ('P \ subsetT (Aut G)).
Canonical Structure aut_action := [action of autact].

Lemma autactK : forall a, actperm aut_action a = a.
Proof. by move=> a; apply/permP=> x; rewrite permE. Qed.

Lemma autact_is_groupAction : is_groupAction G aut_action.
Proof. by move=> a Aa /=; rewrite autactK. Qed.
Canonical Structure aut_groupAction := GroupAction autact_is_groupAction.

End AutAct.

Notation "[ 'Aut' G ]" := (aut_action G) : action_scope.
Notation "[ 'Aut' G ]" := (aut_groupAction G) : groupAction_scope.



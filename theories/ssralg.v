(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

(******************************************************************************)
(*   The algebraic part of the Algebraic Hierarchy, as described in           *)
(*          ``Packaging mathematical structures'', TPHOLs09, by               *)
(*   Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence Rideau     *)
(*                                                                            *)
(* This file defines for each Structure (Zmodule, Ring, etc ...) its type,    *)
(* its packers and its canonical properties :                                 *)
(*                                                                            *)
(*  * Zmodule (additive abelian groups):                                      *)
(*              zmodType == interface type for Zmodule structure.             *)
(* ZmodMixin addA addC add0x addNx == builds the mixin for a Zmodule from the *)
(*                          algebraic properties of its operations.           *)
(*          ZmodType V m == packs the mixin m to build a Zmodule of type      *)
(*                          zmodType. The carrier type V must have a          *)
(*                          choiceType canonical structure.                   *)
(* [zmodType of V for S] == V-clone of the zmodType structure S: a copy of S  *)
(*                          where the sort carrier has been replaced by V,    *)
(*                          and which is therefore a zmodType structure on V. *)
(*                          The sort carrier for S must be convertible to V.  *)
(*       [zmodType of V] == clone of a canonical zmodType structure on V.     *)
(*                          Similar to the above, except S is inferred, but   *)
(*                          possibly with a syntactically different carrier.  *)
(*                     0 == the zero (additive identity) of a Zmodule.        *)
(*                 x + y == the sum of x and y (in a Zmodule).                *)
(*                   - x == the opposite (additive inverse) of x.             *)
(*                 x - y == the difference of x and y; this is only notation  *)
(*                          for x + (- y).                                    *)
(*                x *+ n == n times x, with n in nat (non-negative), i.e.,    *)
(*                          x + (x + .. (x + x)..) (n terms); x *+ 1 is thus  *)
(*                          convertible to x, and x *+ 2 to x + x.            *)
(*                x *- n == notation for - (x *+ n), the opposite of x *+ n.  *)
(*        \sum_<range> e == iterated sum for a Zmodule (cf bigop.v).          *)
(*                  e`_i == nth 0 e i, when e : seq M and M has a zmodType    *)
(*                          structure.                                        *)
(*             support f == 0.-support f, i.e., [pred x | f x != 0],          *)
(*                                                                            *)
(*  * Ring (non-commutative rings):                                           *)
(*              ringType == interface type for a Ring structure.              *)
(* RingMixin mulA mul1x mulx1 mulDx mulxD == builds the mixin for a Ring from *)
(*                           the algebraic properties of its multiplicative   *)
(*                           operators; the carrier type must have a zmodType *)
(*                           structure.                                       *)
(*           RingType R m == packs the ring mixin m into a ringType.          *)
(*                    R^c == the converse Ring for R: R^c is convertible to R *)
(*                           but when R has a canonical ringType structure    *)
(*                           R^c has the converse one: if x y : R^c, then     *)
(*                           x * y = (y : R) * (x : R).                       *)
(*  [ringType of R for S] == R-clone of the ringType structure S.             *)
(*        [ringType of R] == clone of a canonical ringType structure on R.    *)
(*                      1 == the multiplicative identity element of a Ring.   *)
(*                   n%:R == the ring image of an n in nat; this is just      *)
(*                           notation for 1 *+ n, so 1%:R is convertible to 1 *)
(*                           and 2%:R to 1 + 1.                               *)
(*                  x * y == the ring product of x and y.                     *)
(*        \prod_<range> e == iterated product for a ring (cf bigop.v).        *)
(*                 x ^+ n == x to the nth power with n in nat (non-negative), *)
(*                           i.e., x * (x * .. (x * x)..) (n factors); x ^+ 1 *)
(*                           is thus convertible to x, and x ^+ 2 to x * x.   *)
(*         GRing.comm x y <-> x and y commute, i.e., x * y = y * x.           *)
(*           GRing.lreg x <-> x if left-regular, i.e., *%R x is injective.    *)
(*           GRing.rreg x <-> x if right-regular, i.e., *%R x is injective.   *)
(*               [char R] == the characteristic of R, defined as the set of   *)
(*                           prime numbers p such that p%:R = 0 in R. The set *)
(*                           [char p] has a most one element, and is          *)
(*                           implemented as a pred_nat collective predicate   *)
(*                           (see prime.v); thus the statement p \in [char R] *)
(*                           can be read as `R has characteristic p', while   *)
(*                           [char R] =i pred0 means `R has characteristic 0' *)
(*                           when R is a field.                               *)
(*     Frobenius_aut chRp == the Frobenius automorphism mapping x in R to     *)
(*                           x ^+ p, where chRp : p \in [char R] is a proof   *)
(*                           that R has (non-zero) characteristic p.          *)
(*                                                                            *)
(*  * ComRing (commutative Rings):                                            *)
(*            comRingType == interface type for commutative ring structure.   *)
(*     ComRingType R mulC == packs mulC into a comRingType; the carrier type  *)
(*                           R must have a ringType canonical structure.      *)
(* ComRingMixin mulA mulC mul1x mulDx == builds the mixin for a Ring (i.e., a *)
(*                           *non commutative* ring), using the commutativity *)
(*                           to reduce the number of proof obligagtions.      *)
(* [comRingType of R for S] == R-clone of the comRingType structure S.        *)
(*     [comRingType of R] == clone of a canonical comRingType structure on R. *)
(*                                                                            *)
(*  * UnitRing (Rings whose units have computable inverses):                  *)
(*           unitRingType == interface type for the UnitRing structure.       *)
(* UnitRingMixin mulVr mulrV unitP inv0id == builds the mixin for a UnitRing  *)
(*                           from the properties of the inverse operation and *)
(*                           the boolean test for being a unit (invertible).  *)
(*                           The inverse of a non-unit x is constrained to be *)
(*                           x itself (property inv0id). The carrier type     *)
(*                           must have a ringType canonical structure.        *)
(*       UnitRingType R m == packs the unit ring mixin m into a unitRingType. *)
(*                  WARNING: while it is possible to omit R for most of the   *)
(*                           XxxType functions, R MUST be explicitly given    *)
(*                           when UnitRingType is used with a mixin produced  *)
(*                           by ComUnitRingMixin, otherwise the resulting     *)
(*                           structure will have the WRONG sort key and will  *)
(*                           NOT BE USED during type inference.               *)
(* [unitRingType of R for S] == R-clone of the unitRingType structure S.      *)
(*    [unitRingType of R] == clones a canonical unitRingType structure on R.  *)
(*           GRing.unit x <=> x is a unit (i.e., has an inverse).             *)
(*                   x^-1 == the ring inverse of x, if x is a unit, else x.   *)
(*                  x / y == x divided by y (notation for x * y^-1).          *)
(*                 x ^- n := notation for (x ^+ n)^-1, the inverse of x ^+ n. *)
(*                                                                            *)
(*  * ComUnitRing (commutative rings with computable inverses):               *)
(*        comUnitRingType == interface type for ComUnitRing structure.        *)
(* ComUnitRingMixin mulVr unitP inv0id == builds the mixin for a UnitRing (a  *)
(*                           *non commutative* unit ring, using commutativity *)
(*                           to simplify the proof obligations; the carrier   *)
(*                           type must have a comRingType structure.          *)
(*                           WARNING: ALWAYS give an explicit type argument   *)
(*                           to UnitRingType along with a mixin produced by   *)
(*                           ComUnitRingMixin (see above).                    *)
(* [comUnitRingType of R] == a comUnitRingType structure for R created by     *)
(*                           merging canonical comRingType and unitRingType   *)
(*                           structures on R.                                 *)
(*                                                                            *)
(*  * IntegralDomain (integral, commutative, ring with partial inverses):     *)
(*            idomainType == interface type for the IntegralDomain structure. *)
(* IdomainType R mulf_eq0 == packs the integrality property into an           *)
(*                           idomainType integral domain structure; R must    *)
(*                           have a comUnitRingType canonical structure.      *)
(* [idomainType of R for S] == R-clone of the idomainType structure S.        *)
(*     [idomainType of R] == clone of a canonical idomainType structure on R. *)
(*                                                                            *)
(*  * Field (commutative fields):                                             *)
(*              fieldType == interface type for fields.                       *)
(*  GRing.Field.axiom inv == the field axiom (x != 0 -> inv x * x = 1).       *)
(* FieldUnitMixin mulVx unitP inv0id == builds a *non commutative unit ring*  *)
(*                           mixin, using the field axiom to simplify proof   *)
(*                           obligations. The carrier type must have a        *)
(*                           comRingType canonical structure.                 *)
(*       FieldMixin mulVx == builds the field mixin from the field axiom. The *)
(*                           carrier type must have a comRingType structure.  *)
(*    FieldIdomainMixin m == builds an *idomain* mixin from a field mixin m.  *)
(*          FieldType R m == packs the field mixin M into a fieldType. The    *)
(*                           carrier type R must be an idomainType.           *)
(* [fieldType of F for S] == F-clone of the fieldType structure S.            *)
(*       [fieldType of F] == clone of a canonical fieldType structure on F.   *)
(*                                                                            *)
(*  * DecidableField (fields with a decidable first order theory):            *)
(*           decFieldType == interface type for DecidableField structure.     *)
(*     DecFieldMixin satP == builds the mixin for a DecidableField from the   *)
(*                           correctness of its satisfiability predicate. The *)
(*                           carrier type must have a unitRingType structure. *)
(*       DecFieldType F m == packs the decidable field mixin m into a         *)
(*                           decFieldType; the carrier type F must have a     *)
(*                           fieldType structure.                             *)
(* [decFieldType of F for S] == F-clone of the decFieldType structure S.      *)
(*    [decFieldType of F] == clone of a canonical decFieldType structure on F *)
(*           GRing.term R == the type of formal expressions in a unit ring R  *)
(*                           with formal variables 'X_k, k : nat, and         *)
(*                           manifest constants x%:T, x : R. The notation of  *)
(*                           all the ring operations is redefined for terms,  *)
(*                           in scope %T.                                     *)
(*        GRing.formula R == the type of first order formulas over R; the %T  *)
(*                           scope binds the logical connectives /\, \/, ~,   *)
(*                           ==>, ==, and != to formulae; GRing.True/False    *)
(*                           and GRing.Bool b denote constant formulae, and   *)
(*                           quantifiers are written 'forall/'exists 'X_k, f. *)
(*                             GRing.Unit x tests for ring units              *)
(*                             GRing.If p_f t_f e_f emulates if-then-else     *)
(*                             GRing.Pick p_f t_f e_f emulates fintype.pick   *)
(*                             foldr GRing.Exists/Forall q_f xs can be used   *)
(*                               to write iterated quantifiers.               *)
(*         GRing.eval e t == the value of term t with valuation e : seq R     *)
(*                           (e maps 'X_i to e`_i).                           *)
(*  GRing.same_env e1 e2 <-> environments e1 and e2 are extensionally equal.  *)
(*        GRing.qf_form f == f is quantifier-free.                            *)
(*        GRing.holds e f == the intuitionistic CiC interpretation of the     *)
(*                           formula f holds with valuation e.                *)
(*      GRing.qf_eval e f == the value (in bool) of a quantifier-free f.      *)
(*          GRing.sat e f == valuation e satisfies f (only in a decField).    *)
(*          GRing.sol n f == a sequence e of size n such that e satisfies f,  *)
(*                           if one exists, or [::] if there is no such e.    *)
(* QEdecFieldMixin wfP okP == a decidable field Mixin built from a quantifier *)
(*                           eliminator p and proofs wfP : GRing.wf_QE_proj p *)
(*                           and okP : GRing.valid_QE_proj p that p returns   *)
(*                           well-formed and valid formulae: p i (us, vs)     *)
(*                           should be a quntifier free formula equivalent to *)
(*        'exists 'X_i, u1 == 0 /\ ... /\ u_m == 0 /\ v1 != 0 ... /\ v_n != 0 *)
(*                                                                            *)
(*  * ClosedField (algebraically closed fields):                              *)
(*        closedFieldType == interface type for the ClosedField structure.    *)
(*    ClosedFieldType F m == packs the closed field mixin m into a            *)
(*                           closedFieldType. The carrier F must have a       *)
(*                           decFieldType structure.                          *)
(* [closedFieldType of F on S] == F-clone of a closedFieldType structure S.   *)
(* [closedFieldType of F] == clone of a canonicalclosedFieldType structure    *)
(*                           on F.                                            *)
(*                                                                            *)
(*  * Lmodule (module with left multiplication by external scalars).          *)
(*             lmodType R == interface type for an Lmodule structure with     *)
(*                           scalars of type R; R must have a ringType        *)
(*                           structure.                                       *)
(* LmodMixin scalA scal1v scalxD scalDv == builds an Lmodule mixin from the   *)
(*                           algebraic properties of the scaling operation;   *)
(*                           the module carrier type must have a zmodType     *)
(*                           structure, and the scalar carrier must have a    *)
(*                           ringType structure.                              *)
(*         LmodType R V m == packs the mixin v to build an Lmodule of type    *)
(*                           lmodType R. The carrier type V must have a       *)
(*                           zmodType structure.                              *)
(* [lmodType R of V for S] == V-clone of an lmodType R structure S.           *)
(*      [lmodType R of V] == clone of a canonical lmodType R structure on V.  *)
(*                 a *: v == v scaled by a, when v is in an Lmodule V and a   *)
(*                           is in the scalar Ring of V.                      *)
(*                                                                            *)
(*  * Lalgebra (left algebra, ring with scaling that associates on the left): *)
(*             lalgType R == interface type for Lalgebra structures with      *)
(*                           scalars in R; R must have ringType structure.    *)
(*    LalgType R V scalAl == packs scalAl : k (x y) = (k x) y into an         *)
(*                           Lalgebra of type lalgType R. The carrier type V  *)
(*                           must have both lmodType R and ringType canonical *)
(*                           structures.                                      *)
(*                    R^o == the regular algebra of R: R^o is convertible to  *)
(*                           R, but when R has a ringType structure then R^o  *)
(*                           extends it to an lalgType structure by letting R *)
(*                           act on itself: if x : R and y : R^o then         *)
(*                           x *: y = x * (y : R).                            *)
(*                   k%:A == the image of the scalar k in an L-algebra; this  *)
(*                           is simply notation for a *: 1.                   *)
(* [lalgType R of V for S] == V-clone the lalgType R structure S.             *)
(*      [lalgType R of V] == clone of a canonical lalgType R structure on V.  *)
(*                                                                            *)
(*  * Algebra (ring with scaling that associates both left and right):        *)
(*              algType R == type for Algebra structure with scalars in R.    *)
(*                           R should be a commutative ring.                  *)
(*     AlgType R A scalAr == packs scalAr : k (x y) = x (k y) into an Algebra *)
(*                           Structure of type algType R. The carrier type A  *)
(*                           must have an lalgType R structure.               *)
(*        CommAlgType R A == creates an Algebra structure for an A that has   *)
(*                           both lalgType R and comRingType structures.      *)
(* [algType R of V for S] == V-clone of an algType R structure on S.          *)
(*       [algType R of V] == clone of a canonical algType R structure on V.   *)
(*                                                                            *)
(*  * UnitAlgebra (algebra with computable inverses):                         *)
(*          unitAlgType R == interface type for UnitAlgebra structure with    *)
(*                           scalars in R; R should have a unitRingType       *)
(*                           structure.                                       *)
(*   [unitAlgType R of V] == a unitAlgType R structure for V created by       *)
(*                           merging canonical algType and unitRingType on V. *)
(*                                                                            *)
(*   In addition to this strcture hierarchy, we also develop a separate,      *)
(* parallel hierarchy for morphisms linking these structures:                 *)
(*                                                                            *)
(* * Additive (additive functions):                                           *)
(*             additive f <-> f of type U -> V is additive, i.e., f maps the  *)
(*                           Zmodule structure of U to that of V, 0 to 0,     *)
(*                           - to - and + to + (equivalently, binary - to -). *)
(*                        := {morph f : u v / u + v}.                         *)
(*      {additive U -> V} == the interface type for a Structure (keyed on     *)
(*                           a function f : U -> V) that encapsulates the     *)
(*                           additive property; both U and V must have        *)
(*                           zmodType canonical structures.                   *)
(*         Additive add_f == packs add_f : additive f into an additive        *)
(*                           function structure of type {additive U -> V}.    *)
(*   [additive of f as g] == an f-clone of the additive structure on the      *)
(*                           function g -- f and g must be convertible.       *)
(*        [additive of f] == a clone of an existing additive structure on f.  *)
(*                                                                            *)
(* * RMorphism (ring morphisms):                                              *)
(*       multiplicative f <-> f of type R -> S is multiplicative, i.e., f     *)
(*                           maps 1 and * in R to 1 and * in S, respectively, *)
(*                           R ans S must have canonical ringType structures. *)
(*            rmorphism f <-> f is a ring morphism, i.e., f is both additive  *)
(*                           and multiplicative.                              *)
(*     {rmorphism R -> S} == the interface type for ring morphisms, i.e.,     *)
(*                           a Structure that encapsulates the rmorphism      *)
(*                           property for functions f : R -> S; both R and S  *)
(*                           must have ringType structures.                   *)
(*      RMorphism morph_f == packs morph_f : rmorphism f into a Ring morphism *)
(*                           structure of type {rmorphism R -> S}.            *)
(*     AddRMorphism mul_f == packs mul_f : multiplicative f into an rmorphism *)
(*                           structure of type {rmorphism R -> S}; f must     *)
(*                           already have an {additive R -> S} structure.     *)
(*  [rmorphism of f as g] == an f-clone of the rmorphism structure of g.      *)
(*       [rmorphism of f] == a clone of an existing additive structure on f.  *)
(*  -> If R and S are UnitRings the f also maps units to units and inverses   *)
(*     of units to inverses; if R is a field then f if a field isomorphism    *)
(*     between R and its image.                                               *)
(*  -> As rmorphism coerces to both additive and multiplicative, all          *)
(*     structures for f can be built from a single proof of rmorphism f.      *)
(*  -> Additive properties (raddf_suffix, see below) are duplicated and       *)
(*     specialised for RMorphism (as rmorph_suffix). This allows more         *)
(*     precise rewriting and cleaner chaining: although raddf lemmas will     *)
(*     recognize RMorphism functions, the converse will not hold (we cannot   *)
(*     add reverse inheritance rules because of incomplete backtracking in    *)
(*     the Canonical Projection unification), so one would have to insert a   *)
(*     /= every time one switched from additive to multiplicative rules.      *)
(*  -> The property duplication also means that it is not strictly necessary  *)
(*     to declare all Additive instances.                                     *)
(*                                                                            *)
(* * Linear (linear functions):                                               *)
(*             scalable f <-> f of type U -> V is scalable, i.e., f maps      *)
(*                           scaling on U to scaling on V, a *: _ to a*: _.   *)
(*                           U and V must both have lmodType R structures,    *)
(*                           for the same ringType R.                         *)
(*               linear f <-> f of type U -> V is linear, i.e., f maps linear *)
(*                           combinations in U to linear combinations in V;   *)
(*                           U and V must both have lmodType R structures,    *)
(*                           for the same ringType R.                         *)
(*                        := forall a, {morph f / u v / a *: u + v}.          *)
(*            lmorphism f <-> f is both additive and scalable. This is in     *)
(*                           fact equivalent to linear f, although somewhat   *)
(*                           less convenient to prove.                        *)
(*        {linear U -> V} == the interface type for linear functions, i.e., a *)
(*                           Structure that encapsulates the linear property  *)
(*                           for functions f : U -> V; both U and V must have *)
(*                           lmodType R structures, for the same R.           *)
(*           Linear lin_f == packs lin_f : lmorphism f into a linear function *)
(*                           structure of type {linear U -> V}. As linear f   *)
(*                           coerces to lmorphism f, Linear can also be used  *)
(*                           with lin_f : linear f (indeed, that is the       *)
(*                           recommended usage).                              *)
(*       AddLinear scal_f == packs scal_f : scalable f into a {linear U -> V} *)
(*                           structure; f must already have an additive       *)
(*                           structure; lin_f : linear f may be used instead  *)
(*                           of scal_f.                                       *)
(*     [linear of f as g] == an f-clone of the linear structure of g.         *)
(*          [linear of f] == a clone of an existing linear structure on f.    *)
(* -> Similarly to Ring morphisms, additive properties are specialized for    *)
(*    linear functions.                                                       *)
(*                                                                            *)
(* * LRMorphism (linear ring morphisms, i.e., algebra morphisms):             *)
(*           lrmorphism f <-> f of type A -> B is a linear Ring (Algebra)     *)
(*                           morphism: f is both additive, multiplicative and *)
(*                           scalable. A and B must both have lalgType R      *)
(*                           canonical structures, for the same ringType R.   *)
(*    {lrmorphism A -> B} == the interface type for linear morphisms, i.e., a *)
(*                           Structure that encapsulates the lrmorphism       *)
(*                           property for functions f : A -> B; both A and B  *)
(*                           must have lalgType R structures, for the same R. *)
(*      LRmorphism scal_f == packs scal_f : scalable f into a linear morphism *)
(*                           structure of type {lrmorphism U -> V}; f must    *)
(*                           already have a Ring morphism structure, and      *)
(*                           lin_f : linear f may be used instead of scal_f.  *)
(*      [lrmorphism of f] == creates an lrmorphism structure from existing    *)
(*                           rmorphism and linear structures on f; this is    *)
(*                           the preferred way of creating lrmorphism         *)
(*                           structures.                                      *)
(*  -> Linear and rmorphism properties do not need to be specialized for      *)
(*     as we supply inheritance join instances in both directions.            *)
(* Finally we supply some helper notation for morphisms:                      *)
(*                    x^f == the image of x under some morphism. This         *)
(*                           notation is only reserved (not defined) here;    *)
(*                           it is bound locally in sections where some       *)
(*                           morphism is used heavily (e.g., the container    *)
(*                           morphism in the parametricity sections of poly   *)
(*                           and matrix, or the Frobenius section here).      *)
(*                     \0 == the constant null function, which has a          *)
(*                           canonical linear structure, and simplifies on    *)
(*                           application (see ssrfun.v).                      *)
(*                 f \+ g == the additive composition of f and g, i.e., the   *)
(*                           function x |-> f x + g x; f \+ g is canonically  *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application (see ssrfun.v).                      *)
(*                 f \- g == the function x |-> f x - g x, canonically        *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application.                                     *)
(*                k \*: f == the function x |-> k *: f x, which is            *)
(*                           canonically linear when f is and simplifies on   *)
(*                           application (this is a shorter alternative to    *)
(*                           *:%R k \o f).                                    *)
(*         GRing.in_alg A == the ring morphism that injects R into A, where A *)
(*                           has an lalgType R structure; GRing.in_alg A k    *)
(*                           simplifies to k%:A.                              *)
(*                a \*o f == the function x |-> a * f x, canonically linear   *)
(*                           linear when f is and its codomain is an algType  *)
(*                           and which simplifies on application.             *)
(*                a \o* f == the function x |-> f x * a, canonically linear   *)
(*                           linear when f is and its codomain is an lalgType *)
(*                           and which simplifies on application.             *)
(* The Lemmas about these structures are contained in both the GRing module   *)
(* and in the submodule GRing.Theory, which can be imported when unqualified  *)
(* access to the theory is needed (GRing.Theory also allows the unqualified   *)
(* use of additive, linear, Linear, etc). The main GRing module should NOT be *)
(* imported.                                                                  *)
(*   Notations are defined in scope ring_scope (delimiter %R), except term    *)
(* and formula notations, which are in term_scope (delimiter %T).             *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   0 -- ring 0, as in addr0 : x + 0 = x.                                    *)
(*   1 -- ring 1, as in mulr1 : x * 1 = x.                                    *)
(*   D -- ring addition, as in linearD : f (u + v) = f u + f v.               *)
(*   M -- ring multiplication, as in invMf : (x * y)^-1 = x^-1 * y^-1,        *)
(*  Mn -- ring by nat multiplication, as in addfMn : f (x *+ n) = f x *+ n.   *)
(*   N -- ring opposite, as in mulNr : (- x) * y = - (x * y).                 *)
(*   V -- ring inverse, as in mulVr : x^-1 * x = 1.                           *)
(*   X -- ring exponentiation, as in rmorphX : f (x ^+ n) = f x ^+ n.         *)
(*   Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "*%R" (at level 0).
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "k %:A" (at level 2, left associativity, format "k %:A").
Reserved Notation "[ 'char' F ]" (at level 0, format "[ 'char'  F ]").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").
(* Patch for recurring Coq parser bug: Coq seg faults when a level 200 *)
(* notation is used as a pattern.                                      *)
Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Reserved Notation "x ^f" (at level 2, left associativity, format "x ^f").

Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "a \*o f" (at level 40).
Reserved Notation "a \o* f" (at level 40).
Reserved Notation "a \*: f" (at level 40).

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

Module Import GRing.

Import Monoid.Theory.

Module Zmodule.

Record mixin_of (V : Type) : Type := Mixin {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Local Notation "x *+ n" := (natmul x n) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i \in A ) F" := (\big[+%R/0]_(i \in A) F).

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma addrA : @associative V +%R. Proof. by case V => T [? []]. Qed.
Lemma addrC : @commutative V V +%R. Proof. by case V => T [? []]. Qed.
Lemma add0r : @left_id V V 0 +%R. Proof. by case V => T [? []]. Qed.
Lemma addNr : @left_inverse V V V 0 -%R +%R. Proof. by case V => T [? []]. Qed.

Lemma addr0 : @right_id V V 0 +%R.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : @right_inverse V V V 0 -%R +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.

Canonical add_monoid := Monoid.Law addrA add0r addr0.
Canonical add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative V V +%R. Proof. exact: mulmCA. Qed.
Lemma addrAC : @right_commutative V V +%R. Proof. exact: mulmAC. Qed.

Lemma addKr : @left_loop V V -%R +%R.
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addNKr : @rev_left_loop V V -%R +%R.
Proof. by move=> x y; rewrite addrA addrN add0r. Qed.
Lemma addrK : @right_loop V V -%R +%R.
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma addrNK : @rev_right_loop V V -%R +%R.
Proof. by move=> x y; rewrite -addrA addNr addr0. Qed.
Definition subrK := addrNK.
Lemma addrI : @right_injective V V V +%R.
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addIr : @left_injective V V V +%R.
Proof. move=> y; exact: can_inj (addrK y). Qed.
Lemma opprK : @involutive V -%R.
Proof. by move=> x; apply: (@addIr (- x)); rewrite addNr addrN. Qed.
Lemma oppr_inj : @injective V V -%R.
Proof. exact: inv_inj opprK. Qed.
Lemma oppr0 : -0 = 0 :> V.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_eq0 x : (- x == 0) = (x == 0).
Proof. by rewrite (inv_eq opprK) oppr0. Qed.

Lemma subr0 x : x - 0 = x. Proof. by rewrite oppr0 addr0. Qed.
Lemma sub0r x : 0 - x = - x. Proof. by rewrite add0r. Qed.

Lemma oppr_add : {morph -%R: x y / x + y : V}.
Proof.
by move=> x y; apply: (@addrI (x + y)); rewrite addrA subrr addrAC addrK subrr.
Qed.

Lemma oppr_sub x y : - (x - y) = y - x.
Proof. by rewrite oppr_add addrC opprK. Qed.

Lemma subr_eq x y z : (x - z == y) = (x == y + z).
Proof. exact: can2_eq (subrK z) (addrK z) x y. Qed.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Proof. by rewrite subr_eq add0r. Qed.

Lemma addr_eq0 x y : (x + y == 0) = (x == - y).
Proof. by rewrite -[x == _]subr_eq0 opprK. Qed.

Lemma eqr_opp x y : (- x == - y) = (x == y).
Proof. exact: can_eq opprK x y. Qed.

Lemma eqr_oppC x y : (- x == y) = (x == - y).
Proof. exact: inv_eq opprK x y. Qed. 

Lemma mulr0n x : x *+ 0 = 0. Proof. by []. Qed.
Lemma mulr1n x : x *+ 1 = x. Proof. by []. Qed.
Lemma mulr2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma mulrS x n : x *+ n.+1 = x + x *+ n.
Proof. by case: n => //=; rewrite addr0. Qed.

Lemma mulrSr x n : x *+ n.+1 = x *+ n + x.
Proof. by rewrite addrC mulrS. Qed.

Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Proof. by case: b. Qed.

Lemma mul0rn n : 0 *+ n = 0 :> V.
Proof. by elim: n => // n IHn; rewrite mulrS add0r. Qed.

Lemma mulNrn x n : (- x) *+ n = x *- n.
Proof. by elim: n => [|n IHn]; rewrite ?oppr0 // !mulrS oppr_add IHn. Qed.

Lemma mulrn_addl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?addr0 // !mulrS.
by rewrite addrCA -!addrA -IHn -addrCA.
Qed.

Lemma mulrn_addr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof.
elim: m => [|m IHm]; first by rewrite add0r.
by rewrite !mulrS IHm addrA.
Qed.

Lemma mulrn_subl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?subr0 // !mulrS -!addrA; congr(_ + _).
by rewrite addrC IHn -!addrA oppr_add [_ - y]addrC.
Qed.

Lemma mulrn_subr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof.
elim: m n => [|m IHm] [|n le_n_m]; rewrite ?subr0 // {}IHm //.
by rewrite mulrSr mulrS oppr_add addrA addrK.
Qed.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof.
by rewrite mulnC; elim: n => //= n IHn; rewrite mulrS mulrn_addr IHn.
Qed.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof. by rewrite -!mulrnA mulnC. Qed.

Lemma sumr_opp I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof. by rewrite (big_morph _ oppr_add oppr0). Qed.

Lemma sumr_sub I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by rewrite -sumr_opp -big_split /=. Qed.

Lemma sumr_muln I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof. by rewrite (big_morph _ (mulrn_addl n) (mul0rn _)). Qed.

Lemma sumr_muln_r x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (mulrn_addr x) (erefl _)). Qed.

Lemma sumr_const (I : finType) (A : pred I) (x : V) :
  \sum_(i \in A) x = x *+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

End ZmoduleTheory.

Implicit Arguments addrI [V x1 x2].
Implicit Arguments addIr [V x1 x2].
Implicit Arguments oppr_inj [[V] x1 x2].

Module Ring.

Record mixin_of (R : zmodType) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Definition EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 :=
  let _ := @Mixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 in
  @Mixin (Zmodule.Pack (Zmodule.class R) R) _ _
     mulA mul1x mulx1 mul_addl mul_addr nz1.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base R)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.

Definition one (R : ringType) : R := Ring.one (Ring.class R).
Definition mul (R : ringType) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Definition comm R x y := @mul R x y = mul y x.
Definition lreg R x := injective (@mul R x).
Definition rreg R x := injective ((@mul R)^~ x).

Local Notation "1" := (one _) : ring_scope.
Local Notation "- 1" := (- (1)) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _).
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Local Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Local Notation "\prod_ ( i | P ) F" := (\big[*%R/1]_(i | P) F).
Local Notation "\prod_ ( i \in A ) F" := (\big[*%R/1]_(i \in A) F).

(* The ``field'' characteristic; the definition, and many of the theorems,   *)
(* has to apply to rings as well; indeed, we need the Frobenius automorphism *)
(* results for a non commutative ring in the proof of Gorenstein 2.6.3.      *)
Definition char (R : Ring.type) of phant R : nat_pred :=
  [pred p | prime p && (p%:R == 0 :> R)].

Local Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.

(* Converse ring tag. *)
Definition converse R : Type := R.
Local Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R. Proof. by case R => T [? []]. Qed.
Lemma mul1r : @left_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr1 : @right_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr_addl : @left_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma mulr_addr : @right_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma nonzero1r : 1 != 0 :> R. Proof. by case R => T [? []]. Qed.
Lemma oner_eq0 : (1 == 0 :> R) = false. Proof. exact: negbTE nonzero1r. Qed.

Lemma mul0r : @left_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (1 * x)); rewrite -mulr_addl !add0r mul1r.
Qed.
Lemma mulr0 : @right_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (x * 1)); rewrite -mulr_addr !add0r mulr1.
Qed.
Lemma mulrN x y : x * (- y) = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulr_addr !subrr mulr0. Qed.
Lemma mulNr x y : (- x) * y = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulr_addl !subrr mul0r. Qed.
Lemma mulrNN x y : (- x) * (- y) = x * y.
Proof. by rewrite mulrN mulNr opprK. Qed.
Lemma mulN1r x : -1 * x = - x.
Proof. by rewrite mulNr mul1r. Qed.
Lemma mulrN1 x : x * -1 = - x.
Proof. by rewrite mulrN mulr1. Qed.

Canonical mul_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical muloid := Monoid.MulLaw mul0r mulr0.
Canonical addoid := Monoid.AddLaw mulr_addl mulr_addr.

Lemma mulr_suml I r P (F : I -> R) x :
  \sum_(i <- r | P i) F i * x = (\sum_(i <- r | P i) F i) * x.
Proof. by rewrite big_distrl. Qed.

Lemma mulr_sumr I r P (F : I -> R) x :
  \sum_(i <- r | P i) x * F i = x * (\sum_(i <- r | P i) F i).
Proof. by rewrite big_distrr. Qed.

Lemma mulr_subl x y z : (y - z) * x = y * x - z * x.
Proof. by rewrite mulr_addl mulNr. Qed.

Lemma mulr_subr x y z : x * (y - z) = x * y - x * z.
Proof. by rewrite mulr_addr mulrN. Qed.

Lemma mulrnAl x y n : (x *+ n) * y = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mul0r // !mulrS mulr_addl IHn. Qed.

Lemma mulrnAr x y n : x * (y *+ n) = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mulr0 // !mulrS mulr_addr IHn. Qed.

Lemma mulr_natl x n : n%:R * x = x *+ n.
Proof. by rewrite mulrnAl mul1r. Qed.

Lemma mulr_natr x n : x * n%:R = x *+ n.
Proof. by rewrite mulrnAr mulr1. Qed.

Lemma natr_add m n : (m + n)%:R = m%:R + n%:R :> R.
Proof. exact: mulrn_addr. Qed.

Lemma natr_sub m n : n <= m -> (m - n)%:R = m%:R - n%:R :> R.
Proof. exact: mulrn_subr. Qed.

Definition natr_sum := big_morph (natmul 1) natr_add (mulr0n 1).

Lemma natr_mul m n : (m * n)%:R = m%:R * n%:R :> R.
Proof. by rewrite mulrnA -mulr_natr. Qed.

Lemma expr0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expr1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expr2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma exprS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulr1. Qed.

Lemma exp1rn n : 1 ^+ n = 1 :> R.
Proof. by elim: n => // n IHn; rewrite exprS mul1r. Qed.

Lemma exprn_addr x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof. by elim: m => [|m IHm]; rewrite ?mul1r // !exprS -mulrA -IHm. Qed.

Lemma exprSr x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 exprn_addr expr1. Qed.

Lemma commr_sym x y : comm x y -> comm y x. Proof. by []. Qed.
Lemma commr_refl x : comm x x. Proof. by []. Qed.

Lemma commr0 x : comm x 0.
Proof. by rewrite /comm mulr0 mul0r. Qed.

Lemma commr1 x : comm x 1.
Proof. by rewrite /comm mulr1 mul1r. Qed.

Lemma commr_opp x y : comm x y -> comm x (- y).
Proof. by move=> com_xy; rewrite /comm mulrN com_xy mulNr. Qed.

Lemma commrN1 x : comm x (-1).
Proof. apply: commr_opp; exact: commr1. Qed.

Lemma commr_add x y z : comm x y -> comm x z -> comm x (y + z).
Proof. by rewrite /comm mulr_addl mulr_addr => -> ->. Qed.

Lemma commr_muln x y n : comm x y -> comm x (y *+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr0 // mulrS commr_add.
Qed.

Lemma commr_mul x y z : comm x y -> comm x z -> comm x (y * z).
Proof. by move=> com_xy; rewrite /comm mulrA com_xy -!mulrA => ->. Qed.

Lemma commr_nat x n : comm x n%:R.
Proof. by apply: commr_muln; exact: commr1. Qed.

Lemma commr_exp x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr1 // exprS commr_mul.
Qed.

Lemma commr_exp_mull x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulr1.
by rewrite !exprS IHn !mulrA; congr (_ * _); rewrite -!mulrA -commr_exp.
Qed.

Lemma commr_sign x n : comm x ((-1) ^+ n).
Proof. exact: (commr_exp n (commrN1 x)). Qed.

Lemma exprn_mulnl x m n : (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Proof.
elim: n => [|n IHn]; first by rewrite mulr1n.
rewrite exprS IHn -mulr_natr -mulrA -commr_nat mulr_natr -mulrnA -expnSr.
by rewrite -mulr_natr mulrA -exprS mulr_natr.
Qed.

Lemma exprn_mulr x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite exp1rn.
by rewrite mulSn exprn_addr IHm exprS commr_exp_mull //; exact: commr_exp.
Qed.

Lemma exprnC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof. by rewrite -!exprn_mulr mulnC. Qed.

Lemma exprn_mod n x i : x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Proof.
move=> xn1; rewrite {2}(divn_eq i n) exprn_addr mulnC exprn_mulr xn1.
by rewrite exp1rn mul1r.
Qed.

Lemma exprn_dvd n x i : x ^+ n = 1 -> n %| i -> x ^+ i = 1.
Proof.
by move=> xn1 dvd_n_i; rewrite -(exprn_mod i xn1) (eqnP dvd_n_i).
Qed.

Lemma natr_exp n k : (n ^ k)%:R = n%:R ^+ k :> R.
Proof. by rewrite exprn_mulnl exp1rn. Qed.

Lemma signr_odd n : (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim: n => //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite !mulN1r ?opprK.
Qed.

Lemma signr_eq0 n : ((-1) ^+ n == 0 :> R) = false.
Proof. by rewrite -signr_odd; case: odd; rewrite ?oppr_eq0 oner_eq0. Qed.

Lemma mulr_sign (b : bool) x : (-1) ^+ b * x = (if b then - x else x).
Proof. by case: b; rewrite ?mulNr mul1r. Qed.

Lemma signr_addb b1 b2 : (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof. by rewrite mulr_sign; case: b1 b2 => [] []; rewrite ?opprK. Qed.

Lemma exprN x n : (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof. by rewrite -mulN1r commr_exp_mull // /comm mulN1r mulrN mulr1. Qed.

Lemma sqrrN x : (- x) ^+ 2 = x ^+ 2.
Proof. exact: mulrNN. Qed.

Lemma mulrI_eq0 x y : lreg x -> (x * y == 0) = (y == 0).
Proof. by move=> reg_x; rewrite -{1}(mulr0 x) (inj_eq reg_x). Qed.

Lemma lreg_neq0 x : lreg x -> x != 0.
Proof. by move=> reg_x; rewrite -[x]mulr1 mulrI_eq0 ?oner_eq0. Qed.

Lemma mulrI0_lreg x : (forall y, x * y = 0 -> y = 0) -> lreg x.
Proof.
move=> reg_x y z eq_xy_xz; apply/eqP; rewrite -subr_eq0 [y - z]reg_x //.
by rewrite mulr_subr eq_xy_xz subrr.
Qed.

Lemma lregN x : lreg x -> lreg (- x).
Proof. by move=> reg_x y z; rewrite !mulNr => /oppr_inj/reg_x. Qed.

Lemma lreg1 : lreg (1 : R).
Proof. by move=> x y; rewrite !mul1r. Qed.

Lemma lregM x y : lreg x -> lreg y -> lreg (x * y).
Proof. by move=> reg_x reg_y z t; rewrite -!mulrA => /reg_x/reg_y. Qed.

Lemma lregX x n : lreg x -> lreg (x ^+ n).
Proof.
by move=> reg_x; elim: n => [|n]; [exact: lreg1 | rewrite exprS; exact: lregM].
Qed.

Lemma prodr_const (I : finType) (A : pred I) (x : R) :
  \prod_(i \in A) x = x ^+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

Lemma prodr_exp_r x I r P (F : I -> nat) :
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (exprn_addr _) (erefl _)). Qed.

Lemma prodr_opp (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i \in A) - F i = (- 1) ^+ #|A| * \prod_(i \in A) F i.
Proof.
rewrite -sum1_card /= -!(big_filter _ A) !unlock.
elim: {A}(filter _ _) => /= [|i r ->]; first by rewrite mul1r.
by rewrite mulrA -mulN1r (commr_exp _ (commrN1 _)) exprSr !mulrA.
Qed.

Lemma exprn_addl_comm x y n (cxy : comm x y) :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
elim: n => [|n IHn]; rewrite big_ord_recl mulr1 ?big_ord0 ?addr0 //=.
rewrite exprS {}IHn /= mulr_addl !big_distrr /= big_ord_recl mulr1 subn0.
rewrite !big_ord_recr /= !binn !subnn !mul1r !subn0 bin0 !exprS -addrA.
congr (_ + _); rewrite addrA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -leq_subS ?(valP i) //.
by rewrite  subSS (commr_exp _ (commr_sym cxy)) -mulrA -exprS -mulrn_addr.
Qed.

Lemma exprn_subl_comm x y n (cxy : comm x y) :
  (x - y) ^+ n =
    \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
rewrite exprn_addl_comm; last exact: commr_opp.
by apply: eq_bigr => i _; congr (_ *+ _); rewrite -commr_sign -mulrA -exprN.
Qed.

Lemma subr_expn_comm x y n (cxy : comm x y) :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof.
case: n => [|n]; first by rewrite big_ord0 mulr0 subrr.
rewrite mulr_subl !big_distrr big_ord_recl big_ord_recr /= subnn mulr1 mul1r.
rewrite subn0 -!exprS oppr_add -!addrA; congr (_ + _); rewrite addrA -sumr_sub.
rewrite big1 ?add0r // => i _; rewrite !mulrA -exprS -leq_subS ?(valP i) //.
by rewrite subSS (commr_exp _ (commr_sym cxy)) -mulrA -exprS subrr.
Qed.

Lemma exprn_add1 x n : (x + 1) ^+ n = \sum_(i < n.+1) x ^+ i *+ 'C(n, i).
Proof.
rewrite addrC (exprn_addl_comm n (commr_sym (commr1 x))).
by apply: eq_bigr => i _; rewrite exp1rn mul1r.
Qed.

Lemma subr_expn_1 x n : x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Proof.
rewrite -!(oppr_sub 1) mulNr -{1}(exp1rn n).
rewrite (subr_expn_comm _ (commr_sym (commr1 x))); congr (- (_ * _)).
by apply: eq_bigr => i _; rewrite exp1rn mul1r.
Qed.

Lemma sqrr_add1 x : (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Proof.
rewrite exprn_add1 !big_ord_recr big_ord0 /= add0r.
by rewrite addrC addrA addrAC.
Qed.

Lemma sqrr_sub1 x : (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.
Proof. by rewrite -sqrrN oppr_sub addrC sqrr_add1 sqrrN mulNrn. Qed.

Lemma subr_sqr_1 x : x ^+ 2 - 1 = (x - 1) * (x + 1).
Proof. by rewrite subr_expn_1 !big_ord_recr big_ord0 /= addrAC add0r. Qed.

Definition Frobenius_aut p of p \in [char R] := fun x => x ^+ p.

Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Lemma charf0 : p%:R = 0 :> R. Proof. by apply/eqP; case/andP: charFp. Qed.
Lemma charf_prime : prime p. Proof. by case/andP: charFp. Qed.
Hint Resolve charf_prime.

Lemma dvdn_charf n : (p %| n)%N = (n%:R == 0 :> R).
Proof.
apply/idP/eqP=> [/dvdnP[n' ->]|n0]; first by rewrite natr_mul charf0 mulr0.
apply/idPn; rewrite -prime_coprime // => /eqnP pn1.
have [a _ /dvdnP[b]] := bezoutl n (prime_gt0 charf_prime).
move/(congr1 (fun m => m%:R : R))/eqP.
by rewrite natr_add !natr_mul charf0 n0 !mulr0 pn1 addr0 oner_eq0.
Qed.

Lemma charf_eq : [char R] =i (p : nat_pred).
Proof.
move=> q; apply/andP/eqP=> [[q_pr q0] | ->]; last by rewrite charf0.
by apply/eqP; rewrite eq_sym -dvdn_prime2 // dvdn_charf.
Qed.

Lemma bin_lt_charf_0 k : 0 < k < p -> 'C(p, k)%:R = 0 :> R.
Proof. by move=> lt0kp; apply/eqP; rewrite -dvdn_charf prime_dvd_bin. Qed.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE x : x^f = x ^+ p. Proof. by []. Qed.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut_0 : 0^f = 0.
Proof. by rewrite fE -(prednK (prime_gt0 charf_prime)) exprS mul0r. Qed.

Lemma Frobenius_aut_1 : 1^f = 1.
Proof. by rewrite fE exp1rn. Qed.

Lemma Frobenius_aut_add_comm x y (cxy : comm x y) : (x + y)^f = x^f + y^f.
Proof.
have defp := prednK (prime_gt0 charf_prime).
rewrite !fE exprn_addl_comm // big_ord_recr subnn -defp big_ord_recl /= defp.
rewrite subn0 mulr1 mul1r bin0 binn big1 ?addr0 // => i _.
by rewrite -mulr_natl bin_lt_charf_0 ?mul0r //= -{2}defp ltnS (valP i).
Qed.

Lemma Frobenius_aut_muln x n : (x *+ n)^f = x^f *+ n.
Proof.
elim: n => [|n IHn]; first exact: Frobenius_aut_0.
rewrite !mulrS Frobenius_aut_add_comm ?IHn //; exact: commr_muln.
Qed.

Lemma Frobenius_aut_nat n : (n%:R)^f = n%:R.
Proof. by rewrite Frobenius_aut_muln Frobenius_aut_1. Qed.

Lemma Frobenius_aut_mul_comm x y : comm x y -> (x * y)^f = x^f * y^f.
Proof. by exact: commr_exp_mull. Qed.

Lemma Frobenius_aut_exp x n : (x ^+ n)^f = x^f ^+ n.
Proof. by rewrite !fE -!exprn_mulr mulnC. Qed.

Lemma Frobenius_aut_opp x : (- x)^f = - x^f.
Proof.
apply/eqP; rewrite -subr_eq0 opprK addrC.
by rewrite -(Frobenius_aut_add_comm (commr_opp _)) // subrr Frobenius_aut_0.
Qed.

Lemma Frobenius_aut_sub_comm x y : comm x y -> (x - y)^f = x^f - y^f.
Proof.
by move/commr_opp/Frobenius_aut_add_comm->; rewrite Frobenius_aut_opp.
Qed.

End FrobeniusAutomorphism.

Canonical converse_eqType := [eqType of R^c].
Canonical converse_choiceType := [choiceType of R^c].
Canonical converse_zmodType := [zmodType of R^c].

Definition converse_ringMixin :=
  let mul' x y := y * x in
  let mulrA' x y z := esym (mulrA z y x) in
  let mulr_addl' x y z := mulr_addr z x y in
  let mulr_addr' x y z := mulr_addl y z x in
  @Ring.Mixin converse_zmodType
    1 mul' mulrA' mulr1 mul1r mulr_addl' mulr_addr' nonzero1r.
Canonical converse_ringType := RingType R^c converse_ringMixin.

End RingTheory.

Section RightRegular.

Variable R : ringType.
Implicit Types x y : R.
Let Rc := converse_ringType R.

Lemma mulIr_eq0 x y : rreg x -> (y * x == 0) = (y == 0).
Proof. exact: (@mulrI_eq0 Rc). Qed.

Lemma mulIr0_rreg x : (forall y, y * x = 0 -> y = 0) -> rreg x.
Proof. exact: (@mulrI0_lreg Rc). Qed.

Lemma rreg_neq0 x : rreg x -> x != 0.
Proof. exact: (@lreg_neq0 Rc). Qed.

Lemma rregN x : rreg x -> rreg (- x).
Proof. exact: (@lregN Rc). Qed.

Lemma rreg1 : rreg (1 : R).
Proof. exact: (@lreg1 Rc). Qed.

Lemma rregM x y : rreg x -> rreg y -> rreg (x * y).
Proof. by move=> reg_x reg_y; exact: (@lregM Rc). Qed.

Lemma revrX x n : (x : Rc) ^+ n = (x : R) ^+ n.
Proof. by elim: n => // n IHn; rewrite exprS exprSr IHn. Qed.

Lemma rregX x n : rreg x -> rreg (x ^+ n).
Proof. by move/(@lregX Rc x n); rewrite revrX. Qed.

End RightRegular.

Module Lmodule.

Structure mixin_of (R : ringType) (V : zmodType) : Type := Mixin {
  scale : R -> V -> V;
  _ : forall a b v, scale a (scale b v) = scale (a * b) v;
  _ : left_id 1 scale;
  _ : right_distributive scale +%R;
  _ : forall v, {morph scale^~ v: a b / a + b}
}.

Section ClassDef.

Variable R : ringType.

Structure class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base V)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
Notation "[ 'lmodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lmodType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'lmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lmodType'  R 'of'  T ]") : form_scope.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Definition scale (R : ringType) (V : lmodType R) :=
  Lmodule.scale (Lmodule.class V).

Local Notation "*:%R" := (@scale _ _).
Local Notation "a *: v" := (scale a v) : ring_scope.

Section LmoduleTheory.

Variables (R : ringType) (V : lmodType R).
Implicit Types (a b c : R) (u v : V).

Local Notation "*:%R" := (@scale R V).

Lemma scalerA a b v : a *: (b *: v) = a * b *: v.
Proof. by case: V v => ? [] ? []. Qed.

Lemma scale1r : @left_id R V 1 *:%R.
Proof. by case: V => ? [] ? []. Qed.

Lemma scaler_addr a : {morph *:%R a : u v / u + v}.
Proof. by case: V a => ? [] ? []. Qed.

Lemma scaler_addl v : {morph *:%R^~ v : a b / a + b}.
Proof. by case: V v => ? [] ? []. Qed.

Lemma scale0r v : 0 *: v = 0.
Proof. by apply: (addIr (1 *: v)); rewrite -scaler_addl !add0r. Qed.

Lemma scaler0 a : a *: 0 = 0 :> V.
Proof. by rewrite -{1}(scale0r 0) scalerA mulr0 scale0r. Qed.

Lemma scaleNr a v : - a *: v = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scaler_addl !addNr scale0r. Qed.

Lemma scaleN1r v : (- 1) *: v = - v.
Proof. by rewrite scaleNr scale1r. Qed.

Lemma scalerN a v : a *: (- v) = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scaler_addr !addNr scaler0. Qed.

Lemma scaler_subl a b v : (a - b) *: v = a *: v - b *: v.
Proof. by rewrite scaler_addl scaleNr. Qed.

Lemma scaler_subr a u v : a *: (u - v) = a *: u - a *: v.
Proof. by rewrite scaler_addr scalerN. Qed.

Lemma scaler_nat n v : n%:R *: v = v *+ n.
Proof.
elim: n => /= [|n ]; first by rewrite scale0r.
by rewrite !mulrS scaler_addl ?scale1r => ->.
Qed.

Lemma scaler_sign (b : bool) v: (-1) ^+ b *: v = (if b then - v else v).
Proof. by case: b; rewrite ?scaleNr scale1r. Qed.

Lemma scaler_mulrnl a v n : a *: v *+ n = (a *+ n) *: v.
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scale0r.
by rewrite !mulrSr IHn scaler_addl.
Qed.

Lemma scaler_mulrnr a v n : a *: v *+ n = a *: (v *+ n).
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scaler0.
by rewrite !mulrSr IHn scaler_addr.
Qed.

Lemma scaler_suml v I r (P : pred I) F :
  (\sum_(i <- r | P i) F i) *: v = \sum_(i <- r | P i) F i *: v.
Proof. exact: (big_morph _ (scaler_addl v) (scale0r v)). Qed.

Lemma scaler_sumr a I r (P : pred I) (F : I -> V) :
  a *: (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a *: F i.
Proof. exact: big_endo (scaler_addr a) (scaler0 a) I r P F. Qed.

End LmoduleTheory.

Module Lalgebra.

Definition axiom (R : ringType) (V : lmodType R) (mul : V -> V -> V) :=
  forall a u v, a *: mul u v = mul (a *: u) v.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Ring.class_of T;
  mixin : Lmodule.mixin_of R (Zmodule.Pack base T);
  ext : @axiom R (Lmodule.Pack _ (Lmodule.Class mixin) T) (Ring.mul base)
}.
Definition base2 R m := Lmodule.Class (@mixin R m).
Local Coercion base : class_of >-> Ring.class_of.
Local Coercion base2 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.

Definition pack T b0 mul0 (axT : @axiom R (@Lmodule.Pack R _ T b0 T) mul0) :=
  fun bT b & phant_id (Ring.class bT) (b : Ring.class_of T) =>
  fun mT m & phant_id (@Lmodule.class R phR mT) (@Lmodule.Class R T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (@Class T b m ax) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition lmodType := Lmodule.Pack phR class cT.
Definition lmod_ringType := @Lmodule.Pack R phR ringType class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion base2 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Canonical lmod_ringType.
Notation lalgType R := (type (Phant R)).
Notation LalgType R T a := (@pack _ (Phant R) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'lalgType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lalgType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'lalgType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lalgType'  R 'of'  T ]") : form_scope.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

(* Scalar injection (see the definition of in_alg A below). *)
Local Notation "k %:A" := (k *: 1) : ring_scope.

(* Regular ring algebra tag. *)
Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section LalgebraTheory.

Variables (R : ringType) (A : lalgType R).
Implicit Types x y : A.

Lemma scaler_mull k (x y : A) : k *: (x * y) = k *: x * y.
Proof. by case: A k x y => ? []. Qed.

Canonical regular_eqType := [eqType of R^o].
Canonical regular_choiceType := [choiceType of R^o].
Canonical regular_zmodType := [zmodType of R^o].
Canonical regular_ringType := [ringType of R^o].

Definition regular_lmodMixin :=
  let mkMixin := @Lmodule.Mixin R regular_zmodType (@mul R) in
  mkMixin (@mulrA R) (@mul1r R) (@mulr_addr R) (fun v a b => mulr_addl a b v).

Canonical regular_lmodType := LmodType R R^o regular_lmodMixin.
Canonical regular_lalgType := LalgType R R^o (@mulrA regular_ringType).

End LalgebraTheory.

(* Morphism hierarchy. *)

Module Additive.

Section ClassDef.

Variables U V : zmodType.

Definition axiom (f : U -> V) := {morph f : x y / x - y}.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation additive f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Additive fA := (Pack (Phant _) fA).
Notation "{ 'additive' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'additive'  fUV }") : ring_scope.
Notation "[ 'additive' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'additive'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'additive' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'additive'  'of'  f ]") : form_scope.
End Exports.

End Additive.
Include Additive.Exports. (* Allows GRing.additive to resolve conflicts. *)

(* Lifted additive operations. *)
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition null_fun_head (phV : phant V) of U : V := let: Phant := phV in 0.
Definition add_fun_head t (f g : U -> V) x := let: tt := t in f x + g x.
Definition sub_fun_head t (f g : U -> V) x := let: tt := t in f x - g x.
End LiftedZmod.

(* Lifted multiplication. *)
Section LiftedRing.
Variables (R : ringType) (T : Type).
Implicit Type f : T -> R.
Definition mull_fun_head t a f x := let: tt := t in a * f x.
Definition mulr_fun_head t a f x := let: tt := t in f x * a.
End LiftedRing.

(* Lifted linear operations. *)
Section LiftedScale.
Variables (R : ringType) (U : Type) (V : lmodType R) (A : lalgType R).
Definition scale_fun_head t a (f : U -> V) x := let: tt := t in a *: f x.
Definition in_alg_head (phA : phant A) k : A := let: Phant := phA in k%:A.
End LiftedScale.

Notation null_fun V := (null_fun_head (Phant V)) (only parsing).
(* The real in_alg notation is declared after GRing.Theory so that at least *)
(* in Coq 8.2 it gets precendence when GRing.Theory is not imported.        *)
Local Notation in_alg_loc A := (in_alg_head (Phant A)) (only parsing).

Local Notation "\0" := (null_fun _) : ring_scope.
Local Notation "f \+ g" := (add_fun_head tt f g) : ring_scope.
Local Notation "f \- g" := (sub_fun_head tt f g) : ring_scope.
Local Notation "a \*: f" := (scale_fun_head tt a f) : ring_scope.
Local Notation "x \*o f" := (mull_fun_head tt x f) : ring_scope.
Local Notation "x \o* f" := (mulr_fun_head tt x f) : ring_scope.

Section AdditiveTheory.

Section Properties.

Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddf_sub : {morph f : x y / x - y}. Proof. exact: Additive.class. Qed.

Lemma raddf0 : f 0 = 0.
Proof. by rewrite -[0]subr0 raddf_sub subrr. Qed.

Lemma raddfN : {morph f : x / - x}.
Proof. by move=> x /=; rewrite -sub0r raddf_sub raddf0 sub0r. Qed.

Lemma raddfD : {morph f : x y / x + y}.
Proof. by move=> x y; rewrite -[y]opprK raddf_sub -raddfN. Qed.

Lemma raddfMn n : {morph f : x / x *+ n}.
Proof. by elim: n => [|n IHn] x /=; rewrite ?raddf0 // !mulrS raddfD IHn. Qed.

Lemma raddfMNn n : {morph f : x / x *- n}.
Proof. by move=> x /=; rewrite raddfN raddfMn. Qed.

Lemma raddf_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: (big_morph f raddfD raddf0). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite raddf_sub !f'K. Qed.

Lemma bij_additive :
  bijective f -> exists2 f' : {additive V -> U}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (Additive (can2_additive fK f'K)). Qed.

End Properties.

Section AddFun.

Variables (U V W : zmodType) (f g : {additive V -> W}) (h : {additive U -> V}).

Lemma idfun_is_additive : additive (idfun : U -> U).
Proof. by []. Qed.
Canonical idfun_additive := Additive idfun_is_additive.

Lemma comp_is_additive : additive (f \o h).
Proof. by move=> x y /=; rewrite !raddf_sub. Qed.
Canonical comp_additive := Additive comp_is_additive.

Lemma opp_is_additive : additive (-%R : U -> U).
Proof. by move=> x y; rewrite /= oppr_add. Qed.
Canonical opp_additive := Additive opp_is_additive.

Lemma null_fun_is_additive : additive (\0 : U -> V).
Proof. by move=> /=; rewrite subr0. Qed.
Canonical null_fun_additive := Additive null_fun_is_additive.

Lemma add_fun_is_additive : additive (f \+ g).
Proof.
by move=> x y /=; rewrite !raddf_sub addrCA -!addrA addrCA -oppr_add.
Qed.
Canonical add_fun_additive := Additive add_fun_is_additive.

Lemma sub_fun_is_additive : additive (f \- g).
Proof.
by move=> x y /=; rewrite !raddf_sub addrAC -!addrA -!oppr_add addrAC addrA.
Qed.
Canonical sub_fun_additive := Additive sub_fun_is_additive.

End AddFun.

Section MulFun.

Variables (R : ringType) (U : zmodType).
Variables (a : R) (f : {additive U -> R}).

Lemma mull_fun_is_additive : additive (a \*o f).
Proof. by move=> x y /=; rewrite raddf_sub mulr_subr. Qed.
Canonical mull_fun_additive := Additive mull_fun_is_additive.

Lemma mulr_fun_is_additive : additive (a \o* f).
Proof. by move=> x y /=; rewrite raddf_sub mulr_subl. Qed.
Canonical mulr_fun_additive := Additive mulr_fun_is_additive.

End MulFun.

Section ScaleFun.

Variables (R : ringType) (U : zmodType) (V : lmodType R).
Variables (a : R) (f : {additive U -> V}).

Lemma scale_fun_is_additive : additive (a \*: f).
Proof. by move=> u v /=; rewrite raddf_sub scaler_subr. Qed.
Canonical scale_fun_additive := Additive scale_fun_is_additive.

End ScaleFun.

End AdditiveTheory.

Module RMorphism.

Section ClassDef.

Variables R S : ringType.

Definition mixin_of (f : R -> S) :=
  {morph f : x y / x * y}%R * (f 1 = 1) : Prop.

Record class_of f : Prop := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : mixin_of f) :=
  fun (bF : Additive.map phRS) fA & phant_id (Additive.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical additive := Additive.Pack phRS class.

End ClassDef.

Module Exports.
Notation multiplicative f := (mixin_of f).
Notation rmorphism f := (class_of f).
Coercion base : rmorphism >-> Additive.axiom.
Coercion mixin : rmorphism >-> multiplicative.
Coercion apply : map >-> Funclass.
Notation RMorphism fM := (Pack (Phant _) fM).
Notation AddRMorphism fM := (pack fM id).
Notation "{ 'rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'rmorphism'  fRS }") : ring_scope.
Notation "[ 'rmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'rmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'rmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'rmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
End Exports.

End RMorphism.
Include RMorphism.Exports.

Section RmorphismTheory.

Section Properties.

Variables (R S : ringType) (f : {rmorphism R -> S}).

Lemma rmorph0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma rmorphN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma rmorphD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma rmorph_sub : {morph f: x y / x - y}. Proof. exact: raddf_sub. Qed.
Lemma rmorphMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma rmorphMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma rmorph_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.

Lemma rmorphismP : rmorphism f. Proof. exact: RMorphism.class. Qed.
Lemma rmorphismMP : multiplicative f. Proof. exact: rmorphismP. Qed.
Lemma rmorph1 : f 1 = 1. Proof. by case: rmorphismMP. Qed.
Lemma rmorphM : {morph f: x y  / x * y}. Proof. by case: rmorphismMP. Qed.

Lemma rmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof. exact: (big_morph f rmorphM rmorph1). Qed.

Lemma rmorphX n : {morph f: x / x ^+ n}.
Proof. by elim: n => [|n IHn] x; rewrite ?rmorph1 // !exprS rmorphM IHn. Qed.

Lemma rmorph_nat n : f n%:R = n%:R.
Proof. by rewrite rmorphMn rmorph1. Qed.

Lemma rmorph_sign n : f ((- 1) ^+ n) = (- 1) ^+ n.
Proof. by rewrite rmorphX rmorphN rmorph1. Qed.

Lemma rmorph_char p : p \in [char R] -> p \in [char S].
Proof. by rewrite !inE -rmorph_nat => /andP[-> /= /eqP->]; rewrite rmorph0. Qed.

Lemma can2_rmorphism f' : cancel f f' -> cancel f' f -> rmorphism f'.
Proof.
move=> fK f'K; split; first exact: can2_additive fK f'K.
by split=> [x y|]; apply: (canLR fK); rewrite /= (rmorphM, rmorph1) ?f'K.
Qed.

Lemma bij_rmorphism :
  bijective f -> exists2 f' : {rmorphism S -> R}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (RMorphism (can2_rmorphism fK f'K)). Qed.

End Properties.

Section Projections.

Variables (R S T : ringType) (f : {rmorphism S -> T}) (g : {rmorphism R -> S}).

Lemma idfun_is_multiplicative : multiplicative (idfun : R -> R).
Proof. by []. Qed.
Canonical idfun_rmorphism := AddRMorphism idfun_is_multiplicative.

Definition comp_is_multiplicative : multiplicative (f \o g).
Proof. by split=> [x y|] /=; rewrite ?rmorph1 ?rmorphM. Qed.
Canonical comp_rmorphism := AddRMorphism comp_is_multiplicative.

End Projections.

Section InAlgebra.

Variables (R : ringType) (A : lalgType R).

Lemma in_alg_is_rmorphism : rmorphism (in_alg_loc A).
Proof.
split=> [x y|]; first exact: scaler_subl.
by split=> [x y|] /=; rewrite ?scale1r // -scaler_mull mul1r scalerA.
Qed.
Canonical in_alg_additive := Additive in_alg_is_rmorphism.
Canonical in_alg_rmorphism := RMorphism in_alg_is_rmorphism.

End InAlgebra.

End RmorphismTheory.

Module Linear.

Section ClassDef.

Variables (R : ringType) (U V : lmodType R).
Implicit Type phUV : phant (U -> V).

Definition axiom (f : U -> V) := forall a, {morph f : u v / a *: u + v}.

Definition mixin_of (f : U -> V) := forall a, {morph f : v / a *: v}.

Record class_of f : Prop := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Lemma class_of_axiom f : axiom f -> class_of f.
Proof.
move=> fL.
have fA: additive f by move=> x y /=; rewrite -!scaleN1r addrC fL addrC.
split=> // a v /=.
by rewrite -[a *: v]addr0 fL [f 0](raddf0 (Additive fA)) addr0.
Qed.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phUV f fL.

Definition pack (fZ : mixin_of f) :=
  fun (bF : Additive.map phUV) fA & phant_id (Additive.class bF) fA =>
  Pack phUV (Class fA fZ).

Canonical additive := Additive.Pack phUV class.

End ClassDef.

Module Exports.
Notation scalable f := (mixin_of f).
Notation linear f := (axiom f).
Notation lmorphism f := (class_of f).
Coercion class_of_axiom : linear >-> lmorphism.
Coercion base : lmorphism >-> Additive.axiom.
Coercion mixin : lmorphism >-> scalable.
Coercion apply : map >-> Funclass.
Notation Linear fL := (Pack (Phant _) fL).
Notation AddLinear fZ := (pack fZ id).
Notation "{ 'linear' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'linear'  fUV }") : ring_scope.
Notation "[ 'linear' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'linear'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'linear' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'linear'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
End Exports.

End Linear.
Include Linear.Exports.

Section LinearTheory.

Variable R : ringType.

Section Properties.

Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linear0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma linearN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linear_sub : {morph f: x y / x - y}. Proof. exact: raddf_sub. Qed.
Lemma linearMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZ : scalable f. Proof. exact: (Linear.class f). Qed.
Lemma linearP : linear f.
Proof. by move=> a x y /=; rewrite linearD linearZ. Qed.

Lemma can2_linear f' : cancel f f' -> cancel f' f -> linear f'.
Proof. by move=> fK f'K a x y /=; apply: (canLR fK); rewrite linearP !f'K. Qed.

Lemma bij_linear :
  bijective f -> exists2 f' : {linear V -> U}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (Linear (can2_linear fK f'K)). Qed.

End Properties.

Section LinearLmod.

Variables U V W : lmodType R.
Variables (f g : {linear U -> V}) (h : {linear W -> U}).

Lemma idfun_is_scalable : scalable (idfun : U -> U). Proof. by []. Qed.
Canonical idfun_linear := AddLinear idfun_is_scalable.

Lemma comp_is_scalable : scalable (f \o h).
Proof. by move=> a v /=; rewrite !linearZ. Qed.
Canonical comp_linear := AddLinear comp_is_scalable.

Lemma opp_is_scalable : scalable (-%R : U -> U).
Proof. by move=> a v /=; rewrite scalerN. Qed.
Canonical opp_linear := AddLinear opp_is_scalable.

Lemma scale_is_additive a : additive ( *:%R a : V -> V).
Proof. by move=> u v /=; rewrite scaler_addr scalerN. Qed.
Canonical scale_additive a := Additive (scale_is_additive a).

Lemma null_fun_is_scalable : scalable (\0 : U -> U).
Proof. by move=> a v /=; rewrite scaler0. Qed.
Canonical null_fun_linear := AddLinear null_fun_is_scalable.

Lemma add_fun_is_scalable : scalable (f \+ g).
Proof. by move=> a v /=; rewrite raddfD /= !linearZ. Qed.
Canonical add_fun_linear := AddLinear add_fun_is_scalable.

Lemma sub_fun_is_scalable : scalable (f \- g).
Proof. by move=> a v /=; rewrite raddf_sub /= !linearZ. Qed.
Canonical sub_fun_linear := AddLinear sub_fun_is_scalable.

End LinearLmod.

Section LinearLalg.

Variables (A : lalgType R) (U : lmodType R).

Variables (a : A) (f : {linear U -> A}).

Lemma mulr_fun_is_scalable : scalable (a \o* f).
Proof. by move=> k x /=; rewrite linearZ scaler_mull. Qed.
Canonical mulr_fun_linear := AddLinear mulr_fun_is_scalable.

End LinearLalg.

End LinearTheory.

Module LRMorphism.

Section ClassDef.

Variables (R : ringType) (A B : lalgType R).

Record class_of (f : A -> B) : Prop :=
  Class {base : rmorphism f; mixin : scalable f}.
Local Coercion base : class_of >-> rmorphism.
Definition base2 f (fLM : class_of f) := Linear.Class fLM (mixin fLM).
Local Coercion base2 : class_of >-> lmorphism.

Structure map (phAB : phant (A -> B)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phAB : phant (A -> B)) (f : A -> B) (cF : map phAB).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  fun (h : Linear.map phAB) fZ & phant_id (Linear.mixin (Linear.class h)) fZ =>
  Pack phAB (@Class f fM fZ).

Definition pack (fZ : scalable f) :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  Pack phAB (Class fM fZ).

Canonical additive := Additive.Pack phAB class.
Canonical rmorphism := RMorphism.Pack phAB class.
Canonical linear := Linear.Pack phAB class.
Canonical join_rmorphism := @RMorphism.Pack _ _ phAB linear class.
Canonical join_linear := @Linear.Pack R _ _ phAB rmorphism class.

End ClassDef.

Module Exports.
Notation lrmorphism f := (class_of f).
Coercion base : lrmorphism >-> RMorphism.class_of.
Coercion base2 : lrmorphism >-> Linear.class_of.
Coercion apply : map >-> Funclass.
Notation LRMorphism fZ := (pack fZ id).
Notation "{ 'lrmorphism' fAB }" := (map (Phant fAB))
  (at level 0, format "{ 'lrmorphism'  fAB }") : ring_scope.
Notation "[ 'lrmorphism' 'of' f ]" := (@clone _ _ _ _ f _ _ id _ _ id)
  (at level 0, format "[ 'lrmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
Coercion rmorphism : map >-> RMorphism.map.
Canonical rmorphism.
Coercion linear : map >-> Linear.map.
Canonical linear.
Canonical join_rmorphism.
Canonical join_linear.
End Exports.

End LRMorphism.
Include LRMorphism.Exports.

Section LRMorphismTheory.

Variables (R : ringType) (A B C : lalgType R) (f : {lrmorphism B -> C}).

Definition idfun_lrmorphism := [lrmorphism of (idfun : A -> A)].

Definition comp_lrmorphism (g : {lrmorphism A -> B}) := [lrmorphism of f \o g].

Lemma can2_lrmorphism f' : cancel f f' -> cancel f' f -> lrmorphism f'.
Proof.
move=> fK f'K; split; [exact: (can2_rmorphism fK) | exact: (can2_linear fK)].
Qed.

Lemma bij_lrmorphism :
  bijective f -> exists2 f' : {lrmorphism C -> B}, cancel f f' & cancel f' f.
Proof.
by case/bij_rmorphism=> f' fK f'K; exists (LRMorphism (can2_linear fK f'K)).
Qed.

End LRMorphismTheory.

Module ComRing.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Section ClassDef.

Record class_of R :=
  Class {base : Ring.class_of R; _ : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation comRingType := type.
Notation ComRingType T m := (@pack T _ m _ _ id _ id).
Notation ComRingMixin := RingMixin.
Notation "[ 'comRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comRingType'  'of'  T ]") : form_scope.
End Exports.

End ComRing.
Import ComRing.Exports.

Section ComRingTheory.

Variable R : comRingType.
Implicit Types x y : R.

Lemma mulrC : @commutative R R *%R. Proof. by case: R => T []. Qed.
Canonical mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R R *%R. Proof. exact: mulmCA. Qed.
Lemma mulrAC : @right_commutative R R *%R. Proof. exact: mulmAC. Qed.

Lemma exprn_mull n : {morph (fun x => x ^+ n) : x y / x * y}.
Proof. move=> x y; apply: commr_exp_mull; exact: mulrC. Qed.

Lemma prodr_exp n I r (P : pred I) (F : I -> R) :
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Proof. by rewrite (big_morph _ (exprn_mull n) (exp1rn _ n)). Qed.

Lemma exprn_addl x y n :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprn_addl_comm //; exact: mulrC. Qed.

Lemma exprn_subl x y n :
  (x - y) ^+ n =
     \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprn_subl_comm //; exact: mulrC. Qed.

Lemma subr_expn x y n :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof. by rewrite -subr_expn_comm //; exact: mulrC. Qed.

Lemma sqrr_add x y : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof. by rewrite exprn_addl !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

Lemma sqrr_sub x y : (x - y) ^+ 2 = x ^+ 2 - x * y *+ 2 + y ^+ 2.
Proof. by rewrite sqrr_add mulrN mulNrn sqrrN. Qed.

Lemma subr_sqr x y : x ^+ 2 - y ^+ 2 = (x - y) * (x + y).
Proof. by rewrite subr_expn !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

Lemma subr_sqr_add_sub x y : (x + y) ^+ 2 - (x - y) ^+ 2 = x * y *+ 4.
Proof.
rewrite sqrr_add sqrr_sub -!(addrAC _ (y ^+ 2)) oppr_sub.
by rewrite addrC addrA subrK -mulrn_addr.
Qed.

Section FrobeniusAutomorphism.

Variables (p : nat) (charRp : p \in [char R]).

Lemma Frobenius_aut_is_rmorphism : rmorphism (Frobenius_aut charRp).
Proof.
split=> [x y|]; first exact: Frobenius_aut_sub_comm (mulrC _ _).
split=> [x y|]; first exact: Frobenius_aut_mul_comm (mulrC _ _).
exact: Frobenius_aut_1.
Qed.

Canonical Frobenius_aut_additive := Additive Frobenius_aut_is_rmorphism.
Canonical Frobenius_aut_rmorphism := RMorphism Frobenius_aut_is_rmorphism.

End FrobeniusAutomorphism.

Lemma rmorph_comm (S : ringType) (f : {rmorphism R -> S}) x y : 
  comm (f x) (f y).
Proof. by red; rewrite -!rmorphM mulrC. Qed.

Section ScaleLinear.

Variables (U V : lmodType R) (b : R) (f : {linear U -> V}).

Lemma scale_is_scalable : scalable ( *:%R b : V -> V).
Proof. by move=> a v /=; rewrite !scalerA mulrC. Qed.
Canonical scale_linear := AddLinear scale_is_scalable.

Lemma scale_fun_is_scalable : scalable (b \*: f).
Proof. by move=> a v /=; rewrite !linearZ. Qed.
Canonical scale_fun_linear := AddLinear scale_fun_is_scalable.

End ScaleLinear.

End ComRingTheory.

Module Algebra.

Section Mixin.

Variables (R : ringType) (A : lalgType R).

Definition axiom := forall k (x y : A), k *: (x * y) = x * (k *: y).

Lemma comm_axiom : phant A -> commutative (@mul A) -> axiom.
Proof. by move=> _ commA k x y; rewrite commA scaler_mull commA. Qed.

End Mixin.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Lalgebra.class_of R T; 
  mixin : axiom (Lalgebra.Pack _ base T)
}.
Local Coercion base : class_of >-> Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.

Definition pack b0 (ax0 : @axiom R b0) :=
  fun bT b & phant_id (@Lalgebra.class R phR bT) b =>
  fun   ax & phant_id ax0 ax => Pack phR (@Class T b ax) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition lmodType := Lmodule.Pack phR class cT.
Definition lalgType := Lalgebra.Pack phR class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Notation algType R := (type (Phant R)).
Notation AlgType R A ax := (@pack _ (Phant R) A _ ax _ _ id _ id).
Notation CommAlgType R A := (AlgType R A (comm_axiom (Phant A) (@mulrC _))).
Notation "[ 'algType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'algType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'algType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'algType'  R 'of'  T ]") : form_scope.
End Exports.

End Algebra.
Import Algebra.Exports.

Section AlgebraTheory.

Variables (R : comRingType) (A : algType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_mulr k x y : k *: (x * y) = x * (k *: y).
Proof. by case: A k x y => T []. Qed.

Lemma scaler_swap k x y : k *: x * y = x * (k *: y).
Proof. by rewrite -scaler_mull scaler_mulr. Qed.

Lemma scaler_exp k x n : (k *: x) ^+ n = k ^+ n *: x ^+ n.
Proof. 
elim: n => [|n IHn]; first by rewrite !expr0 scale1r.
by rewrite !exprS IHn -scalerA scaler_mulr scaler_mull.
Qed.

Lemma scaler_prodl (I : finType) (S : pred I) (F : I -> A) k :
  \prod_(i \in S) (k *:  F i)  = k ^+ #|S| *: \prod_(i \in S) F i.
Proof.
rewrite -sum1_card /= -!(big_filter _ S) !unlock.
elim: {S}(filter _ _) => /= [|i r ->]; first by rewrite expr0 scale1r.
by rewrite -scaler_mull -scaler_mulr scalerA exprS.
Qed.

Lemma scaler_prodr (I : finType) (S : pred I) (F : I -> R) x :
  \prod_(i \in S) (F i *: x)  = \prod_(i \in S) F i *: x ^+ #|S|.
Proof.
rewrite -sum1_card /= -!(big_filter _ S) !unlock.
elim: {S}(filter _ _) => /= [|i r ->]; first by rewrite expr0 scale1r.
by rewrite -scaler_mull -scaler_mulr scalerA exprS.
Qed.

Lemma scaler_prod I r (P : pred I) (F : I -> R) (G : I -> A) :
  \prod_(i <- r | P i) (F i *: G i) =
    \prod_(i <- r | P i) (F i)  *: \prod_(i <- r | P i) (G i).
Proof.
rewrite -!(big_filter _ P) !unlock.
elim: {P r}(filter _ _) => /= [|i r ->]; first by rewrite scale1r.
by rewrite -scaler_mull -scaler_mulr scalerA.
Qed.

Canonical regular_comRingType := [comRingType of R^o].
Canonical regular_algType := CommAlgType R R^o.

Variables (U : lmodType R) (a : A) (f : {linear U -> A}).

Lemma mull_fun_is_scalable : scalable (a \*o f).
Proof. by move=> k x /=; rewrite linearZ scaler_mulr. Qed.
Canonical mull_fun_linear := AddLinear mull_fun_is_scalable.

End AlgebraTheory.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in predC unit, inv =1 id}
}.

Definition EtaMixin R unit inv mulVr mulrV unitP inv_out :=
  let _ := @Mixin R unit inv mulVr mulrV unitP inv_out in
  @Mixin (Ring.Pack (Ring.class R) R) unit inv mulVr mulrV unitP inv_out.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base R)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation unitRingType := type.
Notation UnitRingType T m := (@pack T _ m _ _ id _ id).
Notation UnitRingMixin := EtaMixin.
Notation "[ 'unitRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'unitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'unitRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'unitRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit (R : unitRingType) : pred R := UnitRing.unit (UnitRing.class R).
Definition inv (R : unitRingType) : R -> R := UnitRing.inv (UnitRing.class R).

Prenex Implicits unit.
Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr x : unit x -> x / x = 1.
Proof. by case: R x => T [? []]. Qed.
Definition mulrV := divrr.

Lemma mulVr x : unit x -> x^-1 * x = 1.
Proof. by case: R x => T [? []]. Qed.

Lemma invr_out x : ~~ unit x -> x^-1 = x.
Proof. by case: R x => T [? []]. Qed.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (unit x).
Proof.
apply: (iffP idP) => [Ux | []]; last by case: R x => T [? []].
by exists x^-1; rewrite divrr ?mulVr.
Qed.

Lemma mulKr x : unit x -> cancel (mul x) (mul x^-1).
Proof. by move=> Ux y; rewrite mulrA mulVr ?mul1r. Qed.

Lemma mulVKr x : unit x -> cancel (mul x^-1) (mul x).
Proof. by move=> Ux y; rewrite mulrA mulrV ?mul1r. Qed.

Lemma mulrK x : unit x -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by move=> Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma mulrVK x : unit x -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by move=> Ux y; rewrite -mulrA mulVr ?mulr1. Qed.
Definition divrK := mulrVK.

Lemma mulrI x : unit x -> injective (mul x).
Proof. move=> Ux; exact: can_inj (mulKr Ux). Qed.

Lemma mulIr x : unit x -> injective ( *%R^~ x).
Proof. move=> Ux; exact: can_inj (mulrK Ux). Qed.

Lemma commr_inv x : comm x x^-1.
Proof.
case Ux: (unit x); last by rewrite invr_out ?Ux.
by rewrite /comm mulVr ?divrr.
Qed.

Lemma unitrE x : unit x = (x / x == 1).
Proof.
apply/idP/eqP=> [Ux | xx1]; first exact: divrr.
by apply/unitrP; exists x^-1; rewrite -commr_inv.
Qed.

Lemma invrK : involutive (@inv R).
Proof.
move=> x; case Ux: (unit x); last by rewrite !invr_out ?Ux.
rewrite -(mulrK Ux _^-1) -mulrA commr_inv mulKr //.
by apply/unitrP; exists x; rewrite divrr ?mulVr.
Qed.

Lemma invr_inj : injective (@inv R).
Proof. exact: inv_inj invrK. Qed.

Lemma unitr_inv x : unit x^-1 = unit x.
Proof. by rewrite !unitrE invrK commr_inv. Qed.

Lemma unitr1 : unit (1 : R).
Proof. by apply/unitrP; exists 1; rewrite mulr1. Qed.

Lemma invr1 : 1^-1 = 1 :> R.
Proof. by rewrite -{2}(mulVr unitr1) mulr1. Qed.

Lemma div1r x : 1 / x = x^-1. Proof. by rewrite mul1r. Qed.
Lemma divr1 x : x / 1 = x. Proof. by rewrite invr1 mulr1. Qed.

Lemma natr_div m d :
  d %| m -> unit (d%:R : R) -> (m %/ d)%:R = m%:R / d%:R :> R.
Proof.
by rewrite dvdn_eq => /eqP def_m unit_d; rewrite -{2}def_m natr_mul mulrK.
Qed.

Lemma unitr0 : unit (0 : R) = false.
Proof.
by apply/unitrP=> [[x [_]]]; apply/eqP; rewrite mul0r eq_sym nonzero1r.
Qed.

Lemma invr0 : 0^-1 = 0 :> R.
Proof. by rewrite invr_out ?unitr0. Qed.

Lemma unitr_opp x : unit (- x) = unit x.
Proof.
wlog Ux: x / unit x.
  by move=> WHx; apply/idP/idP=> Ux; first rewrite -(opprK x); rewrite WHx.
by rewrite Ux; apply/unitrP; exists (- x^-1); rewrite !mulrNN mulVr ?divrr.
Qed.

Lemma invrN x : (- x)^-1 = - x^-1.
Proof.
case Ux: (unit x) (unitr_opp x) => [] Unx.
  by apply: (mulrI Unx); rewrite mulrNN !divrr.
by rewrite !invr_out ?Ux ?Unx.
Qed.

Lemma unitr_mull x y : unit y -> unit (x * y) = unit x.
Proof.
move=> Uy; wlog Ux: x y Uy / unit x => [WHxy|].
  by apply/idP/idP=> Ux; first rewrite -(mulrK Uy x); rewrite WHxy ?unitr_inv.
rewrite Ux; apply/unitrP; exists (y^-1 * x^-1).
by rewrite -!mulrA mulKr ?mulrA ?mulrK ?divrr ?mulVr.
Qed.

Lemma unitr_mulr x y : unit x -> unit (x * y) = unit y.
Proof.
move=> Ux; apply/idP/idP=> [Uxy | Uy]; last by rewrite unitr_mull.
by rewrite -(mulKr Ux y) unitr_mull ?unitr_inv.
Qed.

Lemma invr_mul x y : unit x -> unit y -> (x * y)^-1 = y^-1 * x^-1.
Proof.
move=> Ux Uy; have Uxy: unit (x * y) by rewrite unitr_mull.
by apply: (mulrI Uxy); rewrite divrr ?mulrA ?mulrK ?divrr.
Qed.

Lemma commr_unit_mul x y : comm x y -> unit (x * y) = unit x && unit y.
Proof.
move=> cxy; apply/idP/andP=> [Uxy | [Ux Uy]]; last by rewrite unitr_mull.
suffices Ux: unit x by rewrite unitr_mulr in Uxy.
apply/unitrP; case/unitrP: Uxy => z [zxy xyz]; exists (y * z).
rewrite mulrA xyz -{1}[y]mul1r -{1}zxy cxy -!mulrA (mulrA x) (mulrA _ z) xyz.
by rewrite mul1r -cxy.
Qed.

Lemma unitr_exp x n : unit x -> unit (x ^+ n).
Proof.
by move=> Ux; elim: n => [|n IHn]; rewrite ?unitr1 // exprS unitr_mull.
Qed.

Lemma unitr_pexp x n : n > 0 -> unit (x ^+ n) = unit x.
Proof.
case: n => // n _; rewrite exprS commr_unit_mul; last exact: commr_exp.
by case Ux: (unit x); rewrite // unitr_exp.
Qed.

Lemma expr_inv x n : x^-1 ^+ n = x ^- n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (unit x); first by rewrite exprSr exprS IHn -invr_mul // unitr_exp.
by rewrite !invr_out ?unitr_pexp ?Ux.
Qed.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
Proof.
move=> nx0; case Ux: (unit x); last by rewrite invr_out ?Ux.
by apply/eqP=> x'0; rewrite -unitr_inv x'0 unitr0 in Ux.
Qed.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
Proof. by apply: negb_inj; apply/idP/idP; move/invr_neq0; rewrite ?invrK. Qed.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> unit x.
Proof. by case=> [yx1 xy1]; apply/unitrP; exists y. Qed.

Definition converse_unitRingMixin :=
  @UnitRing.Mixin _ (unit : pred R^c) _ mulrV mulVr rev_unitrP invr_out.
Canonical converse_unitRingType := UnitRingType R^c converse_unitRingMixin.
Canonical regular_unitRingType := [unitRingType of R^o].

End UnitRingTheory.

Implicit Arguments invr_inj [[R] x1 x2].

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : unit x -> unit (f x).
Proof.
case/unitrP=> y [yx1 xy1]; apply/unitrP.
by exists (f y); rewrite -!rmorphM // yx1 xy1 rmorph1.
Qed.

Lemma rmorphV x : unit x -> f x^-1 = (f x)^-1.
Proof.
move=> Ux; rewrite -[(f x)^-1]mul1r; apply: (canRL (mulrK (rmorph_unit Ux))).
by rewrite -rmorphM mulVr ?rmorph1.
Qed.

Lemma rmorph_div x y : unit y -> f (x / y) = f x / f y.
Proof. by move=> Uy; rewrite rmorphM rmorphV. Qed.

End UnitRingMorphism.

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Proof. by move=> x Ux /=; rewrite mulrC mulVx. Qed.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof. case=> yx _; exact: unitPl yx. Qed.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base R)
}.
Local Coercion base : class_of >-> ComRing.class_of.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (ComRing.class bT) (b : ComRing.class_of T) =>
  fun mT m & phant_id (UnitRing.class mT) (@UnitRing.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition comRingType := ComRing.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition com_unitRingType := @UnitRing.Pack comRingType class cT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion mixin : class_of >-> UnitRing.mixin_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Canonical com_unitRingType.
Notation comUnitRingType := type.
Notation ComUnitRingMixin := Mixin.
Notation "[ 'comUnitRingType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'comUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module UnitAlgebra.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Algebra.class_of R T; 
  mixin : GRing.UnitRing.mixin_of (Ring.Pack base T)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.class mT) (@UnitRing.Class T b m) =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition lmodType := Lmodule.Pack phR class cT.
Definition lalgType := Lalgebra.Pack phR class cT.
Definition algType := Algebra.Pack phR class cT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType class cT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType class cT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Notation unitAlgType R := (type (Phant R)).
Notation "[ 'unitAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'unitAlgType' R 'of'  T ]") : form_scope.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Section ComUnitRingTheory.

Variable R : comUnitRingType.
Implicit Types x y : R.

Lemma unitr_mul x y : unit (x * y) = unit x && unit y.
Proof. by apply: commr_unit_mul; exact: mulrC. Qed.

Canonical regular_comUnitRingType := [comUnitRingType of R^o].
Canonical regular_unitAlgType := [unitAlgType R of R^o].

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Variable (R : comUnitRingType) (A : unitAlgType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_injl k : unit k -> @injective _ A ( *:%R k).
Proof.
move=> Uk x1 x2 Hx1x2.
by rewrite -[x1]scale1r -(mulVr Uk) -scalerA Hx1x2 scalerA mulVr // scale1r.
Qed.

Lemma scaler_unit k x : unit k -> unit x = unit (k *: x).
Proof.
move=> Uk; apply/idP/idP=> [Ux | Ukx]; apply/unitrP.
  exists (k^-1 *: x^-1).
  by rewrite -!scaler_mull -!scaler_mulr !scalerA !mulVr // !mulrV // scale1r.
exists (k *: (k *: x)^-1); split.
  apply (mulrI Ukx).
  by rewrite mulr1 mulrA -scaler_mulr mulrV // -scaler_mull mul1r.
apply (mulIr Ukx).
by rewrite mul1r -mulrA -scaler_mull mulVr // -scaler_mulr mulr1.
Qed.
 
Lemma scaler_inv k x : unit k -> unit x -> (k *: x)^-1 = k^-1 *: x^-1.
Proof.
move=> Uk Ux; have Ukx : unit (k *: x) by rewrite -scaler_unit //.
apply (mulIr Ukx).
by rewrite mulVr // -scaler_mull -scaler_mulr scalerA !mulVr // scale1r.
Qed.  

End UnitAlgebraTheory.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Scope Add [_ term_scope term_scope].
Arguments Scope Opp [_ term_scope].
Arguments Scope NatMul [_ term_scope nat_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Inv [_ term_scope].
Arguments Scope Exp [_ term_scope nat_scope].
Arguments Scope Equal [_ term_scope term_scope].
Arguments Scope Unit [_ term_scope].
Arguments Scope And [_ term_scope term_scope].
Arguments Scope Or [_ term_scope term_scope].
Arguments Scope Implies [_ term_scope term_scope].
Arguments Scope Not [_ term_scope].
Arguments Scope Exists [_ nat_scope term_scope].
Arguments Scope Forall [_ nat_scope term_scope].

Implicit Arguments Bool [R].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not.
Prenex Implicits Exists Forall.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
Proof. by move=> eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
case: s => i u; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => unit (eval e t1)
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
Proof. exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
by move=> i f1 IH1 e e'; move/(eq_i i); eauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof.
elim: f e => //=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (IHf (set_nth 0 e j x)) (f_ x);
  by rewrite set_set_nth eq_sym eq_ji; tauto.
Qed.

(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
Proof.
elim: t r n => //.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices eq0_ring t1: rformula (eq0_rform t1) by elim: f => //= => f1 ->.
rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {t1} t1 r /= /andP[t1_r].
  by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; exact: IHr.
have: all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r /IHt1; case: to_rterm.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof.
suffices{e f} equal0_equiv e t1 t2:
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + move=> t1 e; rewrite unitrE; exact: equal0_equiv.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst s t0: s.1 >= ub_var t0 -> tsubst t0 s = t0.
  elim: t0 {t} => //=.
  - by move=> n; case: ltngtP.
  - by move=> t1 IHt1 t2 IHt2; rewrite leq_maxl => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
  - by move=> t1 IHt1 t2 IHt2; rewrite leq_maxl => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Prop :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: m >= ub_var t -> ub_sub m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t].
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (unit y); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id r t0 n: ub_var t0 <= n -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  ub_var t1 <= m1 + size r -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite leq_maxl; case/andP=> hub1 hub2 hmr;
  case: to_rterm {IHt1 hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite leq_maxl; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take leq_minl leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move/IHt1=> {IHt1}IHt1
     | move=> t1 IHt1 n r m; do 2!move/IHt1=> {IHt1}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take leq_minl leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].
Qed.

(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => unit (eval e t1)
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
elim: f => //=; try by move=> *; exact: idP.
- move=> t1 t2 _; exact: eqP.
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1F]; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1 /IHf1[]; [right | left].
Qed.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in 
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
Proof.
by elim: bcs => //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF.
Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; exact/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim: f b => //=; try by [move=> _ ? ? [] | move=> ? ? ? ? [] /= /andP[]; auto].
- by do 2!case.
- by rewrite /dnf_rterm => ? ? [] /= ->.
by auto.
Qed.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by congr andb; [elim: cl1 | elim: cl2] => //= t cl ->; rewrite andbT.
Qed.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
Proof. by move=> /= -> -> ->. Qed.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
Proof. by move=> /= -> -> ->. Qed.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
Proof. by rewrite /=; case: ifP => _; rewrite ?orbF. Qed. 

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph qf_form) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //=; move/negbTE.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [exact | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Module IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.

Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; _: axiom (Ring.Pack base R)}.
Local Coercion base : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (ComUnitRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition comRingType := ComRing.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := ComUnitRing.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Notation idomainType := type.
Notation IdomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'idomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'idomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'idomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'idomainType'  'of'  T ]") : form_scope.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Section IntegralDomainTheory.

Variable R : idomainType.
Implicit Types x y : R.

Lemma mulf_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/eqP/idP; first by case: R x y => T [].
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma prodf_eq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by rewrite (bigD1 i) //= Fi0 mul0r.
elim: (index_enum _) => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | _] := ifP; last exact: IHr.
by rewrite mulf_eq0; case/orP=> // Fi0; exists i.
Qed.

Lemma mulf_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof. move=> x0 y0; rewrite mulf_eq0; exact/norP. Qed.

Lemma prodf_neq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (forall i, P i -> (F i != 0)) (\prod_(i | P i) F i != 0).
Proof.
by rewrite (sameP (prodf_eq0 _ _) exists_inP) negb_exists_in; exact: forall_inP.
Qed.

Lemma expf_eq0 x n : (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
elim: n => [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulf_eq0 IHn andKb.
Qed.

Lemma expf_neq0 x m : x != 0 -> x ^+ m != 0.
Proof. by move=> x_nz; rewrite expf_eq0; apply/nandP; right. Qed.

Lemma mulfI x : x != 0 -> injective ( *%R x).
Proof.
move=> nz_x y z; rewrite -[x * z]add0r; move/(canLR (addrK _))/eqP.
rewrite -mulrN -mulr_addr mulf_eq0 (negbTE nz_x) /=.
by move/eqP/(canRL (subrK _)); rewrite add0r.
Qed.

Lemma mulIf x : x != 0 -> injective ( *%R^~ x).
Proof. by move=> nz_x y z; rewrite -!(mulrC x); exact: mulfI. Qed.

Lemma sqrf_eq1 x : (x ^+ 2 == 1) = (x == 1) || (x == -1).
Proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma expfS_eq1 x n :
  (x ^+ n.+1 == 1) = (x == 1) || (\sum_(i < n.+1) x ^+ i == 0).
Proof. by rewrite -![_ == 1]subr_eq0 subr_expn_1 mulf_eq0. Qed.

Lemma lregP x : reflect (lreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulfI | /lreg_neq0]. Qed.

Lemma rregP x : reflect (rreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulIf | /rreg_neq0]. Qed.

Canonical regular_idomainType := [idomainType of R^o].

End IntegralDomainTheory.

Implicit Arguments lregP [R x].
Implicit Arguments rregP [R x].

Module Field.

Definition mixin_of (F : unitRingType) := forall x : F, x != 0 -> unit x.

Lemma IdomainMixin R : mixin_of R -> IntegralDomain.axiom R.
Proof.
move=> m x y xy0; apply/norP=> [[]] /m Ux /m.
by rewrite -(unitr_mulr _ Ux) xy0 unitr0.
Qed.

Section Mixins.

Variables (R : comRingType) (inv : R -> R).

Definition axiom := forall x, x != 0 -> inv x * x = 1.
Hypothesis mulVx : axiom.
Hypothesis inv0 : inv 0 = 0.

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
Proof.
by move=> yx1; apply: contraNneq (nonzero1r R) => x0; rewrite -yx1 x0 mulr0.
Qed.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof. by move=> x /negbNE/eqP->. Qed.

Definition UnitMixin := ComUnitRing.Mixin mulVx intro_unit inv_out.

Lemma Mixin : mixin_of (UnitRing.Pack (UnitRing.Class UnitMixin) R).
Proof. by []. Qed.

End Mixins.

Section ClassDef.

Record class_of (F : Type) : Type := Class {
  base : IntegralDomain.class_of F;
  _ : mixin_of (UnitRing.Pack base F)
}.
Local Coercion base : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (IntegralDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition comRingType := ComRing.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := ComUnitRing.Pack class cT.
Definition idomainType := IntegralDomain.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Notation fieldType := type.
Notation FieldType T m := (@pack T _ m _ _ id _ id).
Notation FieldUnitMixin := UnitMixin.
Notation FieldIdomainMixin := IdomainMixin.
Notation FieldMixin := Mixin.
Notation "[ 'fieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'fieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'fieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'fieldType'  'of'  T ]") : form_scope.
End Exports.

End Field.
Import Field.Exports.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.

Lemma unitfE x : unit x = (x != 0).
Proof.
apply/idP/idP=> [Ux |]; last by case: F x => T [].
by apply/eqP=> x0; rewrite x0 unitr0 in Ux.
Qed.

Lemma mulVf x : x != 0 -> x^-1 * x = 1.
Proof. by rewrite -unitfE; exact: mulVr. Qed.
Lemma divff x : x != 0 -> x / x = 1.
Proof. by rewrite -unitfE; exact: divrr. Qed.
Definition mulfV := divff.
Lemma mulKf x : x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by rewrite -unitfE; exact: mulKr. Qed.
Lemma mulVKf x : x != 0 -> cancel ( *%R x^-1) ( *%R x).
Proof. by rewrite -unitfE; exact: mulVKr. Qed.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by rewrite -unitfE; exact: mulrK. Qed.
Lemma mulfVK x : x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by rewrite -unitfE; exact: divrK. Qed.
Definition divfK := mulfVK.

Lemma invf_mul : {morph (fun x => x^-1) : x y / x * y}.
Proof.
move=> x y; case: (eqVneq x 0) => [-> |nzx]; first by rewrite !(mul0r, invr0).
case: (eqVneq y 0) => [-> |nzy]; first by rewrite !(mulr0, invr0).
by rewrite mulrC invr_mul ?unitfE.
Qed.

Lemma prodf_inv I r (P : pred I) (E : I -> F) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof. by rewrite (big_morph _ invf_mul (invr1 _)). Qed.

Lemma natf0_char n : n > 0 -> n%:R == 0 :> F -> exists p, p \in [char F].
Proof.
elim: {n}_.+1 {-2}n (ltnSn n) => // m IHm n; rewrite ltnS => le_n_m.
rewrite leq_eqVlt -pi_pdiv mem_primes; move: (pdiv n) => p.
case/predU1P=> [<-|/and3P[p_pr n_gt0 /dvdnP[n']]]; first by rewrite oner_eq0.
move=> def_n; rewrite def_n muln_gt0 andbC prime_gt0 // in n_gt0 *.
rewrite natr_mul mulf_eq0 orbC; case/orP; first by exists p; exact/andP.
by apply: IHm (leq_trans _ le_n_m) _; rewrite // def_n ltn_Pmulr // prime_gt1.
Qed.

Lemma charf'_nat n : [char F]^'.-nat n = (n%:R != 0 :> F).
Proof.
have [-> | n_gt0] := posnP n; first by rewrite eqxx.
apply/idP/idP => [|nz_n]; last first.
  by apply/pnatP=> // p p_pr p_dvd_n; apply: contra nz_n => /dvdn_charf <-.
apply: contraL => n0; have [// | p charFp] := natf0_char _ n0.
have [p_pr _] := andP charFp; rewrite (eq_pnat _ (eq_negn (charf_eq charFp))).
by rewrite p'natE // (dvdn_charf charFp) n0.
Qed.

Lemma charf0P : [char F] =i pred0 <-> (forall n, (n%:R == 0 :> F) = (n == 0)%N).
Proof.
split=> charF0 n; last by rewrite !inE charF0 andbC; case: eqP => // ->.
have [-> | n_gt0] := posnP; first exact: eqxx.
by apply/negP; case/natf0_char=> // p; rewrite charF0.
Qed.

Lemma char0_natf_div :
  [char F] =i pred0 -> forall m d, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof.
move/charf0P=> char0F m [|d] d_dv_m; first by rewrite divn0 invr0 mulr0.
by rewrite natr_div // unitfE char0F.
Qed.

Section FieldMorphismInj.

Variables (R : ringType) (f : {rmorphism F -> R}).

Lemma fmorph_eq0 x : (f x == 0) = (x == 0).
Proof.
have [-> | nz_x] := altP (x =P _); first by rewrite rmorph0 eqxx.
apply/eqP; move/(congr1 ( *%R (f x^-1)))/eqP.
by rewrite -rmorphM mulVf // mulr0 rmorph1 ?oner_eq0.
Qed.

Lemma fmorph_inj : injective f.
Proof.
move=> x y eqfxy; apply/eqP; rewrite -subr_eq0 -fmorph_eq0 rmorph_sub //.
by rewrite eqfxy subrr.
Qed.

Lemma fmorph_char : [char R] =i [char F].
Proof. by move=> p; rewrite !inE -fmorph_eq0 rmorph_nat. Qed.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : unitRingType) (f : {rmorphism F -> R}).

Lemma fmorph_unit x : unit (f x) = (x != 0).
Proof.
have [-> |] := altP (x =P _); first by rewrite rmorph0 unitr0.
by rewrite -unitfE; exact: rmorph_unit.
Qed.

Lemma fmorphV : {morph f: x / x^-1}.
Proof.
move=> x; have [-> | nz_x] := eqVneq x 0; first by rewrite !(invr0, rmorph0).
by rewrite rmorphV ?unitfE.
Qed.

Lemma fmorph_div : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite rmorphM fmorphV. Qed.

End FieldMorphismInv.

Canonical regular_fieldType := [fieldType of F^o].

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma scalerK a : a != 0 -> cancel ( *:%R a : V -> V) ( *:%R a^-1).
Proof. by move=> nz_a v; rewrite scalerA mulVf // scale1r. Qed.

Lemma scalerKV a : a != 0 -> cancel ( *:%R a^-1 : V -> V) ( *:%R a).
Proof. by rewrite -invr_eq0 -{3}[a]invrK; exact: scalerK. Qed.

Lemma scalerI a : a != 0 -> injective ( *:%R a : V -> V).
Proof. move=> nz_a; exact: can_inj (scalerK nz_a). Qed.

Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
Proof.
have [-> | nz_a] := altP (a =P _); first by rewrite scale0r eqxx.
by rewrite (can2_eq (scalerK nz_a) (scalerKV nz_a)) scaler0.
Qed.

End ModuleTheory.

End FieldTheory.

Implicit Arguments fmorph_inj [F R x1 x2].

Module DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.

Record class_of (F : Type) : Type :=
  Class {base : Field.class_of F; mixin : mixin_of (UnitRing.Pack base F)}.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition comRingType := ComRing.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := ComUnitRing.Pack class cT.
Definition idomainType := IntegralDomain.Pack class cT.
Definition fieldType := Field.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Field.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Notation decFieldType := type.
Notation DecFieldType T m := (@pack T _ m _ _ id _ id).
Notation DecFieldMixin := Mixin.
Notation "[ 'decFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'decFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'decFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'decFieldType'  'of'  T ]") : form_scope.
End Exports.

End DecidableField.
Import DecidableField.Exports.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
Proof. exact: DecidableField.satP. Qed.

Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP=> /eqP sz_s /satP f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_maxr leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
Proof.
rewrite /sol; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP) => /eqP.
Qed.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => /eq_sat eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Implicit Arguments satP [F e f].
Implicit Arguments solP [F n f].

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
(* proj is the elimination of a single existential quantifier *)

(* The elimination projector is well_formed. *)
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

(* The elimination projector is valid *)
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf f0 n : let qf := elim_aux f0 n in
  rformula f0 -> qf_form qf && rformula qf.
- by elim: f => //=; do ?[  move=> f1 IH1 f2 IH2;
                     case/andP=> rf1 rf2;
                     case/andP:(IH1 rf1)=> -> ->;
                     case/andP:(IH2 rf2)=> -> -> //
                  |  move=> n f1 IH rf1;
                     case/andP: (IH rf1)=> qff rf;
                     rewrite aux_wf ].
rewrite /elim_aux => rf.
suffices or_wf fs : let ofs := foldr Or False fs in 
  all (@qf_form F) fs && all (@rformula F) fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all (@qf_form _) mbcs && all (@rformula _) mbcs.
    by apply: map_proj_wf; exact: qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_dnf f0 false.
  apply: (@iffP (rc e0 n0 (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; exact: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: ok_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- move=> b e _; exact: idP.
- move=> t1 t2 e _; exact: eqP.
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /= /IHf[]; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; exact/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x /IHf[].
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

Definition QEdecFieldMixin := DecidableField.Mixin proj_satP.

End QE_Mixin.

Module ClosedField.

(* Axiom == all non-constant monic polynomials have a root *)
Definition axiom (R : ringType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Section ClassDef.

Record class_of (F : Type) : Type :=
  Class {base : DecidableField.class_of F; _ : axiom (Ring.Pack base F)}.
Local Coercion base : class_of >-> DecidableField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (DecidableField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* There should eventually be a constructor from polynomial resolution *)
(* that builds the DecidableField mixin using QE.                      *)

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := Zmodule.Pack class cT.
Definition ringType := Ring.Pack class cT.
Definition comRingType := ComRing.Pack class cT.
Definition unitRingType := UnitRing.Pack class cT.
Definition comUnitRingType := ComUnitRing.Pack class cT.
Definition idomainType := IntegralDomain.Pack class cT.
Definition fieldType := Field.Pack class cT.
Definition decFieldType := DecidableField.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DecidableField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> DecidableField.type.
Canonical decFieldType.
Notation closedFieldType := type.
Notation ClosedFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'closedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'closedFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'closedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'closedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma solve_monicpoly : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.

End ClosedFieldTheory.

Module Theory.

Definition addrA := addrA.
Definition addrC := addrC.
Definition add0r := add0r.
Definition addNr := addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition subrr := subrr.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addKr := addKr.
Definition addNKr := addNKr.
Definition addrK := addrK.
Definition addrNK := addrNK.
Definition subrK := subrK.
Definition addrI := addrI.
Definition addIr := addIr.
Implicit Arguments addrI [V x1 x2].
Implicit Arguments addIr [V x1 x2].
Definition opprK := opprK.
Definition oppr_inj := @oppr_inj.
Implicit Arguments oppr_inj [[V] x1 x2].
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition oppr_add := oppr_add.
Definition oppr_sub := oppr_sub.
Definition subr0 := subr0.
Definition sub0r := sub0r.
Definition subr_eq := subr_eq.
Definition subr_eq0 := subr_eq0.
Definition addr_eq0 := addr_eq0.
Definition eqr_opp := eqr_opp.
Definition eqr_oppC := eqr_oppC.
Definition sumr_opp := sumr_opp.
Definition sumr_sub := sumr_sub.
Definition sumr_muln := sumr_muln.
Definition sumr_muln_r := sumr_muln_r.
Definition sumr_const := sumr_const.
Definition mulr0n := mulr0n.
Definition mulr1n := mulr1n.
Definition mulr2n := mulr2n.
Definition mulrS := mulrS.
Definition mulrSr := mulrSr.
Definition mulrb := mulrb.
Definition mul0rn := mul0rn.
Definition mulNrn := mulNrn.
Definition mulrn_addl := mulrn_addl.
Definition mulrn_addr := mulrn_addr.
Definition mulrn_subl := mulrn_subl.
Definition mulrn_subr := mulrn_subr.
Definition mulrnA := mulrnA.
Definition mulrnAC := mulrnAC.
Definition mulrA := mulrA.
Definition mul1r := mul1r.
Definition mulr1 := mulr1.
Definition mulr_addl := mulr_addl.
Definition mulr_addr := mulr_addr.
Definition nonzero1r := nonzero1r.
Definition oner_eq0 := oner_eq0.
Definition mul0r := mul0r.
Definition mulr0 := mulr0.
Definition mulrN := mulrN.
Definition mulNr := mulNr.
Definition mulrNN := mulrNN.
Definition mulN1r := mulN1r.
Definition mulrN1 := mulrN1.
Definition mulr_suml := mulr_suml.
Definition mulr_sumr := mulr_sumr.
Definition mulr_subl := mulr_subl.
Definition mulr_subr := mulr_subr.
Definition mulrnAl := mulrnAl.
Definition mulrnAr := mulrnAr.
Definition mulr_natl := mulr_natl.
Definition mulr_natr := mulr_natr.
Definition natr_add := natr_add.
Definition natr_sub := natr_sub.
Definition natr_sum := natr_sum.
Definition natr_mul := natr_mul.
Definition natr_exp := natr_exp.
Definition expr0 := expr0.
Definition exprS := exprS.
Definition expr1 := expr1.
Definition expr2 := expr2.
Definition exp1rn := exp1rn.
Definition exprn_addr := exprn_addr.
Definition exprSr := exprSr.
Definition commr_sym := commr_sym.
Definition commr_refl := commr_refl.
Definition commr0 := commr0.
Definition commr1 := commr1.
Definition commr_opp := commr_opp.
Definition commrN1 := commrN1.
Definition commr_add := commr_add.
Definition commr_muln := commr_muln.
Definition commr_mul := commr_mul.
Definition commr_nat := commr_nat.
Definition commr_exp := commr_exp.
Definition commr_exp_mull := commr_exp_mull.
Definition commr_sign := commr_sign.
Definition exprn_mulnl := exprn_mulnl.
Definition exprn_mulr := exprn_mulr.
Definition exprnC := exprnC.
Definition exprn_mod := exprn_mod.
Definition exprn_dvd := exprn_dvd.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition mulr_sign := mulr_sign.
Definition signr_addb := signr_addb.
Definition exprN := exprN.
Definition sqrrN := sqrrN.
Definition mulrI_eq0 := mulrI_eq0.
Definition lreg_neq0 := lreg_neq0.
Definition mulrI0_lreg := mulrI0_lreg.
Definition lregN := lregN.
Definition lreg1 := lreg1.
Definition lregM := lregM.
Definition lregX := lregX.
Definition lregP := @lregP.
Definition mulIr_eq0 := mulIr_eq0.
Definition mulIr0_rreg := mulIr0_rreg.
Definition rreg_neq0 := rreg_neq0.
Definition rregN := rregN.
Definition rreg1 := rreg1.
Definition rregM := rregM.
Definition revrX := revrX.
Definition rregX := rregX.
Definition rregP := @rregP.
Definition exprn_addl_comm := exprn_addl_comm.
Definition exprn_subl_comm := exprn_subl_comm.
Definition subr_expn_comm := subr_expn_comm.
Definition exprn_add1 := exprn_add1.
Definition subr_expn_1 := subr_expn_1.
Definition sqrr_add1 := sqrr_add1.
Definition sqrr_sub1 := sqrr_sub1.
Definition subr_sqr_1 := subr_sqr_1.
Definition charf0 := charf0.
Definition charf_prime := charf_prime.
Definition dvdn_charf := dvdn_charf.
Definition charf_eq := charf_eq.
Definition bin_lt_charf_0 := bin_lt_charf_0.
Definition Frobenius_autE := Frobenius_autE.
Definition Frobenius_aut_0 := Frobenius_aut_0.
Definition Frobenius_aut_1 := Frobenius_aut_1.
Definition Frobenius_aut_add_comm := Frobenius_aut_add_comm.
Definition Frobenius_aut_muln := Frobenius_aut_muln.
Definition Frobenius_aut_nat := Frobenius_aut_nat.
Definition Frobenius_aut_mul_comm := Frobenius_aut_mul_comm.
Definition Frobenius_aut_exp := Frobenius_aut_exp.
Definition Frobenius_aut_opp := Frobenius_aut_opp.
Definition Frobenius_aut_sub_comm := Frobenius_aut_sub_comm.
Definition prodr_const := prodr_const.
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition exprn_mull := exprn_mull.
Definition prodr_exp := prodr_exp.
Definition prodr_exp_r := prodr_exp_r.
Definition prodr_opp := prodr_opp.
Definition exprn_addl := exprn_addl.
Definition exprn_subl := exprn_subl.
Definition subr_expn := subr_expn.
Definition sqrr_add := sqrr_add.
Definition sqrr_sub := sqrr_sub.
Definition subr_sqr := subr_sqr.
Definition subr_sqr_add_sub := subr_sqr_add_sub.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP := unitrP.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition commr_inv := commr_inv.
Definition unitrE := unitrE.
Definition invrK := invrK.
Definition invr_inj := @invr_inj.
Implicit Arguments invr_inj [[R] x1 x2].
Definition unitr_inv := unitr_inv.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition divr1 := divr1.
Definition div1r := div1r.
Definition natr_div := natr_div.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitr_opp := unitr_opp.
Definition invrN := invrN.
Definition unitr_mull := unitr_mull.
Definition unitr_mulr := unitr_mulr.
Definition invr_mul := invr_mul.
Definition invr_eq0 := invr_eq0.
Definition invr_neq0 := invr_neq0.
Definition commr_unit_mul := commr_unit_mul.
Definition unitr_exp := unitr_exp.
Definition unitr_pexp := unitr_pexp.
Definition expr_inv := expr_inv.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitr_mul := unitr_mul.
Definition mulf_eq0 := mulf_eq0.
Definition prodf_eq0 := prodf_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition prodf_neq0 := prodf_neq0.
Definition expf_eq0 := expf_eq0.
Definition expf_neq0 := expf_neq0.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition sqrf_eq1 := sqrf_eq1.
Definition expfS_eq1 := expfS_eq1.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition invf_mul := invf_mul.
Definition prodf_inv := prodf_inv.
Definition natf0_char := natf0_char.
Definition charf'_nat := charf'_nat.
Definition charf0P := charf0P.
Definition char0_natf_div := char0_natf_div.
Definition satP := @satP.
Definition eq_sat := eq_sat.
Definition solP := @solP.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := solve_monicpoly.
Definition raddf0 := raddf0.
Definition raddfN := raddfN.
Definition raddfD := raddfD.
Definition raddf_sub := raddf_sub.
Definition raddf_sum := raddf_sum.
Definition raddfMn := raddfMn.
Definition raddfMNn := raddfMNn.
Definition can2_additive := can2_additive.
Definition bij_additive := bij_additive.
Definition rmorph0 := rmorph0.
Definition rmorphN := rmorphN.
Definition rmorphD := rmorphD.
Definition rmorph_sub := rmorph_sub.
Definition rmorph_sum := rmorph_sum.
Definition rmorphMn := rmorphMn.
Definition rmorphMNn := rmorphMNn.
Definition rmorphismP := rmorphismP.
Definition rmorphismMP := rmorphismMP.
Definition rmorph1 := rmorph1.
Definition rmorphM := rmorphM.
Definition rmorph_nat := rmorph_nat.
Definition rmorph_prod := rmorph_prod.
Definition rmorphX := rmorphX.
Definition rmorph_sign := rmorph_sign.
Definition rmorph_char := rmorph_char.
Definition can2_rmorphism := can2_rmorphism.
Definition bij_rmorphism := bij_rmorphism.
Definition rmorph_comm := rmorph_comm.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := fmorph_inj.
Implicit Arguments fmorph_inj [F R x1 x2].
Definition fmorph_char := fmorph_char.
Definition fmorph_unit := fmorph_unit.
Definition fmorphV := fmorphV.
Definition fmorph_div := fmorph_div.
Definition scalerA := scalerA.
Definition scale1r := scale1r.
Definition scaler_addr := scaler_addr.
Definition scaler_addl := scaler_addl.
Definition scaler0 := scaler0.
Definition scale0r := scale0r.
Definition scaleNr := scaleNr.
Definition scaleN1r := scaleN1r.
Definition scalerN := scalerN.
Definition scaler_subl := scaler_subl.
Definition scaler_subr := scaler_subr.
Definition scaler_nat := scaler_nat.
Definition scaler_mulrnl := scaler_mulrnl.
Definition scaler_mulrnr := scaler_mulrnr.
Definition scaler_suml := scaler_suml.
Definition scaler_sumr := scaler_sumr.
Definition scaler_eq0 := scaler_eq0.
Definition scalerK := scalerK.
Definition scalerKV := scalerKV.
Definition scalerI := scalerI.
Definition scaler_mull := scaler_mull.
Definition scaler_mulr := scaler_mulr.
Definition scaler_sign := scaler_sign.
Definition scaler_swap := scaler_swap.
Definition scaler_exp := scaler_exp.
Definition scaler_prodl := scaler_prodl.
Definition scaler_prodr := scaler_prodr.
Definition scaler_prod := scaler_prod.
Definition scaler_injl := scaler_injl.
Definition scaler_unit := scaler_unit.
Definition scaler_inv := scaler_inv.
Definition linearP := linearP.
Definition linear0 := linear0.
Definition linearN := linearN.
Definition linearD := linearD.
Definition linear_sub := linear_sub.
Definition linear_sum := linear_sum.
Definition linearMn := linearMn.
Definition linearMNn := linearMNn.
Definition linearZ := linearZ.
Definition can2_linear := can2_linear.
Definition bij_linear := bij_linear.
Definition can2_lrmorphism := can2_lrmorphism.
Definition bij_lrmorphism := bij_lrmorphism.

Implicit Arguments lregP [R x].
Implicit Arguments rregP [R x].
Implicit Arguments satP [F e f].
Implicit Arguments solP [F n f]. 	 

Notation null_fun V := (null_fun V) (only parsing).
Notation in_alg A := (in_alg_loc A).

End Theory.

Notation in_alg A := (in_alg_loc A).

End GRing.

Export Zmodule.Exports Ring.Exports Lmodule.Exports Lalgebra.Exports.
Export Additive.Exports RMorphism.Exports Linear.Exports LRMorphism.Exports.
Export ComRing.Exports Algebra.Exports UnitRing.Exports UnitAlgebra.Exports.
Export ComUnitRing.Exports IntegralDomain.Exports Field.Exports.
Export DecidableField.Exports ClosedField.Exports.
Notation QEdecFieldMixin := QEdecFieldMixin.

Notation "0" := (zero _) : ring_scope.
Notation "-%R" := (@opp _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _).
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.
Notation Frobenius_aut chRp := (Frobenius_aut chRp).
Notation "*%R" := (@mul _).
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

Notation "*:%R" := (@scale _ _).
Notation "a *: m" := (scale a m) : ring_scope.
Notation "k %:A" := (scale k 1) : ring_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun_head tt f g) : ring_scope.
Notation "f \- g" := (sub_fun_head tt f g) : ring_scope.
Notation "a \*: f" := (scale_fun_head tt a f) : ring_scope.
Notation "x \*o f" := (mull_fun_head tt x f) : ring_scope.
Notation "x \o* f" := (mulr_fun_head tt x f) : ring_scope.

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%R/0%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i \in A | P ) F" :=
  (\big[+%R/0%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i \in A ) F" :=
  (\big[+%R/0%R]_(i \in A) F%R) : ring_scope.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%R/1%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[*%R/1%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[*%R/1%R]_(i \in A) F%R) : ring_scope.

Canonical add_monoid.
Canonical add_comoid.
Canonical mul_monoid.
Canonical mul_comoid.
Canonical muloid.
Canonical addoid.

Canonical idfun_additive.
Canonical idfun_rmorphism.
Canonical idfun_linear.
Canonical idfun_lrmorphism.
Canonical comp_additive.
Canonical comp_rmorphism.
Canonical comp_linear.
Canonical comp_lrmorphism.
Canonical opp_additive.
Canonical opp_linear.
Canonical scale_additive.
Canonical scale_linear.
Canonical null_fun_additive.
Canonical null_fun_linear.
Canonical scale_fun_additive.
Canonical scale_fun_linear.
Canonical add_fun_additive.
Canonical add_fun_linear.
Canonical sub_fun_additive.
Canonical sub_fun_linear.
Canonical mull_fun_additive.
Canonical mull_fun_linear.
Canonical mulr_fun_additive.
Canonical mulr_fun_linear.
Canonical Frobenius_aut_additive.
Canonical Frobenius_aut_rmorphism.
Canonical in_alg_additive.
Canonical in_alg_rmorphism.

Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.
Canonical converse_eqType.
Canonical converse_choiceType.
Canonical converse_zmodType.
Canonical converse_ringType.
Canonical converse_unitRingType.

Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.
Canonical regular_eqType.
Canonical regular_choiceType.
Canonical regular_zmodType.
Canonical regular_ringType.
Canonical regular_lmodType.
Canonical regular_lalgType.
Canonical regular_comRingType.
Canonical regular_algType.
Canonical regular_unitRingType.
Canonical regular_comUnitRingType.
Canonical regular_unitAlgType.
Canonical regular_idomainType.
Canonical regular_fieldType.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

(* Lifting Structure from the codomain of finfuns. *)
Section FinFunZmod.

Variable (aT : finType) (rT : zmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_zero := [ffun a : aT => (0 : rT)].
Definition ffun_opp f := [ffun a => - f a].
Definition ffun_add f g := [ffun a => f a + g a].

Fact ffun_addA : associative ffun_add.
Proof. by move=> f1 f2 f3; apply/ffunP=> a; rewrite !ffunE addrA. Qed.
Fact ffun_addC : commutative ffun_add.
Proof. by move=> f1 f2; apply/ffunP=> a; rewrite !ffunE addrC. Qed.
Fact ffun_add0 : left_id ffun_zero ffun_add.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE add0r. Qed.
Fact ffun_addN : left_inverse ffun_zero ffun_opp ffun_add.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE addNr. Qed.

Definition ffun_zmodMixin :=
  Zmodule.Mixin ffun_addA ffun_addC ffun_add0 ffun_addN.
Canonical ffun_zmodType := Eval hnf in ZmodType _ ffun_zmodMixin.

Lemma sum_ffunE I (r : seq I) (P : pred I) (F : I -> {ffun aT -> rT}) :
  \big[+%R/0]_(i <- r | P i) F i = 
     [ffun x => \big[+%R/0]_(i <- r | P i) (F i x)].
Proof.
apply/ffunP=> j; rewrite ffunE.
by elim/big_rec2: _ => // [|i x f _ <-]; rewrite !ffunE.
Qed.

Lemma ffunMn f n x : (f *+ n) x = f x *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mulrS ffunE ?IHn. Qed.

End FinFunZmod.

Section FinFunRing.

(* As rings require 1 != 0 in order to lift a ring structure over finfuns     *)
(* we need evidence that the domain is non-empty.                             *)

Variable (aT : finType) (R : ringType) (a : aT).

Definition ffun_one : {ffun aT -> R} := [ffun => 1].
Definition ffun_mul (f g : {ffun aT -> R}) := [ffun x => f x * g x]. 

Fact ffun_mulA : associative ffun_mul.
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrA. Qed.
Fact ffun_mul_1l : left_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mul1r. Qed.
Fact ffun_mul_1r : right_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mulr1. Qed.
Fact ffun_mul_addl :  left_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulr_addl. Qed.
Fact ffun_mul_addr :  right_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulr_addr. Qed.
Fact ffun1_nonzero : ffun_one != 0.
Proof. by apply/eqP => /ffunP/(_ a)/eqP; rewrite !ffunE oner_eq0. Qed.

Definition ffun_ringMixin :=
  RingMixin ffun_mulA ffun_mul_1l ffun_mul_1r ffun_mul_addl ffun_mul_addr
            ffun1_nonzero.
Definition ffun_ringType :=
  Eval hnf in RingType {ffun aT -> R} ffun_ringMixin.

End FinFunRing.

Section FinFunComRing.

Variable (aT : finType) (R : comRingType) (a : aT).

Fact ffun_mulC : commutative (@ffun_mul aT R).
Proof. by move=> f1 f2; apply/ffunP=> i; rewrite !ffunE mulrC. Qed.

Definition ffun_comRingType :=
  Eval hnf in ComRingType (ffun_ringType R a) ffun_mulC.

End FinFunComRing.

Section FinFunLmod.

Variable (R : ringType) (aT : finType) (rT : lmodType R).

Implicit Types f g : {ffun aT -> rT}.

Definition ffun_scale k f := [ffun a => k *: f a].

Fact ffun_scaleA k1 k2 f : 
  ffun_scale k1 (ffun_scale k2 f) = ffun_scale (k1 * k2) f.
Proof. by apply/ffunP=> a; rewrite !ffunE scalerA. Qed.
Fact ffun_scale1 : left_id 1 ffun_scale.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE scale1r. Qed.
Fact ffun_scale_addr k : {morph (ffun_scale k) : x y / x + y}.
Proof. by move=> f g; apply/ffunP=> a; rewrite !ffunE scaler_addr. Qed.
Fact ffun_scale_addl u : {morph (ffun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k1 k2; apply/ffunP=> a; rewrite !ffunE scaler_addl. Qed.

Definition ffun_lmodMixin := 
  LmodMixin ffun_scaleA ffun_scale1 ffun_scale_addr ffun_scale_addl.
Canonical ffun_lmodType :=
  Eval hnf in LmodType R {ffun aT -> rT} ffun_lmodMixin.

End FinFunLmod.

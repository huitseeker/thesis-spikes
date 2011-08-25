(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype.

(******************************************************************************)
(* This file develops the theory of finite graphs represented by an "edge"    *)
(* relation over a finType T; this mainly amounts to the theory of the        *)
(* transitive closure of such relations.                                      *)
(*   For e : rel T and f : T -> T we define:                                  *)
(* dfs e n a x    == the list of points traversed by a depth-first search of  *)
(*                   the graph of e, at depth n, starting from x, and         *)
(*                   prepended to a.                                          *)
(* connect e      == the transitive closure of e (computed by dfs).           *)
(* connect_sym e  <=> connect e is symmetric, hence an equivalence relation.  *)
(* root e x       == pick a representative of connect e x, the component of   *)
(*                   x in the transitive closure of e.                        *)
(* roots e        == the codomain predicate of root e.                        *)
(* n_comp e       == number of components of connect e, i.e., the number of   *)
(*                   equivalence classes of connect e if connect_sym e holds. *)
(* closed e a     == the predicate a is e-invariant.                          *)
(* closure e a    == closure under e of a (the image of a under connect e).   *)
(* rel_adjunction h e e' a <=> in the e-closed domain a, h is the left part   *)
(*                   of an adjunction from e to another relation e'.          *)
(* fconnect f     == connect (frel f), i.e., "connected under f iteration".   *)
(* froot f x      == root (frel f) x, the root of the orbit of x under f.     *)
(* froots f       == roots (frel f) == orbit representatives for f.           *)
(* orbit f x      == lists the f orbit of x.                                  *)
(* findex f x y   == index of y in the f-orbit of x.                          *)
(* order f x      == size (cardinal) of the orbit of x under f.               *)
(* order_set f n  == elements of f-order n.                                   *)
(* finv f         == the inverse of f, if f is a permutation; specifically,   *)
(*                   finv f x := iter (order x).-1 f x.                       *)
(* fcard f        == number of orbits of f.                                   *)
(* fclosed f a    == closed under iteration of f.                             *)
(* fclosure f a   == closure under f iteration .                              *)
(* fun_adjunction == rel_adjunction (frel f).                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Decidable connectivity in finite types.                                  *)

Section Connect.

Variables (T : finType) (e : rel T).

Fixpoint dfs (n : nat) (a : seq T) (x : T) {struct n} :=
  if n is n'.+1 then
    if x \in a then a else foldl (dfs n') (x :: a) (enum (e x))
  else a.

Definition connect : rel T := fun x y => y \in dfs #|T| [::] x.

Lemma subset_dfs : forall n (a b : seq T), a \subset foldl (dfs n) a b.
Proof.
elim=> [|n IHn] a b; first by elim: b => /=.
elim: b a => [|x b IHb] a //=; apply: subset_trans (IHb _) => /=.
case: (x \in a) => //=; apply: subset_trans (IHn _ _).
apply/subsetP=> y ay; exact: mem_behead.
Qed.

Inductive dfs_path x y (a : seq T) : Prop :=
  DfsPath p of path e x p & y = last x p & [disjoint x :: p & a].

Lemma dfsP : forall n x y (a : seq T),
  #|T| <= #|a| + n -> y \notin a -> reflect (dfs_path x y a) (y \in dfs n a x).
Proof.
elim=> [|n IHn] x y a Hn Hy /=.
  case/idPn: (max_card (predU1 y (mem a))) => /=.
  by rewrite -ltnNge cardU1 /= (negPf Hy) /= addSn addnC.
case Hx: (x \in a).
  rewrite (negPf Hy); right=> [] [p Hp Ep Hpa].
  by rewrite disjoint_has /= Hx in Hpa.
move Da': (x :: a) => a'; case Hya': (y \in a').
  rewrite (subsetP (subset_dfs n _ _) _ Hya'); left.
  exists (Nil T); repeat split; last by rewrite disjoint_has /= Hx.
  by rewrite -Da' in_cons in Hya'; case/predU1P: Hya' Hy => //= ->.
have Hna': #|T| <= #|a'| + n by rewrite -Da' /= cardU1 Hx /= add1n addSnnS.
move Db: (enum _) => b.
suffices IHb:  reflect (exists2 x', x' \in b & dfs_path x' y a')
                       (y \in foldl (dfs n) a' b).
- apply: {IHn IHb}(iffP IHb) => [[x' Hx' [p Hp Ep Hpa]] | [p Hp Ep Hpa]].
    rewrite -Da' /= disjoint_sym disjointU1 in Hpa.
    move/andP: Hpa => [Hpx Hpa].
    exists (x' :: p); try by rewrite //= disjointU1 Hx disjoint_sym.
    by rewrite -Db mem_enum in Hx'; rewrite /= [_ x']Hx'.
  move/shortenP: Hp Ep => /= [[|y' p']] /= Hp' Up' Hp'p Dy.
    by rewrite -Da' Dy /= mem_head in Hya'.
  move/andP: Hp' => [Hxy' Hp']; move/andP: Up' => [Hp'x' _].
  exists y'; [ by rewrite -Db mem_enum | exists p'; auto ].
  rewrite disjoint_sym -Da' /= disjoint_cons Hp'x' /= disjoint_sym.
  apply: disjoint_trans Hpa; apply/subsetP=> z ?; apply: predU1r; exact: Hp'p.
elim: b a' Hya' Hna' {a x Da' Db Hy Hn Hx} => [|x b IHb] a Hy Hn /=.
  by rewrite Hy; right; case.
have Ha := subset_dfs n a [ :: x ]; simpl in Ha.
case Hdfs_y: (y \in dfs n a x).
  rewrite (subsetP (subset_dfs n _ b) _ Hdfs_y); left.
  exists x; [ exact: mem_head | apply: (IHn _); auto; exact (negbT Hy) ].
have Hca := subset_leq_card Ha; rewrite -(leq_add2r n) in Hca.
apply: {IHb Hca}(iffP (IHb _ Hdfs_y (leq_trans Hn Hca))).
  move=> [x' Hx' [p Hp Ep Hpa]]; rewrite disjoint_sym in Hpa.
  exists x'; [ exact: predU1r | exists p => // ].
  rewrite disjoint_sym; exact (disjoint_trans Ha Hpa).
move=> [x' Hx' [p Hp Ep Hpa]].
case Hpa': [disjoint x' :: p & dfs n a x].
  case/orP: Hx' => [Dx'|Hx']; last by exists x'; auto; exists p.
  move: (pred0P Hpa x'); rewrite /= mem_head /= => Hax'.
  case/idP: (pred0P Hpa' x'); rewrite /= mem_head //=.
  apply/(IHn _ _ _ Hn (negbT Hax')).
  exists (Nil T)=> //; first by move/eqP: Dx'.
  by rewrite disjoint_has /= -(eqP Dx') Hax'.
case/(IHn _ _ _ Hn (negbT Hy)): Hdfs_y.
case/pred0Pn: Hpa' => [x'' H]; case/andP: H => [ /= Hpx'' Hdfs_x''].
have Hax'' := pred0P Hpa x''; rewrite /= Hpx'' in Hax''.
case/(IHn _ _ _ Hn (negbT Hax'')): Hdfs_x'' => [q Hq Eq Hqa].
case/splitPl: {p}Hpx'' Hp Ep Hpa => [p1 p2 Ep1].
rewrite path_cat -cat_cons disjoint_cat last_cat Ep1.
move/andP=> [Hp1 Hp2] Ep2; case/andP=> [Hp1a Hp2a]; exists (cat q p2).
- by rewrite path_cat Hq -Eq.
- by rewrite last_cat -Eq.
by rewrite -cat_cons disjoint_cat Hqa.
Qed.

Lemma connectP : forall x y,
  reflect (exists2 p, path e x p & y = last x p) (connect x y).
Proof.
move=> x y; apply: (iffP (@dfsP _ x _ nil _ _)) => // [|[p]|[p]].
- by rewrite card0 leqnn.
- by exists p.
by exists p; rewrite // disjoint_sym disjoint_has.
Qed.

Lemma connect_trans : forall x1 x2 x3,
  connect x1 x2 -> connect x2 x3 -> connect x1 x3.
Proof.
move=> x1 x2 x3; move/connectP=> [p1 Hp1 ->]; move/connectP=> [p2 Hp2 ->].
by apply/connectP; exists (p1 ++ p2); rewrite ?path_cat ?Hp1 ?last_cat.
Qed.

Lemma connect0 : forall x, connect x x.
Proof. by move=> x; apply/connectP; exists (Nil T). Qed.

Lemma eq_connect0 : forall x y : T, x = y -> connect x y.
Proof. move=> x y ->; exact: connect0. Qed.

Lemma connect1 : forall x y, e x y -> connect x y.
Proof. by move=> x y Hxy; apply/connectP; exists [:: y]; rewrite /= ?Hxy. Qed.

Lemma path_connect : forall x p, path e x p ->
  subpred (mem (x :: p)) (connect x).
Proof.
move=> x p Hp x' Hx'; apply/connectP; case/splitPl: p / Hx' Hp => [p p' Ep].
by rewrite path_cat; case/andP; exists p.
Qed.

Definition root x := if pick (connect x) is Some y then y else x.

Definition roots : pred T := fun x => root x == x.

Definition n_comp a := #|predI roots a|.

Lemma connect_root : forall x, connect x (root x).
Proof.
by move=> x; rewrite /root; case: (pickP (connect x)); rewrite // connect0.
Qed.

Definition connect_sym := forall x y, connect x y = connect y x.

Lemma same_connect : connect_sym -> forall x y,
  connect x y -> connect x =1 connect y.
Proof.
by move=> He x y Hxy z; apply/idP/idP; apply: connect_trans; rewrite // He.
Qed.

Lemma same_connect_r : connect_sym -> forall x y,
  connect x y -> forall z, connect z x = connect z y.
Proof. move=> He x y Hxy z; rewrite !(He z); exact: same_connect. Qed.

Lemma rootP : forall x y,
  connect_sym -> reflect (root x = root y) (connect x y).
Proof.
move=> x y He; apply introP=> [Hxy|Hxy Hr].
  rewrite /root -(eq_pick (same_connect He Hxy)).
  by case: (pickP (connect x)) => [H|Hx] //; case/idP: (Hx y).
case/negP: Hxy; apply: (connect_trans (connect_root x)).
rewrite Hr He; apply connect_root.
Qed.

Lemma root_root : connect_sym -> forall x, root (root x) = root x.
Proof. move=> He x; symmetry; apply/(rootP _ _ He); exact: connect_root. Qed.

Lemma roots_root : connect_sym -> forall x, roots (root x).
Proof. move=> *; apply/eqP; exact: root_root. Qed.

Lemma root_connect :
  connect_sym -> forall x y, (root x == root y) = connect x y.
Proof. move=> He *; exact: sameP eqP (rootP _ _ He). Qed.

End Connect.

Prenex Implicits connect root roots n_comp.

Implicit Arguments connectP [T e x y].
Implicit Arguments rootP [T e x y].
Prenex Implicits connectP rootP.

Notation fconnect f := (connect (frel f)).
Notation froot f := (root (frel f)).
Notation froots f := (roots (frel f)).
Notation fcard f := (n_comp (frel f)).

Section EqConnect.

Variable T : finType.

Lemma connect_sub : forall e e' : rel T,
  subrel e (connect e') -> subrel (connect e) (connect e').
Proof.
move=> e e' He x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x => [_|/=]; first exact: connect0.
move/andP=> [Hx Hp]; exact (connect_trans (He _ _ Hx) (Hrec _ Hp)).
Qed.

Lemma relU_sym : forall e e' : rel T,
  connect_sym e -> connect_sym e' -> connect_sym (relU e e').
Proof.
move=> e e' He He'.
suff Hsub: forall x y, connect (relU e e') x y -> connect (relU e e') y x.
  move=> x y; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
case/andP=> [Hxp Hp]; apply: {Hrec Hp}(connect_trans (Hrec _ Hp)).
case/orP: Hxp; move/(@connect1 T); rewrite 1?He 1?He';
 apply: connect_sub y x => [x y Hy]; apply connect1; apply/orP; auto.
Qed.

Lemma eq_connect : forall e e' : rel T, e =2 e' -> connect e =2 connect e'.
Proof.
by move=> e e' Ee x y; apply/connectP/connectP=> [] [p Hp Ep]; exists p;
  move: Hp; rewrite // (eq_path Ee).
Qed.

Lemma eq_n_comp : forall e e' : rel T,
  connect e =2 connect e' -> n_comp e =1 n_comp e'.
Proof.
move=> e e' Hee' a; apply: eq_card => x.
by rewrite !inE /= /roots /root /= (eq_pick (Hee' x)).
Qed.

Lemma eq_n_comp_r : forall a a' : pred T, a =1 a' ->
  forall e, n_comp e a = n_comp e a'.
Proof. by move=> a a' Ha e; apply: eq_card => x; rewrite inE /= Ha. Qed.

Lemma n_compC : forall a e, n_comp e T = n_comp e a + n_comp e (predC a).
Proof.
move=> a e; rewrite /n_comp; rewrite -(cardID a).
by congr (_ + _); apply: eq_card => x; rewrite !inE !andbT andbC.
Qed.

Lemma eq_root : forall e1 e2 : rel T, e1 =2 e2 -> root e1 =1 root e2.
Proof. by move=> e1 e2 He x; rewrite /root (eq_pick (eq_connect He x)). Qed.

Lemma eq_roots : forall e1 e2 : rel T, e1 =2 e2 -> roots e1 =1 roots e2.
Proof. by move=> e1 e2 He x; rewrite /roots (eq_root He). Qed.

End EqConnect.

Section Closure.

Variables (T : finType) (e : rel T).
Hypothesis He : connect_sym e.

Lemma same_connect_rev : connect e =2 connect (fun x y => e y x).
Proof.
suff Hrev: forall e',
    subrel (connect (fun x y : T => e' y x)) (fun x y => connect e' y x).
  move=> x y; rewrite He; apply/idP/idP => [Hyx|Hxy]; apply: Hrev; auto.
move=> e' x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hyx Hp]; exact (connect_trans (Hrec _ Hp) (connect1 Hyx)).
Qed.

Definition closed (a : pred T) := forall x y, e x y -> a x = a y.

Lemma intro_closed : forall a : pred T,
  (forall x y, e x y -> a x -> a y) -> closed a.
Proof.
move=> a Ha x y Hxy; apply/idP/idP; first by apply: Ha.
move/connectP: {Hxy}(etrans (He _ _) (connect1 Hxy)) => [p Hp ->].
by elim: p y Hp => [|z p Hrec] y //=; move/andP=> [Hxp Hp]; eauto.
Qed.

Lemma closed_connect : forall a, closed a ->
  forall x y, connect e x y -> a x = a y.
Proof.
move=> a Ha x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x //=; move/andP=> [Hxp Hp].
rewrite (Ha _ _ Hxp); auto.
Qed.

Lemma connect_closed : forall x, closed (connect e x).
Proof. by move=> x y z Hyz; apply (same_connect_r He); apply connect1. Qed.

Lemma predC_closed : forall a, closed a -> closed (predC a).
Proof. by move=> a Ha x y Hxy; rewrite /= (Ha x y Hxy). Qed.

Definition closure (a : pred T) : pred T :=
  fun x => ~~ [disjoint connect e x & a].

Lemma closure_closed : forall a, closed (closure a).
Proof.
move=> a; apply intro_closed; move=> x y Hxy.
by rewrite /closure (eq_disjoint (same_connect He (connect1 Hxy))).
Qed.

Lemma subset_closure : forall a : pred T, a \subset (closure a).
Proof.
move=> a; apply/subsetP => x Hx; apply/pred0Pn.
by exists x; rewrite /= -topredE /= connect0.
Qed.

Lemma n_comp_closure2 : forall x y,
  n_comp e (closure (pred2 x y)) = (~~ connect e x y).+1.
Proof.
move=> x y; rewrite -(root_connect He) -card2.
apply: eq_card => z; apply/idP/idP.
  case/andP=> Hrz; case/pred0Pn=> z'; case/andP=> Hzz' Hxyz'.
  rewrite -(eqP Hrz) (rootP He Hzz').
  by case: (orP Hxyz'); move/eqP=> Dz'; rewrite !inE /= Dz' /= eqxx ?orbT.
case/orP; move/eqP=> ->; rewrite /= -topredE /= (roots_root He);
  apply/existsP; [exists x | exists y];
  by rewrite /= -!topredE /= eqxx ?orbT He connect_root.
Qed.

Lemma n_comp_connect : forall x, n_comp e (connect e x) = 1.
Proof.
move=> x; rewrite -(card1 (root e x)); apply: eq_card => [y].
apply/andP/eqP => [[Hy Hxy]|->]; first by rewrite (rootP He Hxy) (eqP Hy).
by rewrite (roots_root He) connect_root.
Qed.

End Closure.

Notation fclosed f := (closed (frel f)).
Notation fclosure f := (closure (frel f)).

Prenex Implicits closed closure.

Section Orbit.

Variables (T : finType) (f : T -> T).

Definition order x := #|fconnect f x|.

Definition orbit x := traject f x (order x).

Definition findex x y := index y (orbit x).

Definition finv x := iter (order x).-1 f x.

Lemma fconnect_iter : forall n x, fconnect f x (iter n f x).
Proof.
move=> n x; apply/connectP.
by exists (traject f (f x) n); [ exact: fpath_traject | rewrite last_traject ].
Qed.

Lemma fconnect1 : forall x, fconnect f x (f x).
Proof. exact (fconnect_iter 1). Qed.

Lemma fconnect_finv : forall x, fconnect f x (finv x).
Proof. move=> x; apply: fconnect_iter. Qed.

Lemma orderSpred : forall x, (order x).-1.+1 = order x.
Proof. by move=> x; rewrite /order (cardD1 x) [_ x _]connect0. Qed.

Lemma size_orbit : forall x : T, size (orbit x) = order x.
Proof. move=> x; apply: size_traject. Qed.

Lemma looping_order : forall x, looping f x (order x).
Proof.
move=> x; apply/idPn => [Ux]; rewrite -looping_uniq in Ux.
case/idP: (ltnn (order x)).
have:= card_uniqP Ux; rewrite size_traject => <-.
apply: subset_leq_card; apply/subsetP=> z.
move/trajectP=> [i _ ->]; apply: fconnect_iter.
Qed.

Lemma fconnect_orbit : forall x, fconnect f x =i orbit x.
Proof.
move=> x y; symmetry; apply/idP/idP.
  move/trajectP=> [i _ ->]; apply: fconnect_iter.
move/connectP=> [q' Hq' ->]; move/fpathP: Hq' => [m ->] {q'}.
rewrite last_traject; apply: loopingP; apply looping_order.
Qed.

Lemma orbit_uniq : forall x, uniq (orbit x).
Proof.
move=> x; rewrite /orbit -orderSpred looping_uniq.
apply/trajectP => [[i Hi Ei]]; set n := (order x).-1; case/idP: (ltnn n).
rewrite {1}/n orderSpred /order -(size_traject f x n).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP=> z.
rewrite fconnect_orbit; case/trajectP=> j Hj ->{z}; apply/trajectP.
rewrite -orderSpred -/n ltnS leq_eqVlt in Hj.
by case/predU1P: Hj => [->|Hj]; [ exists i | exists j ].
Qed.

Lemma findex_max : forall x y, fconnect f x y -> findex x y < order x.
Proof. by move=> x y; rewrite [_ y]fconnect_orbit -index_mem size_orbit. Qed.

Lemma findex_iter : forall x i, i < order x -> findex x (iter i f x) = i.
Proof.
move=> x i Hi; rewrite -(nth_traject f Hi); rewrite -size_orbit in Hi.
exact (index_uniq x Hi (orbit_uniq x)).
Qed.

Lemma iter_findex : forall x y, fconnect f x y -> iter (findex x y) f x = y.
Proof.
move=> x y; rewrite [_ y]fconnect_orbit; move=> Hy.
have Hi := Hy; rewrite -index_mem size_orbit in Hi.
by rewrite -(nth_traject f Hi) -/(orbit x) nth_index.
Qed.

Lemma findex0 : forall x, findex x x = 0.
Proof. by move=> x; rewrite /findex /orbit -orderSpred /= eq_refl. Qed.

Lemma fconnect_invariant : forall (T' : eqType) (k : T -> T'),
  invariant f k =1 xpredT -> forall x y : T, fconnect f x y -> k x = k y.
Proof.
move=> T' k Hk x y; move/iter_findex=> <-; elim: {y}(findex x y) => //= n ->.
exact (esym (eqP (Hk _))).
Qed.

Section Loop.

Variable p : seq T.
Hypotheses (Hp : fcycle f p) (Up : uniq p).
Variable x : T.
Hypothesis Hx : x \in p.

(* The first lemma does not depend on Up : (uniq p) *)
Lemma fconnect_cycle : fconnect f x =i p.
Proof.
case/rot_to: Hx => [i q Dp] y; rewrite -(mem_rot i p) Dp.
have Hp' := Hp; rewrite -(cycle_rot i) {i}Dp (cycle_path x) /=  in Hp'.
case/andP: Hp'; move/eqP=> Eq Hq; apply/idP/idP; last exact: path_connect.
move/connectP=> [q' Hq' ->] {y}; case/fpathP: Hq' => [m ->] {q'}.
case/fpathP: Hq Eq => [n ->]; rewrite !last_traject -iterS; move=> Dx.
by apply: (@loopingP _ f x (n.+1) _ m); rewrite /looping Dx /= mem_head.
Qed.

Lemma order_cycle : order x = size p.
Proof. rewrite -(card_uniqP Up); exact (eq_card fconnect_cycle). Qed.

Lemma orbit_rot_cycle : {i : nat | orbit x = rot i p}.
Proof.
case/rot_to: Hx => [i q Dp]; exists i; rewrite (Dp).
have Hp' := Hp; rewrite -(cycle_rot i) (Dp) (cycle_path x) /= in Hp'.
case/andP: Hp' => _; move/fpathP=> [m Dq].
by rewrite /orbit order_cycle -(size_rot i) Dp /= Dq size_traject.
Qed.

End Loop.

Hypothesis Hf : injective f.

Lemma f_finv : cancel finv f.
Proof.
move=> x; move: (looping_order x) (orbit_uniq x).
rewrite /looping /orbit -orderSpred looping_uniq /= /looping.
set n := (order x).-1; case/predU1P; first by [].
move/trajectP=> [i Hi Dnx]; rewrite -iterSr iterS in Dnx.
by case/trajectP; exists i; last exact: Hf.
Qed.

Lemma finv_f : cancel f finv.
Proof. exact (inj_can_sym f_finv Hf). Qed.

Lemma fin_inj_bij : bijective f.
Proof. exists finv; [ exact finv_f | exact f_finv ]. Qed.

Lemma finv_bij : bijective finv.
Proof. exists f; [ exact f_finv | exact finv_f ]. Qed.

Lemma finv_inj : injective finv.
Proof. exact (can_inj f_finv). Qed.

Lemma fconnect_sym : forall x y, fconnect f x y = fconnect f y x.
Proof.
suff: forall x y, fconnect f x y -> fconnect f y x.
  move=> *; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp ->] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hx Hp]; rewrite -(finv_f x) (eqP Hx).
apply: (connect_trans _ (fconnect_finv _)); auto.
Qed.

Lemma iter_order : forall x, iter (order x) f x = x.
Proof. move=> x; rewrite -orderSpred iterS; exact (f_finv x). Qed.

Lemma iter_finv : forall n x, n <= order x ->
  iter n finv x = iter (order x - n) f x.
Proof.
move=> n x Hn; set m := order x - n.
rewrite -{1}[x]iter_order -(subnKC Hn) -/m iter_add.
move: {m x Hn}(iter m f x) => x.
by elim: n => // [n Hrec]; rewrite iterSr /= finv_f.
Qed.

Lemma cycle_orbit : forall x, fcycle f (orbit x).
Proof.
move=> x; rewrite /orbit -orderSpred (cycle_path x) /= last_traject -/(finv x).
by rewrite fpath_traject f_finv andbT /=.
Qed.

Lemma fpath_finv : forall x p,
  fpath finv x p = fpath f (last x p) (rev (belast x p)).
Proof.
move=> x p; elim: p x => [|y p Hrec] x //=.
rewrite rev_cons -cats1 path_cat -{}Hrec andbC /= eq_sym andbT.
bool_congr; rewrite -(inj_eq Hf) f_finv.
by case: p => [|z p] //=; rewrite rev_cons last_rcons.
Qed.

Lemma same_fconnect_finv : fconnect finv =2 fconnect f.
Proof.
move=> x y; rewrite (same_connect_rev fconnect_sym).
apply: {x y}eq_connect => x y.
by rewrite /= -(inj_eq Hf) f_finv eq_sym.
Qed.

Lemma fcard_finv : fcard finv =1 fcard f.
Proof. exact (eq_n_comp same_fconnect_finv). Qed.

Definition order_set n : pred T := fun x => order x == n.

Lemma order_div_card : forall n a,
    subpred a (order_set n) -> fclosed f a -> 0 < n ->
  forall m, (#|a| == n * m) = (fcard f a == m).
Proof.
move=> n a Han Ha Hn; rewrite /n_comp; set b : pred T := xpredI (froots f) a.
have Hb: forall x, b x -> froot f x = x /\ order x = n.
  move=> x; move/andP=> [Hrx Hax]; split; apply: eqP; rewrite //=.
  exact: (Han _ Hax).
have <-: #|preim (froot f) b| = #|a|.
  apply: eq_card => x; rewrite /b inE /= (roots_root fconnect_sym).
  by rewrite -(closed_connect Ha (connect_root _ x)).
elim: {a b}#|b| {1 3 4}b (eqxx #|b|) Hb {Ha Han} => [|m Hrec] b Em Hb.
  rewrite -(@eq_card _ pred0) => [m|x].
    by rewrite card0 !(eq_sym 0) muln_eq0 eqn0Ngt Hn.
  by rewrite !inE /= (pred0P Em).
case: (pickP b) => [x //= Hx|Hb0]; last by rewrite (eq_card Hb0) card0 in Em.
case: (Hb _ Hx) => [Dx Hex].
case=> [|m']; rewrite mulnC /=; first by rewrite (cardD1 x) inE /= Dx Hx.
rewrite (cardD1 x) [x \in b]Hx in Em; rewrite mulSn mulnC eqSS.
rewrite -{Hrec}(Hrec _ Em) => [|y]; last by case/andP; auto.
apply: etrans (congr1 (fun p => p == _) _) (eqn_addl _ _ _).
rewrite -(cardID (fconnect f x)); congr (_ + _).
  apply: etrans Hex; apply: eq_card => y; rewrite inE /= -!topredE /= andbC.
  case Hy: (fconnect f x y) => //=.
  by rewrite -(rootP fconnect_sym Hy) Dx.
apply: eq_card => y; rewrite !inE andbC.
by rewrite -{2}Dx (root_connect fconnect_sym) fconnect_sym andbC.
Qed.

Lemma fclosed1 : forall a, fclosed f a -> forall x, a x = a (f x).
Proof. move=> a Ha x; exact (Ha x _ (eq_refl _)). Qed.

Lemma same_fconnect1 : forall x, fconnect f x =1 fconnect f (f x).
Proof. move=> x; exact (same_connect fconnect_sym (fconnect1 x)). Qed.

Lemma same_fconnect1_r : forall x y, fconnect f x y = fconnect f x (f y).
Proof. by move=> x y; rewrite /= !(fconnect_sym x) -same_fconnect1. Qed.

End Orbit.

Prenex Implicits order orbit findex finv order_set.

Section FinCancel.

Variables (T : finType) (f f' : T -> T).
Hypothesis Ef : cancel f f'.

Let Hf := can_inj Ef.

Lemma finv_eq_can : finv f =1 f'.
Proof. exact (bij_can_eq (fin_inj_bij Hf) (finv_f Hf) Ef). Qed.

End FinCancel.

Section FconnectEq.

Variables (T : finType) (f f' : T -> T).
Hypothesis Eff' : f =1 f'.

Lemma eq_pred1 : frel f =2 frel f'.
Proof. move=> x y; rewrite /= Eff'; done. Qed.

Lemma eq_fpath : fpath f =2 fpath f'.
Proof. exact: eq_path eq_pred1. Qed.

Lemma eq_fconnect : fconnect f =2 fconnect f'.
Proof. exact: eq_connect eq_pred1. Qed.

Lemma eq_fcard : fcard f =1 fcard f'.
Proof. exact: eq_n_comp eq_fconnect. Qed.

Lemma eq_finv : finv f =1 finv f'.
Proof.
move=> x; rewrite /finv /order (eq_card (eq_fconnect x)).
exact: (eq_iter Eff').
Qed.

Lemma eq_froot : froot f =1 froot f'.
Proof. exact: eq_root eq_pred1. Qed.

Lemma eq_froots : froots f =1 froots f'.
Proof. exact: eq_roots eq_pred1. Qed.

Hypothesis Hf : injective f.

Lemma finv_inv : finv (finv f) =1 f.
Proof. exact (finv_eq_can (f_finv Hf)). Qed.

Lemma order_finv : order (finv f) =1 order f.
Proof. move=> x; exact (eq_card (same_fconnect_finv Hf x)). Qed.

Lemma order_set_finv : order_set (finv f) =2 order_set f.
Proof. by move=> n x; rewrite /order_set order_finv. Qed.

End FconnectEq.

Section RelAdjunction.

Variables (T T' : finType) (h : T' -> T) (e : rel T) (e' : rel T').
Hypotheses (He : connect_sym e) (He' : connect_sym e').

Variable a : pred T.
Hypothesis Ha : closed e a.

Record rel_adjunction : Type := RelAdjunction {
  rel_unit : forall x, a x -> {x' : T' | connect e x (h x')};
  rel_functor : forall x' y',
    a (h x') -> connect e' x' y' = connect e (h x') (h y')
}.

Lemma intro_adjunction : forall h' : (forall x, a x -> T'),
   (forall x Hx, connect e x (h (h' x Hx))
             /\ (forall y Hy, e x y -> connect e' (h' x Hx) (h' y Hy))) ->
   (forall x' Hx, connect e' x' (h' (h x') Hx)
             /\ (forall y', e' x' y' -> connect e (h x') (h y'))) ->
  rel_adjunction.
Proof.
move=> h' Hee' He'e; split.
  by move=> y Hy; exists (h' y Hy); case (Hee' _ Hy).
move=> x' z' Hx'; apply/idP/idP.
  move/connectP=> [p Hp ->] {z'}.
  elim: p x' Hp Hx' => [|y' p Hrec] x' /=; first by rewrite connect0.
  move/andP=> [Hx' Hp] Hx.
  move: (He'e _ Hx) => [_ H]; move/H: {H}Hx' => Hxp.
  apply: (connect_trans Hxp (Hrec _ Hp _)).
  by rewrite -(closed_connect Ha Hxp).
case: (He'e _ Hx') => [Hx'x'' _] Hxz; apply: (connect_trans Hx'x'').
move/connectP: Hxz Hx' {Hx'x''} => [p Hp Hpz].
elim: p {x'}(h x') Hp Hpz => [|y' p Hrec] x /=.
  by move=> _ <- Hz'; rewrite He'; case (He'e _ Hz').
move/andP=> [Hx' Hp] Dz' Hy.
move: (Hy) (Hee' _ Hy) => Hx [_ Hhxy]; rewrite (Ha Hx') in Hy.
apply: connect_trans (Hrec _ Hp Dz' Hy); auto.
Qed.

Lemma strict_adjunction :
    injective h -> a \subset codom h -> rel_base h e e' (predC a) ->
  rel_adjunction.
Proof.
move=> /= Hh Hha He'e.
apply intro_adjunction with (fun x Hx => iinv (subsetP Hha x Hx)).
  move=> x Hx; split; first by rewrite f_iinv; apply connect0.
  by move=> y Hy //= Hxy; apply connect1; rewrite -He'e !f_iinv ?Hx //= negbK.
move=> x' Hx'; split; first by rewrite (iinv_f _ Hh); apply connect0.
by move=> y' //= Hx'y'; apply connect1; rewrite He'e ?Hx' //= negbK.
Qed.

Lemma adjunction_closed : rel_adjunction -> closed e' (preim h a).
Proof.
move=> [Hu He'e]; apply (intro_closed He').
move=> x' y'; move/(@connect1 T')=> Hx'y' Hx'.
by rewrite He'e // in Hx'y'; rewrite /preim /= -(closed_connect Ha Hx'y').
Qed.

Lemma adjunction_n_comp : rel_adjunction -> n_comp e a = n_comp e' (preim h a).
Proof.
move=> [Hu He'e]; have Hac := closed_connect Ha.
have inj_h: {in predI (roots e') (preim h a) &, injective (root e \o h)}.
  move=> x' y'; case/andP; move/eqP=> rx' /= ax'; case/andP; move/eqP=> ry' _.
  by move/(rootP He); rewrite -He'e //; move/(rootP He'); rewrite rx' ry'.
rewrite /n_comp -(card_in_image inj_h); apply: eq_card => x.
apply/andP/imageP=> [[] | [x']]; last first.
  case/andP; move/eqP=> rx' /= ax' ->.
  by rewrite -(Hac _ _ (connect_root _ _)) roots_root.
move/eqP=> rx ax; have [y' x_y']:= Hu x ax; pose x' := root e' y'.
have ay': a (h y') by rewrite -(Hac _ _ x_y').
have x'_y': connect e (h y') (h x') by rewrite -He'e ?connect_root.
exists x'; first by rewrite /= !inE -(Hac _ _ x'_y') ?roots_root.
rewrite -rx; apply/(rootP He); exact: connect_trans x'_y'.
Qed.

End RelAdjunction.

Definition fun_adjunction T T' h f f' :=
  @rel_adjunction T T' h (frel f) (frel f').

Implicit Arguments intro_adjunction [T T' h e e' a].
Implicit Arguments adjunction_n_comp [T T' e e' a].

Unset Implicit Arguments.


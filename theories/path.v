(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(*    The basic theory of paths over an eqType; this file is essentially a    *)
(* complement to seq.v. Paths are non-empty sequences that obey a progression *)
(* relation. They are passed around in three parts: the head and tail of the  *)
(* sequence, and a proof of (boolean) predicate asserting the progression.    *)
(* This "exploded" view is rarely embarrassing, as the first two parameters   *)
(* are usually inferred from the type of the third; on the contrary, it saves *)
(* the hassle of constantly constructing and destructing a dependent record.  *)
(*    We define similarly cycles, for which we allow the empty sequence,      *)
(* which represents a non-rooted empty cycle; by contrast, the "empty" path   *)
(* from a point x is the one-item sequence containing only x.                 *)
(*   We allow duplicates; uniqueness, if desired (as is the case for several  *)
(* geometric constructions), must be asserted separately. We do provide       *)
(* shorthand, but only for cycles, because the equational properties of       *)
(* "path" and "uniq" are unfortunately  incompatible (esp. wrt "cat").        *)
(*    We define notations for the common cases of function paths, where the   *)
(* progress relation is actually a function. In detail:                       *)
(*   path e x p == x :: p is an e-path [:: x_0; x_1; ... ; x_n], i.e., we     *)
(*                 e x_i x_{i+1} for all i < n. The path x :: p starts at x   *)
(*                 and ends at last x p.                                      *)
(*  fpath f x p == x :: p is an f-path, where f is a function, i.e., p is of  *)
(*                 the form [:: f x; f (f x); ...]. This is just a notation   *)
(*                 for path (frel f) x p.                                     *)
(*   sorted e s == s is an e-sorted sequence: either s = [::], or s = x :: p  *)
(*                 is an e-path (this is oten used with e = leq or ltn).      *)
(*    cycle e c == c is an e-cycle: either c = [::], or c = x :: p with       *)
(*                 x :: (rcons p x) an e-path.                                *)
(*   fcycle f c == c is an f-cycle, for a function f.                         *)
(* traject f x n == the f-path of size n starting at x                        *)
(*              := [:: x; f x; ...; iter n.-1 f x]                            *)
(* looping f x n == the f-paths of size greater than n starting at x loop     *)
(*                 back, or, equivalently, traject f x n contains all         *)
(*                 iterates of f at x.                                        *)
(* merge e s1 s2 == the e-sorted merge of sequences s1 and s2: this is always *)
(*                 a permutation of s1 ++ s2, and is e-sorted when s1 and s2  *)
(*                 are and e is total.                                        *)
(*     sort e s == a permutation of the sequence s, that is e-sorted when e   *)
(*                 is total (computed by a merge sort with the merge function *)
(*                 above).                                                    *)
(*   mem2 s x y == x, then y occur in the sequence (path) s; this is          *)
(*                 non-strict: mem2 s x x = (x \in s).                        *)
(*     next c x == the successor of the first occurrence of x in the sequence *)
(*                 c (viewed as a cycle), or x if x \notin c.                 *)
(*     prev c x == the predecessor of the first occurrence of x in the        *)
(*                 sequence c (viewed as a cycle), or x if x \notin c.        *)
(*    arc c x y == the sub-arc of the sequece c (viewed as a cycle) starting  *)
(*                 at the first occurrence of x in c, and ending just before  *)
(*                 the next ocurrence of y (in cycle order); arc c x y        *)
(*                 returns an unspecified sub-arc of c if x and y do not both *)
(*                 occur in c.                                                *)
(*  ucycle e c <-> ucycleb e c (ucycle e c is a Coercion target of type Prop) *)
(* ufcycle f c <-> c is a simple f-cycle, for a function f.                   *)
(*  shorten x p == the tail a duplicate-free subpath of x :: p with the same  *)
(*                 endpoints (x and last x p), obtained by removing all loops *)
(*                 from x :: p.                                               *)
(* rel_base e e' h b <-> the function h is a functor from relation e to       *)
(*                 relation e', EXCEPT at points whose image under h satisfy  *)
(*                 the "base" predicate b:                                    *)
(*                    e' (h x) (h y) = e x y UNLESS b (h x) holds             *)
(*                 This is the statement of the side condition of the path    *)
(*                 functorial mapping lemma path_map.                         *)
(* fun_base f f' h b <-> the function h is a functor from function f to f',   *)
(*                 except at the preimage of predicate b under h.             *)
(* We also provide three segmenting dependently-typed lemmas (splitP, splitPl *)
(* and splitPr) whose elimination split a path x0 :: p at an internal point x *)
(* as follows:                                                                *)
(*  - splitP applies when x \in p; it replaces p with (rcons p1 x ++ p2), so  *)
(*    that x appears explicitly at the end of the left part. The elimination  *)
(*    of splitP will also simultaneously replace take (index x p) with p1 and *)
(*    drop (index x p).+1 p with p2.                                          *)
(*  - splitPl applies when x \in x0 :: p; it replaces p with p1 ++ p2 and     *)
(*    simulaneously generates an equation x = last x0 p.                      *)
(*  - splitPr applies when x \in p; it replaces p with (p1 ++ x :: p2), so x  *)
(*    appears explicitly at the start of the right part.                      *)
(* The parts p1 and p2 are computed using index/take/drop in all cases, but   *)
(* only splitP attemps to subsitute the explicit values. The substitution of  *)
(* p can be deferred using the dependent equation generation feature of       *)
(* ssreflect, e.g.: case/splitPr def_p: {1}p / x_in_p => [p1 p2] generates    *)
(* the equation p = p1 ++ p2 instead of performing the substitution outright. *)
(*   Similarly, eliminating the loop removal lemma shortenP simultaneously    *)
(* replaces shorten e x p with a fresh constant p', and last x p with         *)
(* last x p'.                                                                 *)
(*   Note that although all "path" functions actually operate on the          *)
(* underlying sequence, we provide a series of lemmas that define their       *)
(* interaction with thepath and cycle predicates, e.g., the path_cat equation *)
(* can be used to split the path predicate after splitting the underlying     *)
(* sequence.                                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Paths.

Variables (n0 : nat) (T : Type).

Section Path.

Variables (x0_cycle : T) (e : rel T).

Fixpoint path x (p : seq T) {struct p} :=
  if p is y :: p' then e x y && path y p' else true.

Lemma path_cat : forall x p1 p2,
  path x (p1 ++ p2) = path x p1 && path (last x p1) p2.
Proof.
by move=> x p1 p2; elim: p1 x => [|y p1 Hrec] x //=; rewrite Hrec -!andbA.
Qed.

Lemma path_rcons : forall x p y,
  path x (rcons p y) = path x p && e (last x p) y.
Proof. by move=> x p y; rewrite -cats1 path_cat /= andbT. Qed.

Lemma pathP : forall x p x0,
  reflect (forall i, i < size p -> e (nth x0 (x :: p) i) (nth x0 p i))
          (path x p).
Proof.
move=> x p x0; elim: p x => [|y p Hrec] x /=; first by left.
apply: (iffP andP) => [[Hxy Hp]|Hp].
  move=> [|i] Hi //; exact: Hrec _ Hp i Hi.
split; first exact: Hp 0 (leq0n (size p)).
apply/(Hrec y) => i; exact: Hp i.+1.
Qed.

Definition cycle p := if p is x :: p' then path x (rcons p' x) else true.

Lemma cycle_path : forall p, cycle p = path (last x0_cycle p) p.
Proof. by move=> [|x p] //=; rewrite path_rcons andbC. Qed.

Lemma cycle_rot : forall p, cycle (rot n0 p) = cycle p.
Proof.
case: (n0) => [|n] [|y0 p] //=; first by rewrite /rot /= cats0.
rewrite /rot /= -{3}(cat_take_drop n p) -cats1 -catA path_cat.
case: (drop n p) => [|z0 q]; rewrite /= -cats1 !path_cat /= !andbT andbC //.
by rewrite last_cat; repeat bool_congr.
Qed.

Lemma cycle_rotr : forall p, cycle (rotr n0 p) = cycle p.
Proof. by move=> p; rewrite -cycle_rot rotrK. Qed.

End Path.

Lemma eq_path : forall e e', e =2 e' -> path e =2 path e'.
Proof.
by move=> e e' Ee x p; elim: p x => [|y p Hrec] x //=; rewrite Ee Hrec.
Qed.

Lemma sub_path : forall e e', subrel e e' ->
  forall x p, path e x p -> path e' x p.
Proof.
move=> e e' He x p; elim: p x => [|y p Hrec] x //=.
by move/andP=> [Hx Hp]; rewrite (He _ _ Hx) (Hrec _ Hp).
Qed.

Lemma path_rev : forall e x p,
  path e (last x p) (rev (belast x p)) = path (fun z y => e y z) x p.
Proof.
move=> e x p; elim: p x => //= y p IHp x.
rewrite rev_cons path_rcons -IHp andbC.
by rewrite -(last_cons x) -rev_rcons -lastI rev_cons last_rcons.
Qed.

End Paths.

Implicit Arguments pathP [T e x p].
Prenex Implicits pathP.

Section EqPath.

Variables (n0 : nat) (T : eqType) (x0_cycle : T) (e : rel T).

CoInductive split x : seq T -> seq T -> seq T -> Type :=
  Split p1 p2 : split x (rcons p1 x ++ p2) p1 p2.

Lemma splitP : forall (p : seq T) x, x \in p ->
   let i := index x p in split x p (take i p) (drop i.+1 p).
Proof.
move=> p x Hx i; have := esym (cat_take_drop i p).
have Hi := Hx; rewrite -index_mem -/i in Hi; rewrite (drop_nth x Hi).
by rewrite -cat_rcons {2}/i (nth_index x Hx) => Dp; rewrite {1}Dp.
Qed.

CoInductive splitl (x1 x : T) : seq T -> Type :=
  Splitl p1 p2 of last x1 p1 = x : splitl x1 x (p1 ++ p2).

Lemma splitPl : forall x1 p x, x \in x1 :: p -> splitl x1 x p.
Proof.
move=> x1 p x; rewrite in_cons.
case: eqP => [->| _]; first by rewrite -(cat0s p).
case/splitP; split; exact: last_rcons.
Qed.

CoInductive splitr x : seq T -> Type :=
  Splitr p1 p2 : splitr x (p1 ++ x :: p2).

Lemma splitPr : forall (p : seq T) x, x \in p -> splitr x p.
Proof. by move=> p x; case/splitP=> p1 p2; rewrite cat_rcons. Qed.

Fixpoint next_at (x y0 y : T) (p : seq T) {struct p} :=
  match p with
  | [::] => if x == y then y0 else x
  | y' :: p' => if x == y then y' else next_at x y0 y' p'
  end.

Definition next p x := if p is y :: p' then next_at x y y p' else x.

Fixpoint prev_at (x y0 y : T) (p : seq T) {struct p} :=
  match p with
  | [::]     => if x == y0 then y else x
  | y' :: p' => if x == y' then y else prev_at x y0 y' p'
  end.

Definition prev p x := if p is y :: p' then prev_at x y y p' else x.

Lemma next_nth : forall p x,
  next p x = if x \in p then
               if p is y :: p' then nth y p' (index x p) else x
             else x.
Proof.
move=> [|y0 p] x //=; elim: p {2 3 5}y0 => [|y' p Hrec] y /=;
  by rewrite (eq_sym y) in_cons; case (x == y); try exact: Hrec.
Qed.

Lemma prev_nth : forall p x,
  prev p x = if x \in p then
               if p is y :: p' then nth y p (index x p') else x
             else x.
Proof.
move=> [|y0 p] x //=; rewrite in_cons orbC.
elim: p {2 5}y0 => [|y' p Hrec] y; rewrite /= ?in_cons // (eq_sym y').
by case (x == y') => /=; auto.
Qed.

Lemma mem_next : forall (p : seq T) x, (next p x \in p) = (x \in p).
Proof.
move=> p x; rewrite next_nth; case Hpx: (x \in p) => //.
case: p (index x p) Hpx => [|y0 p'] //= i _; rewrite in_cons.
case: (ltnP i (size p')) => Hi; first by rewrite /= (mem_nth y0 Hi) orbT.
by rewrite (nth_default y0 Hi) eqxx.
Qed.

Lemma mem_prev : forall (p : seq T) x, (prev p x \in p) = (x \in p).
Proof.
move=> p x; rewrite prev_nth; case Hpx: (x \in p) => //.
case: p Hpx => [|y0 p'] Hpx //.
by apply mem_nth; rewrite /= ltnS index_size.
Qed.

(* ucycleb is the boolean predicate, but ucycle is defined as a Prop *)
(* so that it can be used as a coercion target. *)
Definition ucycleb p := cycle e p && uniq p.
Definition ucycle p : Prop := cycle e p && uniq p.

(* Projections, used for creating local lemmas. *)
Lemma ucycle_cycle : forall p, ucycle p -> cycle e p.
Proof. by move=> p; case/andP. Qed.

Lemma ucycle_uniq : forall p, ucycle p -> uniq p.
Proof. by move=> p; case/andP. Qed.

Lemma next_cycle : forall p x, cycle e p -> x \in p -> e x (next p x).
Proof.
move=> [|y0 p] //= x.
elim: p {1 3 5}y0 => [|y' p Hrec] y /=; rewrite in_cons.
  by rewrite andbT orbF => Hy Dy; rewrite Dy (eqP Dy).
move/andP=> [Hy Hp]; case: (x =P y) => [->|_] //; exact: Hrec.
Qed.

Lemma prev_cycle : forall p x, cycle e p -> x \in p -> e (prev p x) x.
Proof.
move=> [|y0 p] //= x; rewrite in_cons orbC.
elim: p {1 5}y0 => [|y' p Hrec] y /=; rewrite ?in_cons.
  by rewrite andbT=> Hy Dy; rewrite Dy (eqP Dy).
move/andP=> [Hy Hp]; case: (x =P y') => [->|_] //; exact: Hrec.
Qed.

Lemma ucycle_rot : forall p, ucycle (rot n0 p) = ucycle p.
Proof. by move=> *; rewrite /ucycle rot_uniq cycle_rot. Qed.

Lemma ucycle_rotr : forall p, ucycle (rotr n0 p) = ucycle p.
Proof. by move=> *; rewrite /ucycle rotr_uniq cycle_rotr. Qed.

(* The "appears no later" partial preorder defined by a path. *)

Definition mem2 (p : seq T) x y := y \in drop (index x p) p.

Lemma mem2l : forall p x y, mem2 p x y -> x \in p.
Proof.
move=> p x y; rewrite /mem2 -!index_mem size_drop; move=> Hxy.
by rewrite -subn_gt0 -(ltn_predK Hxy) ltnS leq0n.
Qed.

Lemma mem2lf : forall (p : seq T) x,
  (x \in p) = false -> forall y, mem2 p x y = false.
Proof. move=> p x Hx y; apply/idP => Hp; case/idP: Hx; apply: mem2l Hp. Qed.

Lemma mem2r : forall p x y, mem2 p x y -> y \in p.
Proof.
rewrite /mem2; move=> p x y Hxy.
by rewrite -(cat_take_drop (index x p) p) mem_cat Hxy orbT.
Qed.

Lemma mem2rf : forall (p : seq T) y,
  (y \in p) = false -> forall x, mem2 p x y = false.
Proof. move=> p y Hy x; apply/idP => [Hp]; case/idP: Hy; apply: mem2r Hp. Qed.

Lemma mem2_cat : forall p1 p2 x y,
  mem2 (p1 ++ p2) x y = mem2 p1 x y || mem2 p2 x y || (x \in p1) && (y \in p2).
Proof.
move=> p1 p2 x y; rewrite {1}/mem2 index_cat drop_cat; case Hp1x: (x \in p1).
  rewrite index_mem Hp1x mem_cat /= -orbA.
  by case Hp2: (y \in p2); [ rewrite !orbT // | rewrite (mem2rf Hp2) ].
by rewrite ltnNge leq_addr /= orbF addKn (mem2lf Hp1x).
Qed.

Lemma mem2_splice : forall p1 p3 x y p2,
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ p2 ++ p3) x y.
Proof.
move=> p1 p3 x y p2 Hxy; move: Hxy; rewrite !mem2_cat mem_cat.
case: (mem2 p1 x y) (mem2 p3 x y) => [|] // [|] /=; first by rewrite orbT.
by case: (x \in p1) => [|] //= Hy; rewrite Hy !orbT.
Qed.

Lemma mem2_splice1 : forall p1 p3 x y z,
  mem2 (p1 ++ p3) x y -> mem2 (p1 ++ z :: p3) x y.
Proof. move=> p1 p3 x y z; exact: (mem2_splice [::z]). Qed.

Lemma mem2_cons : forall x p y,
  mem2 (x :: p) y =1 if x == y then predU1 x (mem p) : pred T else mem2 p y.
Proof. by move=> x p y z; rewrite {1}/mem2 /=; case (x == y). Qed.

Lemma mem2_last : forall y0 p x,
  mem2 (y0 :: p) x (last y0 p) = (x \in y0 :: p).
Proof.
move=> y0 p x; apply/idP/idP; first by apply mem2l.
rewrite -index_mem /mem2; move: (index x _) => i Hi.
by rewrite lastI drop_rcons ?size_belast // mem_rcons mem_head.
Qed.

Lemma mem2l_cat : forall (p1 : seq T) x, (x \in p1) = false ->
  forall p2, mem2 (p1 ++ p2) x =1 mem2 p2 x.
Proof. by move=> p1 x Hx p2 y; rewrite mem2_cat (Hx) (mem2lf Hx) /= orbF. Qed.

Lemma mem2r_cat : forall (p2 : seq T) y, (y \in p2) = false ->
   forall p1 x, mem2 (p1 ++ p2) x y = mem2 p1 x y.
Proof.
by move=> p2 y Hy p1 x; rewrite mem2_cat (Hy) (mem2rf Hy) andbF !orbF.
Qed.

Lemma mem2lr_splice : forall (p2 : seq T) x y,
    (x \in p2) = false -> (y \in p2) = false ->
  forall p1 p3, mem2 (p1 ++ p2 ++ p3) x y = mem2 (p1 ++ p3) x y.
Proof.
move=> p2 x y Hx Hy p1 p3.
by rewrite catA !mem2_cat !mem_cat Hx Hy (mem2lf Hx) !andbF !orbF.
Qed.

CoInductive split2r (x y : T) : seq T -> Type :=
  Split2r p1 p2 of y \in x :: p2 : split2r x y (p1 ++ x :: p2).

Lemma splitP2r : forall p x y, mem2 p x y -> split2r x y p.
Proof.
move=> p x y Hxy; have Hx := mem2l Hxy.
have Hi := Hx; rewrite -index_mem in Hi.
move: Hxy; rewrite /mem2 (drop_nth x Hi) (nth_index x Hx).
by case (splitP Hx); move=> p1 p2; rewrite cat_rcons; split.
Qed.

Fixpoint shorten x (p : seq T) {struct p} :=
  if p is y :: p' then
    if x \in p then shorten x p' else y :: shorten y p'
  else [::].

CoInductive shorten_spec (x : T) (p : seq T) : T -> seq T -> Type :=
   ShortenSpec p' of path e x p' & uniq (x :: p') & subpred (mem p') (mem p) :
     shorten_spec x p (last x p') p'.

Lemma shortenP : forall x p, path e x p ->
   shorten_spec x p (last x p) (shorten x p).
Proof.
move=> x p Hp; have: x \in x :: p by exact: mem_head.
elim: p x {1 3 5}x Hp => [|y2 p Hrec] x y1.
  by rewrite mem_seq1 => _; move/eqP->; split.
rewrite in_cons orbC /=; case/andP=> Hy12 Hp.
case: ifP => y2p_x; rewrite ?y2p_x.
  case: (Hrec _ _ Hp y2p_x) => p' Hp' Up' Hp'p _.
  by split=> // y; move/Hp'p; exact: predU1r.
case: (Hrec y2 _ Hp) => /= [|p' Hp' Up' Hp'p]; first by rewrite mem_head.
have{Hp'p} Hp'p: subpred (mem (y2 :: p')) (mem (y2 :: p)).
  by move=> z; rewrite /= !in_cons; case: (z == y2); last exact: Hp'p.
rewrite -(last_cons x); move/eqP=> xy1.
split=> //=; first by rewrite xy1 Hy12.
by rewrite {}Up' andbT; apply/negP; move/Hp'p; case/negPf.
Qed.

End EqPath.

(* Ordered paths and sorting. *)

Section SortSeq.

Variable T : eqType.
Variable leT : rel T.

Definition sorted s := if s is x :: s' then path leT x s' else true.

Lemma path_sorted : forall x s, path leT x s -> sorted s.
Proof. by move=> x [|y s] //=; case/andP. Qed.

Lemma path_min_sorted : forall x s,
  (forall y, y \in s -> leT x y) -> path leT x s = sorted s.
Proof. by move=> x [|y s] //= -> //; rewrite in_cons eqxx. Qed.

Section Transitive.

Hypothesis leT_tr : transitive leT.

Lemma subseq_order_path : forall x s1 s2,
  subseq s1 s2 -> path leT x s2 -> path leT x s1.
Proof.
move=> x s1 s2; elim: s2 x s1 => [|y s2 IHs] x [|z s1] //=.
move/(IHs y); case: eqP => [-> | _] /= IHs1; first by case/andP=> ->.
by case/andP=> leTxy; move/IHs1; case/andP; move/(leT_tr leTxy)->.
Qed.

Lemma order_path_min : forall x s, path leT x s -> all (leT x) s.
Proof.
move=> x s le_x_s; apply/allP=> y; rewrite -subseq_seq1 => s_y.
by have:= subseq_order_path s_y le_x_s; rewrite /= andbT.
Qed.

Lemma subseq_sorted : forall s1 s2, subseq s1 s2 -> sorted s2 -> sorted s1.
Proof.
case=> [|x1 s1] [|x2 s2] //= sub_s12; move/(subseq_order_path sub_s12).
by case: eqP => [-> | _] //=; case/andP.
Qed.

Lemma sorted_filter : forall a s, sorted s -> sorted (filter a s).
Proof. move=> a s; exact: subseq_sorted (filter_subseq a s). Qed.

Lemma sorted_uniq : irreflexive leT -> forall s, sorted s -> uniq s.
Proof.
move=> leT_irr; elim=> //= x s IHs s_ord.
rewrite (IHs (path_sorted s_ord)) andbT; apply/negP=> s_x.
by case/allPn: (order_path_min s_ord); exists x; rewrite // leT_irr.
Qed.

Lemma eq_sorted : antisymmetric leT -> forall s1 s2,
   sorted s1 -> sorted s2 -> perm_eq s1 s2 -> s1 = s2.
Proof.
move=> leT_asym; elim=> [|x1 s1 IHs1] s2 //= ord_s1 ord_s2 eq_s12.
  by case: {+}s2 (perm_eq_size eq_s12).
have s2_x1: x1 \in s2 by rewrite -(perm_eq_mem eq_s12) mem_head.
case: s2 s2_x1 eq_s12 ord_s2 => //= x2 s2; rewrite in_cons.
case: eqP => [<- _| ne_x12 /= s2_x1] eq_s12 ord_s2.
  by rewrite {IHs1}(IHs1 s2) ?(@path_sorted x1) // -(perm_cons x1).
case: (ne_x12); apply: leT_asym; rewrite (allP (order_path_min ord_s2)) //.
have: x2 \in x1 :: s1 by rewrite (perm_eq_mem eq_s12) mem_head.
case/predU1P=> [eq_x12 | s1_x2]; first by case ne_x12.
by rewrite (allP (order_path_min ord_s1)).
Qed.

Lemma eq_sorted_irr : irreflexive leT -> forall s1 s2,
  sorted s1 -> sorted s2 -> s1 =i s2 -> s1 = s2.
Proof.
move=> leT_irr s1 s2 s1_sort s2_sort eq_s12.
have: antisymmetric leT.
  move=> m n; case/andP=> ? ltnm; case/idP: (leT_irr m); exact: leT_tr ltnm.
move/eq_sorted; apply=> //; apply: uniq_perm_eq => //; exact: sorted_uniq.
Qed.

End Transitive.

Hypothesis leT_total : total leT.

Fixpoint merge s1 :=
  if s1 is x1 :: s1' then
    let fix merge_s1 (s2 : seq T) :=
      if s2 is x2 :: s2' then
        if leT x2 x1 then x2 :: merge_s1 s2' else x1 :: merge s1' s2
      else s1 in
    merge_s1
  else id.

Lemma path_merge : forall x s1 s2,
  path leT x s1 -> path leT x s2 -> path leT x (merge s1 s2).
Proof.
move=> x s1 s2; elim: s1 s2 x => //= x1 s1 IHs1; elim=> //= x2 s2 IHs2 x.
case/andP=> le_x_x1 ord_s1; case/andP=> le_x_x2 ord_s2.
case: ifP => le_x21 /=; first by rewrite le_x_x2 {}IHs2 // le_x21.
by rewrite le_x_x1 IHs1 //=; have:= leT_total x2 x1; rewrite le_x21 /= => ->.
Qed.

Lemma sorted_merge : forall s1 s2,
  sorted s1 -> sorted s2 -> sorted (merge s1 s2).
Proof.
move=> [|x1 s1] [|x2 s2] //= ord_s1 ord_s2.
case: ifP => le_x21 /=.
  by apply: (@path_merge x2 (x1 :: s1)) => //=; rewrite le_x21.
by apply: path_merge => //=; have:= leT_total x2 x1; rewrite le_x21 /= => ->.
Qed.

Lemma perm_merge : forall s1 s2, perm_eql (merge s1 s2) (s1 ++ s2).
Proof.
move=> s1 s2; apply/perm_eqlP; rewrite perm_eq_sym.
elim: s1 s2 => //= x1 s1 IHs1.
elim=> [|x2 s2 IHs2]; rewrite /= ?cats0 //.
case: ifP => _ /=; last by rewrite perm_cons.
by rewrite (perm_catCA (_ :: _) [::x2]) perm_cons.
Qed.

Lemma mem_merge : forall s1 s2, merge s1 s2 =i s1 ++ s2.
Proof. by move=> s1 s2; apply: perm_eq_mem; rewrite perm_merge. Qed.

Lemma size_merge : forall s1 s2, size (merge s1 s2) = size (s1 ++ s2).
Proof. by move=> s1 s2; apply: perm_eq_size; rewrite perm_merge. Qed.

Lemma merge_uniq : forall s1 s2, uniq (merge s1 s2) = uniq (s1 ++ s2).
Proof. by move=> s1 s2; apply: perm_eq_uniq; rewrite perm_merge. Qed.

Fixpoint merge_sort_push (s1 : seq T) (ss : seq (seq T)) {struct ss} :=
  match ss with
  | [::] :: ss' | [::] as ss' => s1 :: ss'
  | s2 :: ss' => [::] :: merge_sort_push (merge s1 s2) ss'
  end.

Fixpoint merge_sort_pop (s1 : seq T) (ss : seq (seq T)) {struct ss} :=
  if ss is s2 :: ss' then merge_sort_pop (merge s1 s2) ss' else s1.

Fixpoint merge_sort_rec (ss : seq (seq T)) (s : seq T) {struct s} :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    merge_sort_rec (merge_sort_push s1 ss) s'
  else merge_sort_pop s ss.

Definition sort := merge_sort_rec [::].

Lemma sorted_sort : forall s, sorted (sort s).
Proof.
rewrite /sort => s; have allss: all sorted [::] by [].
elim: {s}_.+1 {-2}s [::] allss (ltnSn (size s)) => // n IHn s ss allss.
have: sorted s -> sorted (merge_sort_pop s ss).
  elim: ss allss s => //= s2 ss IHss.
  by case/andP=> *; exact: IHss (sorted_merge _ _).
case: s => [|x1 [|x2 s _]]; try by auto.
move/ltnW; move/IHn; apply; rewrite {n IHn s} ifE; set s1 := if_expr _ _ _.
have: sorted s1 by exact: (@sorted_merge [::x2] [::x1]).
elim: ss {x1 x2}s1 allss => /= [|s2 ss IHss] s1; first by rewrite andbT.
case/andP=> ord_s2 ord_ss ord_s1.
by case: {1}s2=> /= [|_ _]; [rewrite ord_s1 | exact: IHss (sorted_merge _ _)].
Qed.

Lemma perm_sort : forall s, perm_eql (sort s) s.
Proof.
rewrite /sort => s; apply/perm_eqlP; pose catss := foldr (@cat T) [::].
rewrite perm_eq_sym -{1}[s]/(catss [::] ++ s).
elim: {s}_.+1 {-2}s [::] (ltnSn (size s)) => // n IHn s ss.
have: perm_eq (catss ss ++ s) (merge_sort_pop s ss).
  elim: ss s => //= s2 ss IHss s1; rewrite -{IHss}(perm_eqrP (IHss _)).
  by rewrite perm_catC catA perm_catC perm_cat2l -perm_merge.
case: s => // x1 [//|x2 s _]; move/ltnW; move/IHn=> {n IHn}IHs.
rewrite -{IHs}(perm_eqrP (IHs _)) ifE; set s1 := if_expr _ _ _.
rewrite (catA _ [::_;_] s) {s}perm_cat2r.
apply: (@perm_eq_trans _ (catss ss ++ s1)).
  by rewrite perm_cat2l /s1 -ifE; case: ifP; rewrite // (perm_catC [::_]).
elim: ss {x1 x2}s1 => /= [|s2 ss IHss] s1; first by rewrite cats0.
rewrite perm_catC; case def_s2: {2}s2=> /= [|y s2']; first by rewrite def_s2.
by rewrite catA -{IHss}(perm_eqrP (IHss _)) perm_catC perm_cat2l -perm_merge.
Qed.

Lemma mem_sort : forall s, sort s =i s.
Proof. by move=> s; apply: perm_eq_mem; rewrite perm_sort. Qed.

Lemma size_sort : forall s, size (sort s) = size s.
Proof. by move=> s; apply: perm_eq_size; rewrite perm_sort. Qed.

Lemma sort_uniq : forall s, uniq (sort s) = uniq s.
Proof. by move=> s; apply: perm_eq_uniq; rewrite perm_sort. Qed.

Lemma perm_sortP : transitive leT -> antisymmetric leT ->
  forall s1 s2, reflect (sort s1 = sort s2) (perm_eq s1 s2).
Proof.
move=> leT_tr leT_asym s1 s2; apply: (iffP idP) => eq12; last first.
  by rewrite -perm_sort eq12 perm_sort.
apply: eq_sorted; rewrite ?sorted_sort //.
by rewrite perm_sort (perm_eqlP eq12) -perm_sort.
Qed.

End SortSeq.

Lemma sorted_rev : forall (T : eqType) (leT : rel T) s,
  sorted leT (rev s) = sorted (fun y x => leT x y) s.
Proof. by move=> T leT [|x p] //=; rewrite -path_rev lastI rev_rcons. Qed.

Lemma sorted_ltn_uniq_leq : forall s, sorted ltn s = uniq s && sorted leq s.
Proof.
case=> //= n s; elim: s n => //= m s IHs n.
rewrite inE ltn_neqAle negb_or IHs -!andbA.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
rewrite eqn_leq lenm; exact: (allP (order_path_min leq_trans le_ms)).
Qed.

Lemma sorted_iota : forall i n, sorted leq (iota i n).
Proof. by move=> i n; elim: n i => // [[|n] //= IHn] i; rewrite IHn leqW. Qed.

Lemma sorted_ltn_iota : forall i n, sorted ltn (iota i n).
Proof. by move=> i n; rewrite sorted_ltn_uniq_leq sorted_iota iota_uniq. Qed.

(* Function trajectories. *)

Notation fpath f := (path (frel f)).
Notation fcycle f := (cycle (frel f)).
Notation ufcycle f := (ucycle (frel f)).

Prenex Implicits path next prev cycle ucycle mem2.

Section Trajectory.

Variables (T : Type) (f : T -> T).

Fixpoint traject x (n : nat) {struct n} :=
  if n is n'.+1 then x :: traject (f x) n' else [::].

Lemma trajectS : forall x n, traject x n.+1 = x :: traject (f x) n.
Proof. by []. Qed.

Lemma trajectSr : forall x n, traject x n.+1 = rcons (traject x n) (iter n f x).
Proof. by move=> x n; elim: n x => //= n IHn x; rewrite IHn -iterSr. Qed.

Lemma last_traject : forall x n, last x (traject (f x) n) = iter n f x.
Proof. by move=> x [|n] //; rewrite iterSr trajectSr last_rcons. Qed.

Lemma traject_iteri : forall x n,
  traject x n = iteri n (fun i => rcons^~ (iter i f x)) [::].
Proof. by move=> x; elim=> //= n <-; rewrite -trajectSr. Qed.

Lemma size_traject : forall x n, size (traject x n) = n.
Proof. by move=> x n; elim: n x => //= n IHn x //=; rewrite IHn. Qed.

Lemma nth_traject : forall i n, i < n ->
  forall x, nth x (traject x n) i = iter i f x.
Proof.
move=> i; elim=> // n IHn; rewrite ltnS leq_eqVlt => le_i_n x.
rewrite trajectSr nth_rcons size_traject.
case: ltngtP le_i_n => [? _||->] //; exact: IHn.
Qed.

End Trajectory.

Section EqTrajectory.

Variables (T : eqType) (f : T -> T).

Lemma fpathP : forall x p,
  reflect (exists n, p = traject f (f x) n) (fpath f x p).
Proof.
move=> x p; elim: p x => [|y p Hrec] x; first by left; exists 0.
rewrite /= andbC; case: {Hrec}(Hrec y) => Hrec.
  apply: (iffP eqP); first by case: Hrec => [n ->] <-; exists n.+1.
  by case=> [] [|n] // [Dp].
by right; move=> [[|n] // [Dy Dp]]; case: Hrec; exists n; rewrite Dy -Dp.
Qed.

Lemma fpath_traject : forall x n, fpath f x (traject f (f x) n).
Proof. by move=> x n; apply/(fpathP x); exists n. Qed.

Definition looping x n := iter n f x \in traject f x n.

Lemma loopingP : forall x n,
  reflect (forall m, iter m f x \in traject f x n) (looping x n).
Proof.
move=> x n; apply introP; last by move=> Hn Hn'; rewrite /looping Hn' in Hn.
case: n => [|n] Hn //; elim=> [|m Hrec]; first by exact: predU1l.
move: (fpath_traject x n) Hn; rewrite /looping !iterS -last_traject /=.
rewrite /= in Hrec; case/splitPl: Hrec; move: (iter m f x) => y p1 p2 Ep1.
rewrite path_cat last_cat Ep1; case: p2 => [|z p2] //; case/and3P=> [_ Dy _] _.
by rewrite !(in_cons, mem_cat) (eqP Dy) eqxx !orbT.
Qed.

Lemma trajectP : forall x n y,
  reflect (exists2 i, i < n & y = iter i f x) (y \in traject f x n).
Proof.
move=> x n y; elim: n x => [|n Hrec] x; first by right; case.
  rewrite /= in_cons orbC; case: {Hrec}(Hrec (f x)) => Hrec.
  by left; case: Hrec => [i Hi ->]; exists i.+1; last by rewrite -iterSr.
apply: (iffP eqP); first by exists 0; first by rewrite ltnNge.
by move=> [[|i] Hi Dy] //; case Hrec; exists i; last by rewrite -iterSr.
Qed.

Lemma looping_uniq : forall x n, uniq (traject f x n.+1) = ~~ looping x n.
Proof.
move=> x n; rewrite /looping; elim: n x => [|n Hrec] x //.
rewrite iterSr {2}[succn]lock /= -lock {}Hrec -negb_or in_cons; bool_congr.
set y := iter n f (f x); case (trajectP (f x) n y); first by rewrite !orbT.
rewrite !orbF => Hy; apply/idP/eqP => [Hx|Dy]; last first.
  by rewrite -{1}Dy /y -last_traject mem_last.
case: {Hx}(trajectP _ n.+1 _ Hx) => [m Hm Dx].
have Hx': looping x m.+1 by rewrite /looping iterSr -Dx mem_head.
case/trajectP: (loopingP _ _ Hx' n.+1); rewrite iterSr -/y.
move=> [|i] Hi //; rewrite iterSr => Dy.
by case: Hy; exists i; first exact (leq_trans Hi Hm).
Qed.

End EqTrajectory.

Implicit Arguments fpathP [T f x p].
Implicit Arguments loopingP [T f x n].
Implicit Arguments trajectP [T f x n y].
Prenex Implicits traject fpathP loopingP trajectP.

Section UniqCycle.

Variables (n0 : nat) (T : eqType) (e : rel T) (p : seq T).

Hypothesis Up : uniq p.

Lemma prev_next : cancel (next p) (prev p).
Proof.
move=> x; rewrite prev_nth mem_next next_nth.
case Hpx: (x \in p) => [|] //; case Dp: p Up Hpx => [|y p'] //.
rewrite -(Dp) {1}Dp /=; move/andP=> [Hpy Hp'] Hx.
set i := index x p; rewrite -(nth_index y Hx) -/i; congr (nth y).
rewrite -index_mem -/i Dp /= ltnS leq_eqVlt in Hx.
case/predU1P: Hx => [Di|Hi]; last by apply: index_uniq.
rewrite Di (nth_default y (leqnn _)).
rewrite -index_mem -leqNgt in Hpy.
by apply: eqP; rewrite eqn_leq Hpy /index find_size.
Qed.

Lemma next_prev : cancel (prev p) (next p).
Proof.
move=> x; rewrite next_nth mem_prev prev_nth.
case Hpx: (x \in p) => [|] //; case Dp: p Up Hpx => [|y p'] //.
rewrite -Dp => Hp Hpx; set i := index x p'.
have Hi: i < size p by rewrite Dp /= ltnS /i /index find_size.
rewrite (index_uniq y Hi Hp); case Hx: (x \in p'); first by apply: nth_index.
rewrite Dp in_cons Hx orbF in Hpx; rewrite (eqP Hpx).
by apply: nth_default; rewrite leqNgt /i index_mem Hx.
Qed.

Lemma cycle_next : fcycle (next p) p.
Proof.
case Dp: {-2}p Up => [|x p'] Up' //; apply/(pathP x)=> i; rewrite size_rcons => Hi.
rewrite -cats1 -cat_cons nth_cat Hi /= next_nth {}Dp mem_nth //.
rewrite index_uniq // nth_cat /=; rewrite ltnS leq_eqVlt in Hi.
case/predU1P: Hi => [Di|Hi]; last by rewrite Hi eqxx.
by rewrite Di ltnn subnn nth_default ?leqnn /= ?eqxx.
Qed.

Lemma cycle_prev : cycle (fun x y => x == prev p y) p.
Proof.
apply: etrans cycle_next; symmetry; case Dp: p => [|x p'] //.
apply: eq_path; rewrite -Dp; exact (can2_eq prev_next next_prev).
Qed.

Lemma cycle_from_next : (forall x, x \in p -> e x (next p x)) -> cycle e p.
Proof.
move=> He; case Dp: p cycle_next => [|x p'] //; rewrite -Dp !(cycle_path x).
have Hx: last x p \in p by rewrite Dp /= mem_last.
move: (next p) He {Hx}(He _ Hx) => np.
elim: (p) {x p' Dp}(last x p) => [|y p' Hrec] x He Hx //=.
case/andP=> [Dy Hp']; rewrite -{1}(eqP Dy) Hx /=.
apply: Hrec Hp' => [z Hz|]; apply: He; [exact: predU1r | exact: predU1l].
Qed.

Lemma cycle_from_prev : (forall x, x \in p -> e (prev p x) x) -> cycle e p.
Proof.
move=> He; apply: cycle_from_next => [x Hx].
by rewrite -{1}[x]prev_next He ?mem_next.
Qed.

Lemma next_rot : next (rot n0 p) =1 next p.
Proof.
move=> x; have Hp := cycle_next; rewrite -(cycle_rot n0) in Hp.
case Hx: (x \in p); last by rewrite !next_nth mem_rot Hx.
rewrite -(mem_rot n0) in Hx; exact (esym (eqP (next_cycle Hp Hx))).
Qed.

Lemma prev_rot : prev (rot n0 p) =1 prev p.
Proof.
move=> x; have Hp := cycle_prev; rewrite -(cycle_rot n0) in Hp.
case Hx: (x \in p); last by rewrite !prev_nth mem_rot Hx.
rewrite -(mem_rot n0) in Hx; exact (eqP (prev_cycle Hp Hx)).
Qed.

End UniqCycle.

Section UniqRotrCycle.

Variables (n0 : nat) (T : eqType) (p : seq T).

Hypothesis Up : uniq p.

Lemma next_rotr : next (rotr n0 p) =1 next p. Proof. exact: next_rot. Qed.

Lemma prev_rotr : prev (rotr n0 p) =1 prev p. Proof. exact: prev_rot. Qed.

End UniqRotrCycle.

Section UniqCycleRev.

Variable T : eqType.

Lemma prev_rev : forall p : seq T, uniq p -> prev (rev p) =1 next p.
Proof.
move=> p Up x; case Hx: (x \in p); last first.
  by rewrite next_nth prev_nth mem_rev Hx.
case/rot_to: Hx (Up) => [i p' Dp] Urp; rewrite -rev_uniq in Urp.
rewrite -(prev_rotr i Urp); do 2 rewrite -(prev_rotr 1) ?rotr_uniq //.
rewrite -rev_rot -(next_rot i Up) {i p Up Urp}Dp.
case: p' => [|y p'] //; rewrite !rev_cons rotr1_rcons /= eqxx.
by rewrite -rcons_cons rotr1_rcons /= eqxx.
Qed.

Lemma next_rev : forall p : seq T, uniq p -> next (rev p) =1 prev p.
Proof. by move=> p Up x; rewrite -{2}[p]revK prev_rev // rev_uniq. Qed.

End UniqCycleRev.

Section MapPath.

Variables (T T' : Type) (h : T' -> T) (e : rel T) (e' : rel T').

Definition rel_base (b : pred T) :=
  forall x' y', ~~ b (h x') -> e (h x') (h y') = e' x' y'.

Lemma path_map : forall b x' p', rel_base b ->
    ~~ has (preim h b) (belast x' p') ->
  path e (h x') (map h p') = path e' x' p'.
Proof.
move=> b x' p' Hb; elim: p' x' => [|y' p' Hrec] x' //=; move/norP=> [Hbx Hbp].
congr andb; auto.
Qed.

End MapPath.

Section MapEqPath.

Variables (T T' : eqType) (h : T' -> T) (e : rel T) (e' : rel T').

Hypothesis Hh : injective h.

Lemma mem2_map : forall x' y' p',
  mem2 (map h p') (h x') (h y') = mem2 p' x' y'.
Proof. by move=> *; rewrite {1}/mem2 (index_map Hh) -map_drop mem_map. Qed.

Lemma next_map : forall p, uniq p ->
  forall x, next (map h p) (h x) = h (next p x).
Proof.
move=> p Up x; case Hx: (x \in p); last by rewrite !next_nth (mem_map Hh) Hx.
case/rot_to: Hx => [i p' Dp].
rewrite -(next_rot i Up); rewrite -(map_inj_uniq Hh) in Up.
rewrite -(next_rot i Up) -map_rot {i p Up}Dp /=.
by case: p' => [|y p] //=; rewrite !eqxx.
Qed.

Lemma prev_map : forall p, uniq p ->
  forall x, prev (map h p) (h x) = h (prev p x).
Proof.
by move=> p Up x; rewrite -{1}[x](next_prev Up) -(next_map Up) prev_next ?map_inj_uniq.
Qed.

End MapEqPath.

Definition fun_base (T T' : eqType) (h : T' -> T) f f' :=
  rel_base h (frel f) (frel f').

Section CycleArc.

Variable T : eqType.

Definition arc (p : seq T) x y :=
  let px := rot (index x p) p in take (index y px) px.

Lemma arc_rot : forall i p, uniq p -> {in p, arc (rot i p) =2 arc p}.
Proof.
move=> i p Up x Hx y; congr (fun q => take (index y q) q); move: Up Hx {y}.
rewrite -{1 2 5 6}(cat_take_drop i p) /rot cat_uniq; move/and3P=> [_ Hp _].
rewrite !drop_cat !take_cat !index_cat mem_cat orbC.
case Hx: (x \in drop i p) => /= => [_|Hx'].
  rewrite [x \in _](negbTE (hasPn Hp _ Hx)).
  by rewrite index_mem Hx ltnNge leq_addr /= addKn catA.
by rewrite Hx' index_mem Hx' ltnNge leq_addr /= addKn catA.
Qed.

Lemma left_arc : forall x y p1 p2,
  let p := x :: p1 ++ y :: p2 in uniq p -> arc p x y = x :: p1.
Proof.
move=> x y p1 p2 p Up; rewrite /arc {1}/p /= eqxx rot0.
move: Up; rewrite /p -cat_cons cat_uniq index_cat; move: (x :: p1) => xp1.
rewrite /= negb_or -!andbA; move/and3P=> [_ Hy _].
by rewrite (negbTE Hy) eqxx addn0 take_size_cat.
Qed.

Lemma right_arc : forall x y p1 p2,
  let p := x :: p1 ++ y :: p2 in uniq p -> arc p y x = y :: p2.
Proof.
move=> x y p1 p2 p Up; set n := size (x :: p1); rewrite -(arc_rot n Up).
  move: Up; rewrite -(rot_uniq n) /p -cat_cons /n rot_size_cat.
  by move=> *; rewrite /= left_arc.
by rewrite /p -cat_cons mem_cat /= mem_head orbT.
Qed.

CoInductive rot_to_arc_spec (p : seq T) (x y : T) : Type :=
    RotToArcSpec i p1 p2 of x :: p1 = arc p x y
                          & y :: p2 = arc p y x
                          & rot i p = x :: p1 ++ y :: p2 :
    rot_to_arc_spec p x y.

Lemma rot_to_arc : forall p x y,
  uniq p -> x \in p -> y \in p -> x != y -> rot_to_arc_spec p x y.
Proof.
move=> p x y Up Hx Hy Hxy; case: (rot_to Hx) (Hy) (Up) => [i p' Dp] Hy'.
rewrite -(mem_rot i) Dp in_cons eq_sym (negPf Hxy) in Hy'.
rewrite -(rot_uniq i) Dp.
case/splitPr: p' / Hy' Dp => [p1 p2] Dp Up'; exists i p1 p2; auto.
  by rewrite -(arc_rot i Up Hx) Dp (left_arc Up').
by rewrite -(arc_rot i Up Hy) Dp (right_arc Up').
Qed.

End CycleArc.

Prenex Implicits arc.


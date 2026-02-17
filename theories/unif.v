From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.

Definition disjoint_tm t1 t2:=
  [disjoint vars_tm t1 & vars_tm t2].

Axiom match_unif: forall u a b s,
  matching u a b s -> unify u a b s.

Axiom unif_trans : forall u a b c s,
  unify u a b s -> unify u b c s -> unify u a c s.

Axiom unif_sym : forall u a b s,
  unify u a b s = unify u b a s.

(* Axiom unifP: forall u t1 t2 t3 s1 s2,  ground t3 ->
  ~~ unify u t1 t2 fmap0 -> unify u t3 t1 s1 -> ~~ unify u t3 t2 s2. *)

(* if 2 disjoint terms do not unify, then any rename cannot make them unify *)
(* Axiom unif_none_ren: forall u f1 f2 f3 f4 t1 t2 s,
  let tm1:= deref f1 t1 in let tm2:= deref f2 t2 in
  disjoint_tm tm1 tm2 ->
  ~~ unify u tm1 tm2 empty ->
  ~~ unify u (deref f3 t1) (deref f4 t2) s. *)

(* Axiom unif_none_ren: forall u f1 f2 f3 f4 t1 t2 s,
  let tm1:= ren f1 t1 in let tm2:= ren f2 t2 in
  disjoint_tm tm1 tm2 ->
  ~~ unify u tm1 tm2 empty ->
  ~~ unify u (ren f3 t1) (ren f4 t2) s. *)

Lemma unif_match u a b s:
  ~~unify u a b s -> ~~matching u a b s.
Proof. apply: contraNN; apply: match_unif. Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.

(* Lemma unif_matchP: forall u h1 h2 q  s1 s2,
  ~~ unify u h1 h2 fmap0  ->
     matching u q h1 s1   ->
  ~~ matching u q h2 s2.
Proof.
  move=> > U1 H.
  have U2 :=match_unif H.
  have U3 := unifP _ U1 U2.
  by apply: unif_match.
Qed.

 *)
Axiom matching_subst : forall u q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching u q (deref s t) fmap0) <-> (matching u q t s).

Lemma matching_subst1:
  forall u q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching u q t s) -> (matching u q (deref s t) fmap0).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma matching_subst2:
  forall u q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching u q (deref s t) fmap0) -> (matching u q t s).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Axiom matching_disj : 
  forall u a b s1 s1', 
  [disjoint vars_tm a & domf s1] ->
  disjoint_tm a b ->
  matching u a b s1 = Some s1' ->
  exists x, domf s1' = domf s1 `|` x /\ x `<=` vars_tm b.

Axiom matching_monotone : 
  forall u q t s, 
  (matching u q (deref s t) fmap0) -> (matching u q t fmap0).

Lemma match2_unif : forall u q t1 t2 s, (matching u q t1 s) -> (matching u q t2 s) -> (unify u t1 t2 s).
Proof.
 move=> u q t1 t2 s /match_unif H1 /match_unif H2; apply: unif_trans H2.
 by rewrite unif_sym.
Qed.

(* Axiom ad : adesive f f1 -> ren f t = ren (f + f1) t. *)

Axiom unif_rename : forall u t1 t2 (f : {fmap V -> V}), 
  injectiveb f ->
  (unify u t1 t2 fmap0) <-> (unify u (ren f t1) (ren f t2) fmap0).

(* Lemma unif_help: forall qa u f0 f1 f2 f3 t1 t2 s1' s2 s1'',
  let tm1 := (ren f0 t1) in let tm2 := (ren f1 t2) in
  let tm3 := (ren f2 t1) in let tm4 := (ren f3 t2) in
  disjoint_tm tm1 tm2 ->
  unify u tm1 tm2 fmap0  = None    ->
  matching u qa tm3 s1'  = Some s2 ->
  matching u qa tm4 s1'' = None.
Proof.
  move=> qa u f0 f1 f2 f3 t1 t2 s1' s2 s1'' tm1 tm2 tm3 tm4 D1 U M.
  have {}U := isNoneP U.
  have {}M := isSomeP M.
  apply/isNoneP1.
  apply: contra U => M'.
  move/matching_subst/matching_monotone: M => M.
  move/matching_subst/matching_monotone: M' => M'.
  have Abs := match2_unif M M'.
  have := (iffLR (unif_rename _ _ _ _)). *)
(* Admitted. *)

Axiom matching_V: forall u s t d,
  vars_sigma s `<=` d -> vars_tm t `<=` d ->
  matching u t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).


Definition acyclic_sigma (s:Sigma) :=
  [disjoint (domf s) & (codom_vars s)].

Axiom matching_acyclic: forall u a a1 s1 s2,
  acyclic_sigma s1 -> 
    matching u a a1 s1 = Some s2 -> acyclic_sigma s2.

Axiom unif_acyclic: forall u a a1 s1 s2,
  acyclic_sigma s1 -> 
    unify u a a1 s1 = Some s2 -> acyclic_sigma s2.

    
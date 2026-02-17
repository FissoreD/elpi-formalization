From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.

Section s.
Variable u: Unif.
Notation matching := (matching u).
Notation unify := (unify u).
Definition disjoint_tm t1 t2:=
  [disjoint vars_tm t1 & vars_tm t2].

(*SNIPT: matchunif *)
Axiom match_unif: 
  forall t1 t2 s, matching t1 t2 s -> unify t1 t2 s.
(*ENDSNIPT: matchunif *)

(*SNIPT: unif_trans *)
Axiom unif_trans:
  forall t1 t2 t3 s, unify t1 t2 s -> unify t2 t3 s -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)

Axiom unif_sym : forall t1 t2 s, unify t1 t2 s = unify t2 t1 s.

(* Axiom unifP: forall t1 t2 t3 s1 s2,  ground t3 ->
  ~~ unify t1 t2 fmap0 -> unify t3 t1 s1 -> ~~ unify t3 t2 s2. *)

(* if 2 disjoint terms do not unify, then any rename cannot make them unify *)
(* Axiom unif_none_ren: forall f1 f2 f3 f4 t1 t2 s,
  let tm1:= deref f1 t1 in let tm2:= deref f2 t2 in
  disjoint_tm tm1 tm2 ->
  ~~ unify tm1 tm2 empty ->
  ~~ unify (deref f3 t1) (deref f4 t2) s. *)

(* Axiom unif_none_ren: forall f1 f2 f3 f4 t1 t2 s,
  let tm1:= ren f1 t1 in let tm2:= ren f2 t2 in
  disjoint_tm tm1 tm2 ->
  ~~ unify tm1 tm2 empty ->
  ~~ unify (ren f3 t1) (ren f4 t2) s. *)

Lemma unif_match a b s:
  ~~unify a b s -> ~~matching a b s.
Proof. apply: contraNN; apply: match_unif. Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.

(* Lemma unif_matchP: forall h1 h2 q  s1 s2,
  ~~ unify h1 h2 fmap0  ->
     matching q h1 s1   ->
  ~~ matching q h2 s2.
Proof.
  move=> > U1 H.
  have U2 :=match_unif H.
  have U3 := unifP _ U1 U2.
  by apply: unif_match.
Qed.

 *)
Axiom matching_subst : forall q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching q (deref s t) fmap0) <-> (matching q t s).

Lemma matching_subst1:
  forall q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching q t s) -> (matching q (deref s t) fmap0).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma matching_subst2:
  forall q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching q (deref s t) fmap0) -> (matching q t s).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

(*SNIPT: matchdisj *)
Axiom matching_disj: 
  forall t1 t2 s s', [disjoint vars_tm t1 & domf s] -> disjoint_tm t1 t2 ->
  matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars_tm t2.
(*ENDSNIPT: matchdisj *)

(*SNIPT: matchingmono *)
Axiom matching_monotone: 
  forall q t s, matching q (deref s t) fmap0 -> matching q t fmap0.
(*ENDSNIPT: matchingmono *)

Lemma match2_unif : forall q t1 t2 s, (matching q t1 s) -> (matching q t2 s) -> (unify t1 t2 s).
Proof.
 move=> q t1 t2 s /match_unif H1 /match_unif H2; apply: unif_trans H2.
 by rewrite unif_sym.
Qed.

(* Axiom ad : adesive f f1 -> ren f t = ren (f + f1) t. *)

Axiom unif_rename : forall t1 t2 (f : {fmap V -> V}), 
  injectiveb f ->
  (unify t1 t2 fmap0) <-> (unify (ren f t1) (ren f t2) fmap0).

(* Lemma unif_help: forall qa u f0 f1 f2 f3 t1 t2 s1' s2 s1'',
  let tm1 := (ren f0 t1) in let tm2 := (ren f1 t2) in
  let tm3 := (ren f2 t1) in let tm4 := (ren f3 t2) in
  disjoint_tm tm1 tm2 ->
  unify tm1 tm2 fmap0  = None    ->
  matching qa tm3 s1'  = Some s2 ->
  matching qa tm4 s1'' = None.
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

Axiom matching_V: forall s t d,
  vars_sigma s `<=` d -> vars_tm t `<=` d ->
  matching t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).


Definition acyclic_sigma (s:Sigma) :=
  [disjoint (domf s) & (codom_vars s)].

Axiom matching_acyclic: forall a a1 s1 s2,
  acyclic_sigma s1 -> 
    matching a a1 s1 = Some s2 -> acyclic_sigma s2.

Axiom unif_acyclic: forall a a1 s1 s2,
  acyclic_sigma s1 -> 
    unify a a1 s1 = Some s2 -> acyclic_sigma s2.
End s.

    
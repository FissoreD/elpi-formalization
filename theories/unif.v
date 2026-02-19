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
Notation vars := vars_tm.

(*SNIPT: matchunif *)
Axiom match_unif: 
  forall t1 t2 s, matching t1 t2 s -> unify t1 t2 s.
(*ENDSNIPT: matchunif *)

(*SNIPT: unif_trans *)
Axiom unif_trans:
  forall t1 t2 t3 s, unify t1 t2 s -> unify t2 t3 s -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)

Axiom unif_sym : forall t1 t2 s, unify t1 t2 s = unify t2 t1 s.

Axiom matching_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> matching t1 t2 s = Some s' -> acyclic_sigma s'.

Axiom unif_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> unify t1 t2 s = Some s' -> acyclic_sigma s'.

Axiom matching_subst : forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q (deref s t) fmap0) <-> (matching q t s).

Notation "t1 # t2" := [disjoint t1 & t2] (at level 20).

(*SNIPT: matchdisj *)
Axiom matching_disj:
  forall s s' t1 t2, vars t1 # domf s -> vars t1 # vars t2 ->
    matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars t2.
(*ENDSNIPT: matchdisj *)

(*SNIPT: matchingmono *)
Axiom matching_monotone: 
  forall q t s, matching q (deref s t) fmap0 -> matching q t fmap0.
(*ENDSNIPT: matchingmono *)


Lemma matching_subst1:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q t s) -> (matching q (deref s t) fmap0).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma matching_subst2:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q (deref s t) fmap0) -> (matching q t s).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.


Lemma unif_match a b s:
  ~~unify a b s -> ~~matching a b s.
Proof. apply: contraNN; apply: match_unif. Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.

(* Axiom unif_rename : forall t1 t2 (f : {fmap V -> V}), 
  injectiveb f ->
  (unify t1 t2 fmap0) <-> (unify (ren f t1) (ren f t2) fmap0). *)

Lemma match2_unif : forall q t1 t2 s, (matching q t1 s) -> (matching q t2 s) -> (unify t1 t2 s).
Proof.
 move=> q t1 t2 s /match_unif H1 /match_unif H2; apply: unif_trans H2.
 by rewrite unif_sym.
Qed.

Axiom matching_V: forall s t d,
  vars_sigma s `<=` d -> vars t `<=` d ->
  matching t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).

Notation "A | B" := (A `|` B) (at level 15).
Notation injective := (@injectiveb _ V).
Notation "A ∧ B" := (A && B) (at level 15).
Notation rename := ren.

(*SNIPT: refresh_for *)
Definition refresh_for x t := 
  (vars t `<=` domf x) ∧ injective x ∧ (domf x # codomf x).
(*ENDSNIPT: refresh_for *)


(*SNIPT: unif_ren *)
Axiom unif_ren: 
  forall x y z w t1 t2,
  refresh_for w t1 -> refresh_for y t2 -> refresh_for z t1 -> refresh_for x t2 ->
  codomf w # vars (rename y t2) -> codomf z # vars (rename x t2) ->
  unify (rename w t1) (rename y t2) empty -> unify (rename z t1) (rename x t2) empty.
(*ENDSNIPT: unif_ren *)  

Lemma good_ren_app x f a: refresh_for x (Tm_App f a) = refresh_for x f && refresh_for x a.
Proof. rewrite/refresh_for/= fsubUset !andbA -!(andbC (injective x)) !andbA andbb !(andbC _ (_ # _)) !andbA andbb//. Qed.

Lemma disjoint_sub {T: choiceType} (s1 s2 s3: {fset T}):
  [disjoint s1 & s2] ->
  s3 `<=` s2 -> [disjoint s1 & s3].
Proof.
  move=> /eqP H1 D; apply/eqP; move: H1 D.
  move=> /fsetP I /fsubsetP S; apply/fsetP => x.
  have:= I x; have:= S x.
  rewrite !in_fsetI; case: (x \in s1) => //=.
  by case: (_ \in s3) => //=->//.
Qed.

Lemma varUP v (s: seq fvS):
  reflect (exists x, x \in s /\ v \in x) (v \in varsU s).
Proof.
  move=> /=; case vs: (_ \in _); constructor.
    elim: s v vs => //= x xs IH v; rewrite in_fsetU => /orP[] H.
      by exists x; rewrite in_cons eqxx//.
    have:= IH _ H => -[e [H1 H2]].
    by exists e; rewrite in_cons H1 orbT.
  move: vs; apply/contraFnot => -[+ []].
  elim: s v => //= x xs IH v vs.
  rewrite in_cons in_fsetU => /orP[/eqP?|]; subst; first by move => ->.
  by move=> H1 H2; rewrite (IH v vs)//orbT.
Qed.

Lemma codom_vars_sub v s (vs: v \in domf s): vars s.[vs] `<=` codom_vars s.
Proof.
  rewrite/codom_vars.
  apply/fsubsetP => /=v' H.
  apply/varUP; exists (vars s.[vs]); split => //.
  by apply/map_f/codomP; eexists.
Qed.

Lemma disjointUr {T:choiceType} (A B C: {fset T}): 
  fdisjoint A (B `|` C) = fdisjoint A B && fdisjoint A C.
Proof. by rewrite/fdisjoint fsetIUr fsetU_eq0//. Qed.

Lemma disjointUl {T:choiceType} (A B C: {fset T}): 
  fdisjoint (B `|` C) A = fdisjoint B A && fdisjoint C A.
Proof. by rewrite fdisjoint_sym disjointUr !(fdisjoint_sym A). Qed.

Lemma deref_disj_id s t: domf s # vars t -> deref s t = t.
Proof. 
  elim: t => //=[v|f Hf a Ha].
    rewrite/fdisjoint fsetI1; case: ifP.
      by move=> _ /eqP/fsetP/(_ v); rewrite !inE eqxx.
    by move=> H; rewrite not_fnd//H.
  by rewrite disjointUr => /andP[H1 H2]; rewrite Ha//Hf//.
Qed.

Lemma deref2 s t:
  acyclic_sigma s -> deref s (deref s t) = deref s t.
Proof.
  move=> H; elim: t => //=[v|f -> a ->]//.
  case: fndP => //= vs; last by rewrite not_fnd//.
  have: fdisjoint (domf s) (vars s.[vs]).
    by apply/disjoint_sub/codom_vars_sub/H.
  by apply/deref_disj_id.
Qed.

End s.
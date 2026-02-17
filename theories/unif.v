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

Definition disjoint_tm t1 t2:= [disjoint vars_tm t1 & vars_tm t2].

(*SNIPT: matchunif *)
Axiom match_unif: 
  forall t1 t2 s, matching t1 t2 s -> unify t1 t2 s.
(*ENDSNIPT: matchunif *)

(*SNIPT: unif_trans *)
Axiom unif_trans:
  forall t1 t2 t3 s, unify t1 t2 s -> unify t2 t3 s -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)

Axiom unif_sym : forall t1 t2 s, unify t1 t2 s = unify t2 t1 s.

Definition acyclic_sigma (s:Sigma) :=
  [disjoint (domf s) & (codom_vars s)].

Axiom matching_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> matching t1 t2 s = Some s' -> acyclic_sigma s'.

Axiom unif_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> unify t1 t2 s = Some s' -> acyclic_sigma s'.

Axiom matching_subst : forall q t s, 
  [disjoint vars_tm q & domf s] ->
  (matching q (deref s t) fmap0) <-> (matching q t s).

(*SNIPT: matchdisj *)
Axiom matching_disj: 
  forall t1 t2 s s', [disjoint vars_tm t1 & domf s] -> disjoint_tm t1 t2 ->
  matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars_tm t2.
(*ENDSNIPT: matchdisj *)

(*SNIPT: matchingmono *)
Axiom matching_monotone: 
  forall q t s, matching q (deref s t) fmap0 -> matching q t fmap0.
(*ENDSNIPT: matchingmono *)


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
  vars_sigma s `<=` d -> vars_tm t `<=` d ->
  matching t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).
End s.
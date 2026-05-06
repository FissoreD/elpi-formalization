From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.

Section s.
(* Variable u: Unif. *)
(* Notation matching := (matching u). *)
(* Notation unify := (unify u). *)
Notation vars := vars_tm.

Definition matching_var (s: Sigma) (query:V) (arg: Tm) := 
  @None Sigma.

Definition unify_var (s:Sigma) v arg := 
  if v \in vars_tm arg then None
  else Some s.[v <- arg].

Fixpoint unifier_help var_matcher n query pat s :=
  let unifier_help := unifier_help var_matcher in
  let query := deref s query in
  let pat := deref s pat in
  if query == pat then Some s
  else
  match n with
  | 0 => None
  | n.+1 =>
    match pat with 
    | Tm_V v' => unify_var s v' query
    | Tm_D _ | Tm_P _ =>
        match query with 
        | Tm_V v => var_matcher s v pat
        | _ => None
        end
    | Tm_App t1 t2 =>
      match query with
      | Tm_App tx ty => obind (unifier_help n ty t2) (unifier_help n tx t1 s)
      | Tm_V v => var_matcher s v pat
      | _ => None
      end
    end
  end.

Definition vars_nb t1 t2 := #|` (vars_tm t1 `|` vars_tm t2)|.

Definition matching_aux := unifier_help matching_var.
Definition matching t1 t2 s := matching_aux (vars_nb t1 t2) t1 t2 s.

Definition unify_aux := unifier_help unify_var.
Definition unify t1 t2 s := unify_aux (vars_nb t1 t2) t1 t2 s.

Lemma unify_V_empty v t:
  v \notin vars_tm t ->
  unify (Tm_V v) t empty = if t is Tm_V v' then Some empty.[v' <- Tm_V v] else Some empty.[v <- t].
Proof.
  rewrite/unify /vars_nb/= /unify_aux cardfsU1.
  move=> H; rewrite H/= !deref_empty.
  rewrite/unify_var.
  case:t H => //= v'.
    rewrite !inE => /eqP H; rewrite !ifF => //; apply/eqP; congruence.
  move=> t; case: (_ \in _) => //.
Qed.

Lemma unifier_help_refl h n t s: unifier_help h n t t s = Some s.
Proof. by elim: n s t => [|n IH] s t//=; case D: deref; rewrite ?eqxx//?IH/=IH//. Qed.

Lemma unify_refl t s: unify t t s = Some s.
Proof. apply/unifier_help_refl. Qed.

Definition ground t := vars_tm t == fset0.

Lemma ground_deref1 s t: ground t -> deref1 s t = t.
Proof. 
  rewrite/ground; elim: t => //=[v|f Hf a Ha].
    by move=> /eqP /fsetP /(_ v); rewrite !inE eqxx.
  by rewrite fsetU_eq0 => /andP => -[/Hf -> /Ha->].
Qed.

Lemma ground_deref s t: ground t -> deref s t = t.
Proof. by rewrite/deref; elim: #|`_| t => //= n IH*; rewrite ground_deref1//IH. Qed.

Lemma ground_V v: ground (Tm_V v) = false.
Proof. by rewrite/ground/=; apply:contraFF erefl => /eqP/fsetP /(_ v); rewrite !inE eqxx. Qed.

Lemma ground_app f a: ground (Tm_App f a) = ground f && ground a.
Proof. by rewrite /ground/= fsetU_eq0. Qed.

Lemma unify_help_ground_eq h n t1 t2 s s':
  ground t1 -> ground t2 -> unifier_help h n t1 t2 s = Some s' -> t1 = t2.
Proof.
  elim: n t1 t2 s s' => //=[|n IH] t1 t2 s s' G1 G2; rewrite !ground_deref//.
    by case: eqP => //.
  case: t2 G2 => [p|d|v|f a]; case: t1 G1 => [p'|d'|v'|f' a']; rewrite ?ground_V//=; try by case: eqP.
  rewrite !ground_app => /andP[Gf' Ga'] /andP[Gf Ga].
  case: eqP => //= H.
  case H1: unifier_help => [sx|]//=.
  case H2: unifier_help => [sy|]//=.
  by move=> [?]; subst; f_equal; apply/IH; eauto.
Qed.

Lemma unify_help_diff_ground h n t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help h n t1 t2 s = None.
Proof.
  elim: n t1 t2 s => [|n IH] t1 t2 s/= G1 G2; rewrite !ground_deref//; case: eqP => // _ H.
  case: t2 G2 H => [p|d|v|f a]; case: t1 G1 => [p'|d'|v'|f' a']; rewrite?(ground_V)//.
  rewrite !ground_app => /andP[Gf' Ga'] /andP[Gf Ga] H.
  case X: unifier_help => [s'|]//=.
  apply: IH => //.
  have:= unify_help_ground_eq Gf' Gf X; congruence.
Qed.

Lemma unify_diff_ground t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unify t1 t2 s = None.
Proof. by apply: unify_help_diff_ground. Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.

(*SNIPT: matchunif *)
Lemma match_unif: 
  forall t1 t2 s s', matching t1 t2 s = Some s' -> unify t1 t2 s = Some s'.
(*ENDSNIPT: matchunif *)
Proof.
  rewrite/matching/unify/matching_aux/unify_aux => t1 t2.
  move: (vars_nb _ _) => n.
  elim: n t1 t2 => [|n IH] t1 t2 s s'/=; first by [].
  case D1: deref => [p|d|v|f a];
  case D2: deref => [p'|d'|v'|f' a']//=.
  case: eqP => //= J.
  case u1: unifier_help => [sx|]//= u2.
  rewrite (IH _ _ _ _ u1)//=.
  by apply: IH.
Qed.

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
  unify a b s = None -> matching a b s = None.
Proof. case m: matching => [s'|]//; rewrite (match_unif m)//. Qed.

Lemma match2_unif : forall q t1 t2 s,
  (matching q t1 s) -> (matching q t2 s) -> (unify t1 t2 s).
Proof.
  move=> q t1 t2 s.
  case m1: matching => [s'|]//; case m2: matching => //[s''] _ _.
  have:= match_unif m1.
  have:= match_unif m2.
  move=> H1 H2.
  apply/unif_trans/isSomeP/H1/isSomeP.
  rewrite unif_sym.
  eauto.
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
  elim: t => //=[p|d|v|f Hf a Ha]; rewrite ?(deref_P,deref_D,deref_App)//.
    rewrite/fdisjoint fsetI1; case: ifP.
      by move=> _ /eqP/fsetP/(_ v); rewrite !inE eqxx.
    move=> /negP H; rewrite not_in_deref_V//=.
    by apply/negP.
  by rewrite disjointUr => /andP[H1 H2]; rewrite Ha//Hf//.
Qed.

(* Lemma deref2 s t:
  acyclic_sigma s -> deref s (deref s t) = deref s t.
Proof.
  move=> H; elim: t => //=[v|f -> a ->]//.
  case: fndP => //= vs; last by rewrite not_fnd//.
  have: fdisjoint (domf s) (vars s.[vs]).
    by apply/disjoint_sub/codom_vars_sub/H.
  by apply/deref_disj_id.
Qed. *)

End s.
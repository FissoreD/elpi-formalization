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

Definition compare_var '(IV v1) '(IV v2) := 
  if v1 <= v2 then (IV v1, IV v2) else (IV v2, IV v1).

Definition unify_var (s:Sigma) (v:V) arg := 
  if v \in vars_tm arg then None
  else 
    match arg with
    | Tm_V v' =>
      let: (v1, v2) := compare_var v v' in Some s.[v1 <- Tm_V v2]
    | _ => Some s.[v <- arg]
    end.
    (* Some s.[v <- arg]. *)

Fixpoint unifier_help is_matchin n query pat s :=
  let unifier_help := unifier_help is_matchin in
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
        | Tm_V v => if is_matchin then None else unify_var s v pat
        | _ => None
        end
    | Tm_App t1 t2 =>
      match query with
      | Tm_App tx ty => obind (unifier_help n ty t2) (unifier_help n tx t1 s)
      | Tm_V v => if is_matchin then None else unify_var s v pat
      | _ => None
      end
    end
  end.

Fixpoint size_tm t :=
  match t with
  | Tm_App f a => (size_tm f + size_tm a).+1
  | _ => 1
  end.

(* Definition vars_nb t1 t2 s := (size (vars_tmL t1) + size (vars_tmL t2) + #|` vars_sigma s|)%nat. *)

Definition unifier_help1 b t1 t2 s :=
  omap (fun x => s + x) (unifier_help b (size_tm t1 + size_tm t2) t1 t2 s).

Definition unifier_help2 b t1 t2 s := unifier_help1 b (deref s t1) (deref s t2) s.

Definition matching := unifier_help2 true.
Definition unify := unifier_help2 false.

Lemma compare_var_sym v1 v2: compare_var v1 v2 = compare_var v2 v1.
Proof. 
  case: v1 => v1; case: v2 => v2/=; rewrite leq_eqVlt.
  rewrite eq_sym; case: eqP => //=[->|v21]//; first by rewrite if_same.
  case: leqP => //=.
Qed.

Lemma omap_catf0 t: omap [eta catf empty] t = t.
Proof. by case: t => //=?; rewrite cat0f. Qed.

Lemma omap_catf_refl (t:Sigma): omap [eta catf t] (Some t) = Some t.
Proof. by rewrite/=; f_equal; apply/fmapP => k; rewrite fnd_cat if_same. Qed.

Lemma unify_V_empty v t: v \notin vars_tm t -> 
  unify (Tm_V v) t empty = unify_var empty v t.
Proof.
  rewrite/unify/unifier_help1/unifier_help2/unifier_help1 /= !deref_empty/= /unify_var omap_catf0.
  case:t => //= v'. rewrite !inE eq_sym; case: eqP => //= ?.
  case: eqP => //; first by congruence.
  by rewrite compare_var_sym.
Qed.

Lemma unifier_help_refl h n t s: unifier_help h n t t s = Some s.
Proof. by elim: n s t => [|n IH] s t//=; case D: deref; rewrite ?eqxx//?IH/=IH//. Qed.

Lemma unifier_help_refl1 b t s: unifier_help1 b t t s = Some s.
Proof. by rewrite/unifier_help1 unifier_help_refl omap_catf_refl. Qed.

Lemma unify_refl t s: unify t t s = Some s.
Proof. apply/unifier_help_refl1. Qed.

(* Lemma unify_help_ground_eq h n t1 t2 s s':
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
Qed. *)

Lemma unify_help_ground h n t1 t2 s: 
  ground t1 -> ground t2 -> (t1 == t2) = (unifier_help h n t1 t2 s).
Proof.
  elim: n t1 t2 s => [|n IH] t1 t2 s/= G1 G2; rewrite !ground_deref//; case: eqP => //.
  case: t2 G2 => [p|d|v|f a]; case: t1 G1 => [p'|d'|v'|f' a']//; rewrite?(ground_V,ground_app)//.
  move=> /andP[gf' ga'] /andP[gf ga] H.
  have:= IH _ _ s gf' gf; case: unifier_help => //s'; case: eqP => //=? _; subst.
  have:= IH _ _ s' ga' ga; case: unifier_help => //s''; case: eqP => //; congruence.
Qed.

Lemma unify_help_groundx b n t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help b n t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help_ground b n s G1 G2.
  by case: eqP => //;rewrite/unify; case: unifier_help.
Qed.

Lemma unify_help1_groundx b t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help1 b t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help_ground b (size_tm t1 + size_tm t2) s G1 G2.
  rewrite/unifier_help1; case: eqP => // _; case: unifier_help => //.
Qed.

Lemma unify_help2_groundx b t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help2 b t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help1_groundx b s G1 G2 H.
  by rewrite/unifier_help2 !ground_deref//.
Qed.

Lemma unify_diff_ground t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unify t1 t2 s = None.
Proof. by apply/unify_help2_groundx. Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.


Lemma match_help_unif n t1 t2 s s': 
  unifier_help true n t1 t2 s = Some s' -> unifier_help false n t1 t2 s = Some s'.
Proof.
  elim: n t1 t2 s s' => [|n IH]//= t1 t2 s s'.
  case D1: deref => [p|d|v|f a];
  case D2: deref => [p'|d'|v'|f' a']//=.
  case: eqP => // _.
  case u1: unifier_help => [sy|]//= u2.
  rewrite (IH _ _ _ _ u1)//=.
  by apply: IH.
Qed.

Lemma match_unif t1 t2 s s': matching t1 t2 s = Some s' -> unify t1 t2 s = Some s'.
Proof.
  rewrite/matching/unify/unifier_help2/unifier_help1.
  case U1: unifier_help => //=[sx][?]; subst.
  by rewrite (match_help_unif U1)//.
Qed.

Lemma ground_vars_card t: ground t -> #|` vars_tm t | = 0.
Proof.
  elim: t => //=[v|f Hf a Ha]; rewrite (ground_V, ground_app)//.
  by move=> /andP[/Hf/cardfs0_eq->]; rewrite fset0U.
Qed.

Lemma unify_fuel_ground n m b t1 t2 s:
  ground t1 -> ground t2 ->
  unifier_help b n t1 t2 s = unifier_help b m t1 t2 s.
Proof.
  move=> G1 G2; case: (boolP (t1 == t2)) => /eqP H; subst.
    by rewrite !unifier_help_refl.
  by rewrite !unify_help_groundx//.
Qed.

Lemma unif_fuel n m b t1 t2 s:
  size_tm (deref s t1) + size_tm (deref s t2) <= n ->
  size_tm (deref s t1) + size_tm (deref s t2) <= m ->
  unifier_help b n t1 t2 s = unifier_help b m t1 t2 s.
Proof.
  elim: n m t1 t2 s => //=[|n IH] m t1 t2 s Hn Hm.
    admit.
  case: m Hm => [|m] Hm//=.
    admit.
  case: eqP => // D.
  case D1: deref => [p|d|v|f a];
  case D2: deref => [p'|d'|v'|f' a']//=.
  case: (boolP (ground t1)) => G1.
    move: D2; rewrite !ground_deref// => ?; subst.
    move: G1; rewrite !ground_app => /andP[gf' ga'].
    case: (boolP (ground t2)) => G2.
      move: D1; rewrite !ground_deref// => ?; subst.
      move: G2; rewrite !ground_app => /andP[gf ga].
      rewrite (unify_fuel_ground _ m)//.
      case: unifier_help => //=s'.
      rewrite (unify_fuel_ground _ m)//.
    move: Hn Hm => /=; rewrite deref_App/= addSn !ltnS => Hn Hm.
    rewrite -(IH m)//=.
      case U: unifier_help => [sx|]//=.
      apply: IH.

      admit.
Admitted.

Require Import Lia.

(*SNIPT: unif_trans *)
Lemma unif_trans t1 t2 t3 s: unify t1 t2 s -> unify t2 t3 s -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)
Proof.
  (* pose N := (size (vars_tmL t1) + size (vars_tmL t2) + size (vars_tmL t3) + #|` vars_sigma s|)%nat.
  rewrite/unify -(@unif_fuel N)%nat => //; last first.
    by rewrite/N/vars_nb leq_add2r -addnA leq_add2l leq_addr.
  move=> H1.
  rewrite -(@unif_fuel N)%nat => //; last first.
    by rewrite/N/vars_nb !leq_add2r leq_addl.
  move=> H2.
  rewrite -(@unif_fuel N)%nat => //; last first.
    by rewrite/N/vars_nb !leq_add2r leq_addr.
  move: H1 H2.
  move: @N => /=.
  remember (_ + _)%nat as n eqn:Hn; elim: n s t1 t2 t3 Hn => [|n IH] s t1 t2 t3 Hn.
    admit. *)
Admitted.

Lemma unify_help_ext n t1 t2 s s':

  unifier_help false n t1 t2 s = Some s' ->
    exists e : finMap lang_V__canonical__choice_Choice Tm,
      [disjoint domf e & domf s] /\ s' = s + e.
Proof.
  elim: n t1 t2 s s' => //= [|n IH] t1 t2 s s'.
    by case: eqP => // H [<-]; exists empty; rewrite catf0 fdisjoint0X.
  case: eqP => // DE; first by move=> [<-]; exists empty; rewrite catf0 fdisjoint0X.
  rewrite/unify_var/=.
  case D1: deref => [p|d|v|f a].
  - case D2: deref => [p'|d'|v'|f' a']//= [?]; subst; exists [fmap].[v' <- Tm_P p].
    rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//= [?]; subst; exists [fmap].[v' <- Tm_D d].
    rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
    admit.
  - case: (boolP (_ \in _)) => //.
    admit.
  - case D2: deref => [p|d|v|f' a']//.
      case: (boolP (_ \in _)) => // vd1[<-]; exists [fmap].[v <- Tm_App f a].
      rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
      admit.
    case Uf: unifier_help => [sx|]//= Ua.
    have:= IH _ _ _ _ Uf; have:= IH _ _ _ _ Ua.
    move=> [sy[D ?]][sz[R ?]]; subst.
    move: D; rewrite domf_cat fdisjointXU => /andP[S T].
    by exists (sz + sy); rewrite catfA domf_cat fdisjointUX R S.
Admitted.


Lemma unif_ext t1 t2 s s': unify t1 t2 s = Some s' ->
  exists e, [disjoint domf e & domf s] /\ s' = s + e.
Proof.
  rewrite/unify/unifier_help2/unifier_help1.
  case U: unifier_help => [sx|]//=[?]; subst.
  exists sx; split => //.
Admitted.

Definition swaps_aux (s : Sigma) :=
  let d := filterf s (fun x => if s.[?x] is Some (Tm_V v) then true else false) in
  s.[\ domf d] + [fmap x : codom_vars d => Tm_V (get_father (val x) d)].

Definition swap (sold snew:Sigma) :=
  (snew.[& domf sold] + swaps_aux snew.[\ domf sold]).

Lemma filter0 (K: choiceType) V f: filterf (@fmap0 K V) f = fmap0.
Proof. by apply/fmapP => H; rewrite fnd_filterf !not_fnd// if_same. Qed.

Lemma swaps_aux0: swaps_aux fmap0 = fmap0.
Proof. by apply/fmapP => J; rewrite !not_fnd// /swaps_aux !inE !not_fnd//filter0 codom_vars0. Qed.

Lemma remf_all (K:choiceType) V (s : {fmap K -> V}): s.[\ domf s] = fmap0.
Proof. apply/fmapP => k; rewrite fnd_rem; case: (boolP (_ \in _)) => ks; rewrite !not_fnd//. Qed.

Lemma swap_refl s: swap s s = s.
Proof. by rewrite /swap restrictfT remf_all swaps_aux0 catf0. Qed.

Definition is_var t := if t is (Tm_V _) then true else false.

(* Definition principal_unifier sigma A : Prop :=
 unif sigma A /\ 
 forall tau, unif tau A -> forall s, tau (sigma s) = tau s. *)

Axiom phi: Tm -> Tm -> Sigma.

Axiom xx: forall t1 t2 s s', 
  unify t1 t2 s = Some s' -> deref s' t1 = deref s' (deref (phi t1 t2) t1).

(* f X X = f Z Y ====> {X = Z; Z = Y} *)
(* f Z Y = f X X ====> {Y = X; Z = X} *)
(* Lemma unif_symP t1 t2 s s':
  unify t1 t2 s = Some s' -> unify t2 t1 s = Some (swap s s').
Proof.
  rewrite/unify/vars_nb addnC.
  move: (_+_)%nat => n; elim: n t1 t2 s s' => //= [|n IH] t1 t2 s s'.
    by rewrite/= eq_sym; case: eqP => // D [<-]; rewrite swap_refl.
  rewrite eq_sym; case: eqP => // DE.
    by move=> [<-]; rewrite swap_refl.
  rewrite/unify_var/=; move: DE.
  case D1: deref => [p|d|v|f a].
  - case D2: deref => [p'|d'|v'|f' a']//=; move=> DE [<-]; f_equal.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//=; move=> DE [<-]; f_equal.
    admit.
  - case: (boolP (_ \in _)) => // H + [<-].
    case: (boolP (is_var (deref s t1))).
      case D2: deref => [p'|d'|v'|f' a']//=.
      rewrite !inE; case: eqP => //?; subst => //.
      admit.
    move=> IV Hx.
    suffices: s.[v <- deref s t1] = (swap s s.[v <- deref s t1]).
      by move: IV => + <-; case: deref => //.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//=.
      rewrite !inE; case: (boolP (_ \in _)) => //=vf.
      case: (boolP (_ \in _)) => //=va _ [<-].
      admit.
    move=> H.
    rewrite-/unify_var.
    case U1: unifier_help => [sz|]//= U2.
    have [e[Dx ?]] := unify_help_ext U1; subst.
    have [e'[Dy ?]] := unify_help_ext U2; subst.
    have Hf := IH _ _ _ _ U1.
    have Ha := IH _ _ _ _ U2.
    rewrite Hf/=.
Admitted. *)

Lemma unif_sym t1 t2 s: unify t1 t2 s = unify t2 t1 s.
Proof.
  rewrite/unify/unifier_help2/unifier_help1.
  move: (deref _ _) (deref _ _) => {}t1 {}t2.
  rewrite addnC; move: (_ + _)%nat => n.
  f_equal.
  elim: n t1 t2 s => //= [|n IH] t1 t2 s.
    by rewrite/= eq_sym.
  rewrite eq_sym; case: eqP => // DE.
  case D1: deref => [p|d|v|f a]; case D2: deref => [p'|d'|v'|f' a']//=.
    by rewrite/unify_var !inE eq_sym compare_var_sym.
  rewrite IH.
  case U1: unifier_help => [s'|]//=.
Qed.

(* Lemma unif_sym t1 t2 s: unify t1 t2 s -> unify t2 t1 s.
Proof. case U: unify => //_; apply/isSomeP. /unif_symP/U. Qed. *)


Axiom unif_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> unify t1 t2 s = Some s' -> acyclic_sigma s'.

Lemma matching_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> matching t1 t2 s = Some s' -> acyclic_sigma s'.
Proof. by move=> > A /match_unif; apply: unif_acyclic. Qed.

Axiom matching_subst : forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q (deref s t) fmap0) <-> (matching q t s).

Notation "t1 # t2" := [disjoint t1 & t2] (at level 20).

Search deref fdisjoint.

Lemma disjoint_deref1_refl s t:
  vars t # domf s -> deref1 s t = t.
Proof.
  elim: t => //= [v|f Hf a Ha].
    by rewrite fdisjoint1X => H; rewrite not_fnd.
  rewrite fdisjointUX => /andP[/Hf-> /Ha->]//.
Qed.

Lemma disjoint_deref_refl s t:
  vars t # domf s -> deref s t = t.
Proof.
  rewrite/deref; move: #|`_| => n; elim: n t => //= n IH t H.
  by rewrite disjoint_deref1_refl//IH.
Qed.

(*SNIPT: matchdisj *)
Lemma matching_disj:
  forall s s' t1 t2, vars t1 # domf s -> vars t1 # vars t2 ->
                                                                  (*SHOULD BE: e `<=` vars (deref s t2)*)
    matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars t2.
(*ENDSNIPT: matchdisj *)
Proof.
  rewrite/matching/unifier_help2/unifier_help1 => s s' t1 t2.
  case U: unifier_help => //=[sx] V1 V2[?]; subst.
  exists (domf sx); rewrite domf_cat; split => //.
Admitted.

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
  rewrite unif_sym in H2.
  apply/unif_trans/isSomeP/H1/isSomeP/H2.
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
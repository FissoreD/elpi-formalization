From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From det Require Import finmap ctx.
From det Require Import lang unif.

Definition is_mgu (mgu s : Sigma) :=
  exists2 r : Sigma, acyclic r &
      forall t, deref r (deref mgu t) = deref s t.

Definition mgu_help base mgu l :=
  forall s, acyclic s -> unifier s l -> is_mgu base s -> is_mgu mgu s.

Lemma mgu_help_refl b l: mgu_help b b l.
Proof. by move=> *. Qed.

Lemma mgu_help_tt b s t l: mgu_help b s l -> mgu_help b s ((t, t) :: l).
Proof. by move=> H x A /=/andP[_ U] M; apply: H. Qed.

Lemma mgu_help_app b s f1 f2 a1 a2 l:
  mgu_help b s [:: (f1, f2), (a1, a2) & l] ->
  mgu_help b s ((Tm_App f1 a1, Tm_App f2 a2) :: l).
Proof.
  move=> H x A /=; rewrite unif_pair_app -andbA => /and3P[U1 U2 U].
  by apply: H; rewrite//= U1 U2.
Qed.

Lemma mgu_help_cons_comm s s' t1 t2 l:
  mgu_help s s' ((t1, t2) :: l) ->
  mgu_help s s' ((t2, t1) :: l).
Proof.
  move=> H x A /=/andP[/eqP/= U1 U2] M.
  by apply: H => //=; rewrite /unif_pair/map_prod1/= U1 eqxx.
Qed.

Lemma in_setI1 {S: choiceType} (s1 s2 : {fset S}) x: 
  x \in s1 `&` s2 -> x \in s1.
Proof. by rewrite inE => /andP[]. Qed.

Lemma deref_deref_sigma v t m q: v \notin m ->
  deref (deref_sigma v t m) q = derefkv v t (deref m q).
Proof.
  move=> vm.
  elim: q => //[v'|/=f -> ?->//].
  rewrite !deref_V fnd_set; case: eqP => vv; subst.
    by rewrite not_fnd//=/derefkv deref_V FmapE.fmapE//eqxx.
  case: fndP => vm'; last by rewrite not_fnd//=/derefkv deref_V FmapE.fmapE not_fnd// ifF//; case: eqP.
  by rewrite in_fnd ffunE valPE.
Qed.

Definition build_rV (s: Sigma) f := [fmap x : domf s `&` f => s.[in_setI1 (valP x)]].
Definition build_r (s:Sigma) t := build_rV s (vars t).

Lemma buildrV_in s x f (xs: x \in domf s) (xI: x \in domf s `&` f):
  (build_rV s f) [`xI] = s.[xs].
Proof. by rewrite ffunE; f_equal; apply/val_inj. Qed.

Lemma buildr_in s t x (xs: x \in domf s) (xI: x \in domf s `&` vars t):
  (build_r s t) [`xI] = s.[xs].
Proof. apply: buildrV_in. Qed.

(* Lemma mapI_v T (S:choiceType) (s1 s2: {fset S}) (x:S) (xP : x \in s1 `&` s2) (F: _ -> T):
  [fmap x : s1 `&` s2 => F x] [`xP] = 
  F [`xP].
Admitted. *)

Lemma in_vars x r t: acyclic r -> x \in domf r -> x \in vars (deref r t) = false.
Proof.
  move=> A xr.
  elim: t => //=[v|f Hf a Ha]; last by rewrite inE Hf//.
  case: fndP => //=vr; last by rewrite inE; case: eqP => ?; subst; rewrite//xr in vr.
  have:= fdisjointP A _ xr; apply/contraNF => H.
  by apply/codom_varsP; exists v, vr.
Qed.

Lemma in_vars_V x r v (vx : v \in domf r): acyclic r -> x \in domf r -> x \in vars r.[vx] = false.
Proof.
  move=> A xr; replace r.[vx] with (deref r (Tm_V v)) by rewrite/=in_fnd//.
  by rewrite in_vars.
Qed.

Lemma deref_buildr s t: deref (build_r s t) t = deref s t.
Proof.
  rewrite/build_r.
  suffices H: forall f, vars t `<=` f -> deref (build_rV s f) t = deref s t.
    by apply H.
  move=> fv; elim: t => //[v|/=a Ha f Hf]; last first.
    by rewrite fsubUset => /andP[af ff]; rewrite Hf//Ha.
  rewrite fsub1set !deref_V => vfv.
  case: fndP.
    move=> /[dup]; rewrite {1}inE => /andP[vs vt] vb.
    by rewrite buildrV_in//in_fnd//.
  by rewrite inE vfv andbT => vs; rewrite not_fnd.
Qed.

Lemma deref2_cat_build r s t sx:
  deref r t = deref s t -> deref (r + build_rV s sx) t = deref s t.
Proof.
  elim: t => //[v|/=f Hf a Ha]; last first.
    by move=> [H1 H2]; rewrite Hf//Ha.
  rewrite !deref_V fnd_cat.
  set X := build_rV _ _.
  case: (fndP s) => vs; last first.
    have vb: v \notin domf X by rewrite inE (negbTE vs).
    by rewrite (not_fnd vb) (negbTE vb).
  case: (boolP (v \in sx)) => vsx.
    have vX : v \in domf X by rewrite inE vs.
    by rewrite vX (in_fnd vX)// buildrV_in.
  have vb: v \notin domf X by rewrite inE (negbTE vsx) andbF.
  by rewrite (not_fnd vb) (negbTE vb).
Qed.

Lemma is_mgu_deref_sigma v t mgu s (vs: v \in domf s):
  acyclic mgu -> acyclic s -> v \notin vars t -> domf mgu # vars t ->
  s.[vs] = deref s t -> v \notin domf mgu ->
  is_mgu mgu s -> is_mgu (deref_sigma v t mgu) s.
Proof.
  move=> Am As vt Dmt H vm [r Ar Mr].
  have vr : v \in domf r.
    have:= Mr (Tm_V v); rewrite /=not_fnd//= (in_fnd vs)/=.
    case: fndP => //=vr; rewrite H; destruct t as [|v'|] => //=.
    simpl in *; case: fndP => //vs'; last by move=> [?]; subst; rewrite inE eqxx in vt.
    move=> Hv; rewrite -(negbTE(fdisjointP As _ vs)); simpl in Hv.
    by apply/codom_varsP; eexists _, vs'; rewrite -Hv inE.
  rename Mr into Mr'.
  have {}Mr := Mr' (Tm_V _).
  have vrP: r.[vr] = s.[vs].
    by have:= Mr v; rewrite /=not_fnd//= !in_fnd//.
  exists (r + build_r s t).
    apply/fdisjointP => x; rewrite domf_cat /=2!inE => Hx.
    apply/codom_varsP => -[y[yP]].
    case: (fndP (build_r s t) y) => yX.
      rewrite getf_catr//; move: yX (yX).
      rewrite {1}inE => /andP[ys yt] yX.
      rewrite buildr_in {yX}.
      move: Hx; case: fndP => [xr _|xr /andP[xs xt]]/=.
        have:= Mr y; rewrite/= (in_fnd ys)/=.
        case: fndP => ym/=.
          by move=> <-; rewrite in_vars//.
        case: fndP => yr/= Hy; last first.
          by have:= fdisjointP As _ ys => /codom_varsP[]; exists y, ys; rewrite -Hy inE.
        by rewrite -Hy in_vars_V//.
      move=> Hx.
      have:= fdisjointP As _ xs =>/codom_varsP[]//=.
      by exists y, ys.
    rewrite getf_catl//.
      by move: yX yP; rewrite domf_cat in_fsetU => /negbTE->; rewrite orbF.
    move=> yr xP{yP}.
    move: Hx; case: fndP => xr/=.
      by have:= fdisjointP Ar _ xr => /codom_varsP[]; exists y, yr.
    move=> /andP[xs xt].
    have:= Mr x; rewrite/= (in_fnd xs)/=.
    rewrite not_fnd/=.
      rewrite not_fnd//= => Hx.
      by have:= fdisjointP As _ xs => /codom_varsP[]; exists x, xs; rewrite -Hx inE.
    by apply: fdisjointP_sym xt.
  move=> q.
  rewrite deref_deref_sigma//=. 
  elim: q => //[q|/=?->?->//].
  rewrite deref_V/=.
  have /[dup] Mq := Mr q; rewrite !deref_V.
  case: fndP => qm'/=.
    case: fndP=>qs'//=; last first.
      case Mv: mgu.[qm'] => //=[v'].
      rewrite/derefkv deref_V !FmapE.fmapE (@not_fnd _ _ fmap0)//; case: eqP => vv; subst.
        rewrite in_fnd/= vrP H.
        destruct t as [|v2|]; rewrite//!deref_V fnd_cat !inE eqxx andbT.
        case: fndP => v2s; last first.
          move=> [?]; subst; move: H; rewrite/=not_fnd//=-vrP => vrPx.
          case: fndP => //=vr'.
          by have:= fdisjointP Ar _ vr' => /codom_varsP[]; eexists _,vr; rewrite vrPx inE.
        rewrite odflt_Some => v2sP.
        move: H; rewrite deref_V in_fnd//v2sP => H.
        rewrite in_fnd; first by rewrite !inE v2s/=.
        by move=> v2h; rewrite buildr_in.
      rewrite deref_V fnd_cat; case: fndP => vr'; last first.
        move=> [?]; subst.
        by have:= fdisjointP Am _ qm' => /codom_varsP[]; eexists _, qm'; rewrite Mv inE.
      rewrite odflt_Some => Hx.
      rewrite Hx; case: ifP; rewrite // => vH.
      move: (vH); rewrite inE => /andP[vs' vt'].
      rewrite in_fnd//buildr_in//=-Hx.
      have:= Mr v'; rewrite/=not_fnd//=; first rewrite !in_fnd//=.
      by have:= fdisjointP_sym Dmt _ vt'.
    move=> <-.
    elim: mgu.[qm'] => //[v'|/=?->?->//].
    rewrite /derefkv !deref_V fnd_set (@not_fnd _ _ fmap0)//.
    case: eqP=> vv; subst; last first.
      rewrite deref_V fnd_cat.
      case: fndP => ///[dup].
      rewrite {1}inE => /andP[vs' vt'] vb.
      rewrite buildr_in/=.
      have:= Mr v'; rewrite/= not_fnd/=; first by move=> ->; rewrite in_fnd.
      by apply/fdisjointP_sym/vt'.
    rewrite in_fnd/=.
    rewrite vrP H.
    have:= Mr' t; rewrite (not_in_deref Dmt); apply: deref2_cat_build.
  rewrite/derefkv deref_V fnd_set (@not_fnd _ _ fmap0)//.
  case: eqP => qv; subst; last first.
    rewrite deref_V fnd_cat.
    case: ifP => qs; rewrite//(in_fnd qs).
    move: qs (qs); rewrite {1}inE => /andP[qs qt] qp.
    by rewrite buildr_in/={qp}(in_fnd qs)//.
  rewrite (in_fnd vs)/= H in_fnd/= => _.
  have:= Mr' t; rewrite (not_in_deref Dmt); apply: deref2_cat_build.
Qed.

Lemma mgu_help_deref_sigma v t s l mgu:
  acyclic s -> v \notin domf s -> v \notin vars t -> domf s # vars t ->
  mgu_help (deref_sigma v t s) mgu (deref_list v t l) ->
  mgu_help s mgu ((Tm_V v, t) :: l).
Proof.
  move=> A vs vt Dst IH.
  move=> x A' /=/andP[/eqP/= Ur Ul] M.
  apply: IH => //{mgu}; rename s into mgu; rename x into s.
    move: Ur; case: fndP => /=vx H.
      apply: unifier_deref_list => //.
      apply/forallP => -[y yP]; rewrite valPE ffunE[val _]/=.
      by move: yP; rewrite !inE orbF => /eqP?; subst; rewrite eqxx/= -H in_fnd.
    case: t vt H {Dst} => //v'; rewrite inE => vv/=.
    case: fndP => vx'/=; last by move=> [?]; subst; rewrite eqxx in vv.
    by move=> *; apply: unifier_deref_list_not_in.
  clear l Ul; move: M Ur => [r Ar M]; case: fndP => vx/=; last first.
    { case: t vt {Dst} => //=v'; rewrite inE => vv.
    case: fndP => vx'/=; last by move=> [?]; subst; rewrite eqxx in vv.
    move=> H.
    have /= := M (Tm_V v); rewrite not_fnd//not_fnd//=.
    case: fndP => //=vr Hr.
      have:= fdisjointP Ar _ vr => /codom_varsP[].
      by exists v, vr; rewrite Hr/= inE.
    clear Hr.
    have:= M (Tm_V v').
    rewrite !deref_V  (in_fnd vx')/=-H.
    case: fndP => //=vm'; last first.
      case: fndP => vr'/=; last by move=> [?]; subst; rewrite eqxx in vv.
      move=> Hr; exists r => //.
      elim => //[v2|/=f -> a ->//].
      rewrite deref_V//fnd_set; case: eqP => //v2v; subst.
        by rewrite !deref_V (not_fnd vx)/= in_fnd.
      rewrite -(M (Tm_V v2)) deref_V.
      case: fndP => //v2m; [rewrite in_fnd|rewrite not_fnd//].
      by rewrite ffunE valPE/= derefkv_not_in//.
    exists (deref_sigma v' (Tm_V v) r).
      apply: acyclic_sigma_deref_sigma => //; first by rewrite inE eq_sym.
      by rewrite /=fdisjointX1.
    elim => //[v2|/=?->?->//].
    rewrite !deref_V fnd_set; case: eqP => vv2; subst.
      by rewrite deref_V fnd_set eqxx//= not_fnd.
    have:= M (Tm_V v2); rewrite !deref_V.
    case: (fndP [fmap _ => _]) => v2m; last first.
      rewrite deref_V fnd_set not_fnd//deref_V.
      case: eqP => v2v; subst; first by rewrite (@in_fnd _ _ s).
      case: (fndP [fmap _ => _]) => v2r; last by rewrite not_fnd.
      rewrite ffunE valPE/= in_fnd//=/derefkv.
      move=> ->/=; rewrite not_in_deref//=fsetU0 fdisjoint1X.
      case: fndP => /=v2s.
        have:= fdisjointP A' _ vx'.
        by apply/contra => {}H; apply/codom_varsP; eexists _,v2s => //.
      by rewrite inE; case: eqP => ?; subst.
    rewrite in_fnd !odflt_Some ffunE valPE; simpl in v2m.
    have : v' \notin vars mgu.[v2m].
      have:= fdisjointP A _ vm'; apply: contra => Hx.
      by apply/codom_varsP; eexists _, v2m.
    move=> +{}M.
    have: v' \notin vars (deref r mgu.[v2m]).
      rewrite M; case: fndP => v2s/=.
        have:= fdisjointP A' _ vx'; apply: contra => Hx.
        by apply/codom_varsP; eexists _, v2s.
      rewrite inE; case: eqP => //?; subst.
      by rewrite vx' in v2s.
    rewrite -M.
    elim: (mgu.[v2m]) => //[v3|/=f Hf a Ha]; last first.
      by rewrite !inE => /norP[??]/norP[??]; rewrite Ha//Hf//.
    rewrite /derefkv !deref_V FmapE.fmapE// inE => + vv'.
    rewrite (@not_fnd _ _ fmap0)//.
    case: eqP => ?; subst => //; rewrite !deref_V fnd_set.
      by rewrite eqxx//not_fnd.
    rewrite eq_sym (negbTE vv').
    case: fndP => //v3r; [rewrite in_fnd | rewrite not_fnd//].
    rewrite ffunE valPE; simpl in * => vvr.
    by rewrite/derefkv not_in_deref//=fsetU0 fdisjoint1X.
   }
   move=> H.
   apply: is_mgu_deref_sigma => //.
   exists r => //.
Qed.


Lemma montanariPmgu b l s mgu: acyclic s -> disjoint_L s l ->
  montanari s b l = Some mgu -> mgu_help s mgu l.
Proof.
  move: mgu; montanari_ind s b l => mgu A//; cycle -1.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D M].
    have {IH M} := IH _ A _ M; rewrite disjoint_L_cons/= d2 d1 D.
    move=> /(_ isT).
    apply: mgu_help_cons_comm.
  - by move=> _ [<-]; apply: mgu_help_refl.
  - by rewrite disjoint_L_cons => /and3P[Dt _ Dl] M; apply/mgu_help_tt/IH.
  - rewrite disjoint_L_cons /=!fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 D] M.
    apply/mgu_help_app/IH; auto.
    by rewrite !disjoint_L_cons/=d1 d2 d3 d4.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M IH} := IH _ (acyclic_sigma_deref_sigma _ _ A) (disjoint_deref_sigma_deref_list A _ _ _) M.
    rewrite inE in vt.
    rewrite inE/= eq_sym => /(_ vt D1 D1 vt D3) IH.
    apply: mgu_help_cons_comm; rewrite !fdisjointX1 in D1, D2.
    by apply: mgu_help_deref_sigma IH; rewrite//(inE,fdisjointX1)//eq_sym.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M}IH := IH _ (acyclic_sigma_deref_sigma vt D2 A) (disjoint_deref_sigma_deref_list A D2 vt D3) M.
    by apply: mgu_help_deref_sigma IH; rewrite fdisjointX1 in D1. 
Qed.

Definition mgu m t1 t2 :=
  acyclic m /\ deref m t1 = deref m t2 /\ forall s, acyclic s -> deref s t1 = deref s t2 -> 
    exists s', acyclic s' /\ forall t, deref s' (deref m t) = (deref s t).

Lemma ren_empty t: ren fmap0 t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.

Lemma is_mgu0 s: acyclic s -> is_mgu fmap0 s.
Proof. by exists s => //t; rewrite deref_empty. Qed.

(*SNIPT: unif_correct *)
Lemma unify_correct t1 t2 s:
  unify t1 t2 fmap0 = Some s -> mgu s t1 t2.
(*ENDSNIPT: unif_correct *)
Proof.
  move=> U.
  have H := montanariPmgu acyclic_sigma0 (disjoint_Lempty _) U.
  rewrite !deref_empty in H; repeat split.
    by apply: unif_acyclic acyclic_sigma0 U.
    by have:= unify_P acyclic_sigma0 U.
  move=> s' A D.
  have:= H s' A; rewrite/=/unif_pair/map_prod1 D eqxx.
  move=> /(_ isT (is_mgu0 _)) [|r] //.
  by exists r.
Qed.

Print Assumptions mgu_help_deref_sigma.

(*SNIPT: unify_complete *)
Lemma unify_complete:
  forall t1 t2, (exists s, acyclic s /\ deref s t1 = deref s t2) -> exists s', unify t1 t2 fmap0 = Some s'.
(*ENDSNIPT: unify_complete *)
Proof.
  move=> t1 t2 [sx [H1 H2]].
  rewrite /unify/montanari_deref/montanari_pair.
  have:= exists_montanari acyclic_sigma0 (disjoint_Lempty _) (ex_intro _ sx _).
  move=> /(_ fset0 [::(deref fmap0 t1, deref fmap0 t2)] ).
  rewrite H1/= /unif_pair/map_prod1/= !deref_empty H2 eqxx fdisjointX0.
  move=> /(_ (And3 isT isT isT)).
  case M: montanari => [s'|]// _.
  by eexists.
Qed.

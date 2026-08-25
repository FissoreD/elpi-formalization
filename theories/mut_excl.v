From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars fresh unif.

Section good_mode.
  Definition arri t := if t is _ --i--> _ then true else false.

  Fixpoint all_mode dfl m :=
    match m with b _ => true | arr m _ r => (m == dfl) && all_mode dfl r end.

  Definition all_out := all_mode output.

  Fixpoint good_mode m :=
    match m with
    | b _ => true
    | arr input _ r => good_mode r
    | arr output _ r => all_out r
    end.

  Definition good_modes (s: sigT) := [forall x : domf s, good_mode s.[valP x]].

  Lemma all_mode_good_mode d l: all_mode d l -> good_mode l.
  Proof. elim: l => //= m f Hf a Ha /andP[/eqP->{m}]; destruct d => //. Qed.

  Lemma good_modes_in p sP (pP: p  \in domf sP):
    good_modes sP -> good_mode sP.[pP].
  Proof. by move=> GM; have:= forallP GM [`pP]; rewrite valPE. Qed.

  Lemma eat_ty_good_mode n m r:
    good_mode m -> eat_ty n m = Some r -> good_mode r.
  Proof.
    elim: n m r => //=[|n IH] m r; first by move=> + [<-].
    by case: m => //=m tl tr; case: m => [|/all_mode_good_mode]; apply: IH.
  Qed.

  Lemma good_modes_arri_H sP b f f' s m tf ta s': good_modes sP ->
    H u sP b f f' s = Some (arr m tf ta, s') ->
    arri ta -> m = input.
  Proof.
    move=> GM; elim: f f' m tf ta s' => //[p|f Hf a _][p'|//|f' a']//=m tf ta s'.
      case: eqP => //->; case: fndP => //pP[H _].
      have := good_modes_in pP GM; rewrite {}H.
      by case: ta => [|[]]//=; case: m => //.
    case H1: H => //[[[//|m' tf' ta'] s'']]; case: (_ s'') => //s'''[??] AI; subst.
    have /= := Hf _ _ _ _ _ H1.
    destruct m => //= _.
    have [_ _ [p[pP fp E]]] := HP H1.
    have /= := eat_ty_good_mode (good_modes_in pP GM) E.
    by destruct m' => //=; case: ta H1 AI E => //=[[]]//.
  Qed.
End good_mode.

Section mut_excl.
  Variable u : Unif.

  (* returns if all inputs can be unified *)
  (* inputs come before outputs *)
  (* outputs are neutral for this function *)
  Fixpoint H_head (sP:sigT) (q : Tm) (h: Tm) : option S :=
  match q,h with
  | Tm_P p, Tm_P p' => if p == p' then sP.[?p] else None
  | Tm_App f a, Tm_App f' a' =>
    if H_head sP f f' is Some (arr m _ r) then
      if (m == output) || lang.unify u f f' fmap0 then Some r
      else None
    else None
  | _, _ => None
  end.

  Lemma H_headP sP t1 t2 r: H_head sP t1 t2 = Some r -> 
    [/\ get_tm_hd t1 = get_tm_hd t2, term_arg t1 = term_arg t2 &
      exists p, exists2 pP : p \in sP, get_tm_hd t1 = inl p & eat_ty (term_arg t1) sP.[pP] = Some r]
    .
  Proof.
    elim: t1 t2 r => //=[p|f Hf a _] [p'|v|f' a']//=r.
      case: eqP => //<-; case: fndP => //=pP[<-]; split => //.
      by exists p, pP.
    case H: H_head => [[|m tl tr]|]//=.
    case: ifP => []// _ [<-{r}].
    have /=[Hx Hy [p [pP H1 H2]]] := Hf _ _ H.
    rewrite Hx Hy; split => //; rewrite -Hy -Hx.
    exists p, pP => //.
    move: H2; case: sP.[pP] => //=; first by case: term_arg.
    clear => md tf ta; apply: eat_ty_arr.
  Qed.

  Fixpoint select_head (sP:sigT) (q: Tm) (rules: list R) : seq R :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head sP q rules in
      if H_head sP q rule.(head) then rule :: tl else tl
    end.

  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    ~~ tm_is_det sig r.(head) ||
      all_but_last (fun x => has_cut_seq x.(premises)) (r :: select_head sig r.(head) rules).

  Fixpoint mut_excl_aux sig rules :=
    match rules with
    | [::] => true
    | x :: xs => mut_excl_head sig x xs && mut_excl_aux sig xs
    end.

  Definition mut_excl pr :=
    let: (fv, rules) := fresh_rules (fresh (v_prog pr.(rules))) pr.(rules) in
    good_modes pr.(sig) && mut_excl_aux pr.(sig) rules.

  Lemma callable_ren m hd p:
    get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. by elim: hd => //= [q|d|v|f Hf a Ha]. Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv mp hd).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename => /=; split => /callable_ren. Qed.

  Lemma is_det_cder s s1 c: tm_is_det s c -> tm_is_det s (deref s1 c).
  Proof. elim: c s => //=[p|f Hf a Ha] s; rewrite ?deref_P//. Qed.
End mut_excl.

Definition u := mk_Unif unify matching.

Lemma eat_ty_inp n t m t1 t2:
  eat_ty n t = Some (arr m t1 t2) ->
  good_mode t -> arri t2 -> m = input.
Proof.
  elim: n t m t1 t2 => [[//|]|n IH]//=.
    by move=> ??? m ? t [???]; subst; case: m => //=; case: t => //=[[]]//.
  by move=> [|[]]//= _ s m t1 t2 + /all_mode_good_mode ; apply: IH.
Qed.

Lemma fdisjoint_rem (K: choiceType) (qa qf:{fset K}) :
  (qa `\` qf) # qf.
Proof. by apply/fdisjointP => k; rewrite !inE => /andP[]. Qed.

Lemma mp_trans: transitive mp.
Proof.
  move=> b a c M1 M2; apply/forallP => -[x xa].
  have:= forallP M1 [`xa]; rewrite !valPE/=.
  case: fndP => //= xb/eqP[]; have:= forallP M2 [`xb].
  rewrite valPE/=; case: fndP => //xc/eqP[<-] <-.
  by rewrite derefxx//.
Qed.

Lemma idempotent_H sP fv q hd s1 r:
  idempotent s1 ->
    H u sP fv q hd s1 = Some r ->
      idempotent r.2.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a Ha] fv [p'|//|f' a']// s1 r.
    by case: eqP => //= _ A; case: fndP => //=pP[<-].
  move=> A.
  case H: H => [[[|[] tyl tyr] s1']|]//=.
    case M: matching => //= [s1''][?]; subst.
    by apply: matching_idempotent M; apply: Hf H.
  case M: unify => //= [s1''][?]; subst.
  by apply: unif_idempotent M; apply: Hf H.
Qed.

Lemma idempotent_select sP query rules s1 e:
  idempotent s1 ->
    e \in (select u sP query rules s1) ->
      idempotent e.1.
Proof.
  elim: rules query s1 e => //= -[hd bo] rs IH query s1 e AS/=.
  case H: H => [[ty s1']|]; last by apply: IH.
  rewrite in_cons => /orP[/eqP?|]; subst; last by apply: IH.
  by have := idempotent_H AS H.
Qed.

Lemma H_mp sP fv q hd s1 r: idempotent s1 ->
  H u sP fv q hd s1 = Some r -> mp s1 r.2.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a _] fv [p'|//|f' a']// s1 r.
    by case: eqP => //->; case: fndP => //= ? A[<-]; apply: mp_id.
  move=> A; case H: H => [[[|m tl tr] s']|]//=.
  case M: (_ s') => //=[{}r][<-]/=.
  have {}Hf := Hf _ _ _ _ A H.
  have A' := idempotent_H A H.
  have: mp s' r.
    by move: M; destruct m => /=/(montanari_mp A' (disjoint_L_deref _ _ A')) ->//.
  by apply: mp_trans.
Qed.

Lemma H_deref_eq sP fv q hd s1 r:
  idempotent s1 ->
    H u sP fv q hd s1 = Some r ->
      deref r.2 q = deref r.2 hd.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a _] fv [p'|//|f' a']// s1 r.
    by case: eqP => //-> A; case: fndP => //.
  move=> A.
  case H: H => [[[|m tl tr] s1']|]//=.
  case X: (_ s1') => //= [sx][?]; subst => /=.
  have /= A' := idempotent_H A H.
  have s1s1' := H_mp A H.
  have s1'sx: mp s1' sx.
    have M := montanari_mp A' (disjoint_L_deref _ _ A').
    by move: X; destruct m => /= /M.
  have MP := mp_trans s1s1' s1'sx.
  have /={}Hf := Hf _ _ _ _ A H.
  rewrite -(@derefxx s1')// Hf derefxx//.
  move: X; destruct m => /matchingP->//.
Qed.

Lemma H_ext1 sP froz t1 t2 s r: good_modes sP ->
  (domf s) # froz -> H u sP froz t1 t2 s = Some r ->
  arri r.1 -> (domf r.2) # froz.
Proof.
  move=> GM.
  elim: t1 t2 s r => //[p|f Hf a _] [p'|//|f' a']//= s r.
    case: eqP => //-> H; case: fndP => //=pP[<-]//=; rewrite /=?fdisjoint0X fsetU0//=.
  case H: H => [[[|m tf' tr'] sm]|]//=.
  move=> sfroz.
  case I: (_ sm) => //=[r'][?] AI; subst; simpl in *.
  have /=[hff haa [p'[pP hp E]]] := HP H.
  have ? := eat_ty_inp E (good_modes_in pP GM) AI; subst.
  rewrite/= in I *.
  have /={Hf} := Hf _ _ _ sfroz H isT.
  move=> {}Hf.
  have Ha := matching_ext1 I.
  by apply/(fdisjointWl Ha); rewrite fdisjointUX Hf/= fdisjoint_rem.
Qed.

Lemma H_matchingI sP v1 query head s1 r:
  idempotent s1 ->
  good_modes sP ->
  fdisjoint (domf s1) v1 ->
  H u sP v1 query head s1 = Some r -> arri r.1 ->
  matching v1 head query s1.
Proof.
  move=> A GM sq H AI.
  rewrite/matching/montanari_deref/montanari_pair.
  apply: exists_montanari => //.
    by rewrite disjoint_L_deref.
  exists r.2; split => //.
    by apply: idempotent_H H.
    have mp := H_mp A H.
    have:= H_deref_eq A H.
    rewrite/unifier/unif_pair/map_prod1/= => Hx.
    by rewrite !derefxx//=Hx eqxx.
  by apply: H_ext1 H _.
Qed.

Lemma get_input_vars2 sP fv q h s x:
  H u sP fv q h s = Some x -> (get_input_vars sP q).2 = Some x.1.
Proof.
  elim: q h s x => //=[p|f Hf a _][p'||f' a']//=s [ty s'].
    by case: eqP => //=->; case: fndP => //= ? [<-].
  case H: H => [[[|m tl tr] s'']|]//=.
  case M: (_ s'') => //=[r][??]; subst.
  have:= Hf _ _ _ H.
  by case X: get_input_vars => //=?; subst => /=.
Qed.

Lemma get_input_vars_vars_tm sP fv q h s r:
  good_modes sP ->
  H u sP fv q h s = Some r -> arri r.1 ->
  (get_input_vars sP q).1 = vars_tm q.
Proof.
  move=> GM; elim: q h s r => [p||f Hf a _]//=[p'||f' a']//= s r.
  case H: H => //=[[[|m tl tr] s']]//=.
  case X: (_ s') => //=[s''][?]; subst.
  case: tr H => //[[] tl' tr']//= H' _.
  have [_ _ [p [pP G E]]] := HP H'.
  have ? := eat_ty_inp E (good_modes_in pP GM) isT; subst.
  have /= := Hf _ _ _ H' isT.
  case IV: get_input_vars => //=[fv' ty'] ?; subst.
  by have:= get_input_vars2 H'; rewrite IV => /=?; subst.
Qed.

Lemma get_input_vars_sub sP query:
  (get_input_vars sP query).1 `<=` vars query.
Proof.
  elim: query => //= f + a _.
  case: get_input_vars => fv s/= H.
  have {}H:= fsubset_trans H (fsubsetUl _ (vars a)).
  by case: s => [[|[]]|]//= _ _; rewrite fsubUset//= H//=fsubsetUr.
Qed.

Lemma SHS sP fv query hd2 hd1 (s1 s2:Sigma):
  good_modes sP ->
  idempotent s1 -> idempotent s2 ->
  fdisjoint (domf s1) fv ->
  fdisjoint (domf s2) fv ->
  (get_input_vars sP query).1 `<=` fv ->
  [disjoint vars_sigma s1 & vars hd2] -> 
  [disjoint vars_sigma s2 & vars hd1] -> 
  [disjoint vars hd1 & vars hd2] ->
  [disjoint vars query & vars hd1] ->
  [disjoint vars query & vars hd2] ->
  [disjoint domf s1 & vars query] ->
  [disjoint domf s2 & vars query] ->
  H u sP fv query hd1 s1 ->
  H u sP fv query hd2 s2 ->
  H_head u sP hd1 hd2.
Proof.
  move=> GM A1 A2  s1fv s2fv.
  elim: query hd1 hd2 => //=[p|f Hf a _];
  move=> [p1|v1|f1 a1]//[p2|v2|f2 a2]//=.
    move=> _ _ _ _ _ _ _ _; case: eqP => // <-; case: eqP => //->; case: fndP => //=.
  move=> IF.
  rewrite 2!fdisjointXU => /andP[V1 V2] /andP[V3 V4].
  rewrite ?fdisjointUX !fdisjointXU.
  move=> /andP[/andP[f1f2 f1a2] /andP[a1f2 a1a2]].
  move=> /andP[/andP[ff1 fa1] /andP[af1 aa1]].
  move=> /andP[/andP[ff2 fa2] /andP[af2 aa2]].
  move=> /andP[s1f s1a] .
  move=> /andP[s2f s2a] .
  case H1 : H => //=[[[//|m1 tf1 ta1] s1']].
  case H2 : H => //=[[[//|m2 tf2 ta2] s2']].
  have [hh1 ha1 [p[pP hf1 he]]] := HP H1.
  have:= HP H2.
  rewrite hh1 ha1 => -[hh2 ha2 [p'[pP']]].
  rewrite -hh1 hf1 => /esym [?]; subst.
  rewrite (bool_irrelevance pP' pP) -ha1 he => -[???]; subst.
  have fv2sub : (get_input_vars sP f).1 `<=` fv.
    by move: IF; apply: fsubset_trans => //=; case: get_input_vars => //= ? [[|[]]|]//=; rewrite fsubsetUl.
  have {Hf} := Hf _ _ fv2sub V1 V3 f1f2 ff1 ff2 s1f s2f (isSomeP H1) (isSomeP H2).
  case HH: H_head => //=[ty'] _.
  have [Hx Hy [p'[{}pP']]] := H_headP HH.
  rewrite -hh1 hf1 => -[?]; subst.
  rewrite -ha1 (bool_irrelevance pP' pP) he => -[?]; subst.
  destruct m2 => //=.
  rewrite ifT => //.
  have:= forallP GM [`pP]; rewrite valPE => GM'.
  have /= Hs := H_matchingI A1 GM s1fv H1 isT.
  have /= Hr := H_matchingI A2 GM s2fv H2 isT.
  rewrite !(fdisjoint_sym (vars_tm f)) in ff1, ff2.
  have ivf1 := get_input_vars_vars_tm GM H1 isT.
  rewrite ivf1 in fv2sub.
  by apply: matching_unify_transP Hs Hr => //.
Qed.

Lemma HSH sP rules hd query s: 
  good_modes sP ->
  idempotent s ->
  [disjoint domf s & vars_tm query] ->
  [disjoint vars_tm hd & v_prog rules] ->
  [disjoint vars_tm query & v_prog rules] ->
  [disjoint vars_tm query & vars_tm hd] ->
  [disjoint vars_sigma s & v_prog rules] ->
  [disjoint vars_sigma s & vars_tm hd] ->
  H u sP (get_input_vars sP query).1 query hd s ->
  select_head u sP hd rules = [::] ->
  select u sP query rules s = [::].
Proof.
  move=> GM.
  elim: rules query s hd => //=-[hd bo] rs IH/= query s h' AS sq.
  rewrite !v_prog_cons /varsU_rhead /varsU_rprem/=.
  rewrite !fdisjointXU -!andbA.
  move=> /and3P[h'h h'b h'r] /and3P[qh qb qr] qh' /and3P[sh sb sr sh'] H1.
  case HH: H_head => //= S1.
  have {IH} := IH _ _ _ AS sq h'r qr qh' sr sh' H1 S1.
  case S: select => //=?; subst.
  case H2: H => [[ty s']|]//=.
  have {}HH := isNoneP HH.
  exfalso; apply: negP HH; rewrite negbK.
  have sq' := fdisjointWr (get_input_vars_sub sP _) sq.
  apply: SHS H1 (isSomeP H2) => //=.
Qed.

Lemma H_head_ren_aux sP hd q (x y:renaming_for hd) (z w: renaming_for q):
  [disjoint codomf z & codomf x] ->
  [disjoint codomf w & codomf y] ->
  (H_head u sP (ren z q) (ren x hd)) = H_head u sP (ren w q) (ren y hd).
Proof.
  move: x y z w => [[x/= Ix Dx] Vx] [[y/= Iy Dy] Vy][[z/= Iz Dz] Vz][[w/= Iw Dw] Vw]/= D1 D2.
  elim: q hd Vx Vy Vz Vw => //=[p|f Hf a Ha][p'|//|f' a']//=.
  rewrite !fsubUset => /andP[fx' ax'] /andP[fy' ay'] /andP[fz az] /andP[fw aw].
  have {Hf} := Hf f' fx' fy' fz fw.
  case: H_head => [s'|]//=; case: H_head => [s|]//=[?]; subst.
  case: s => //=-[]//=_ s.
  have ->// : isSome (unify (ren z f) (ren x f') fmap0) = isSome (unify (ren w f) (ren y f') fmap0).
  have H: vars (ren z f) # vars (ren x f').
    apply: fdisjointWl (vars_tm_ren_sub fz) _.
    by apply: fdisjointWr (vars_tm_ren_sub _) _. 
  have/=:= @unif_ren f f' (mk_renfA Ix Dx fx') (mk_renfA Iy Dy fy') (mk_renfA Iz Dz fz) (mk_renfA Iw Dw fw) H.
  case U1: unify => //=; first by move=> /(_ isT)->.
  have H': vars (ren w f) # vars (ren y f').
    apply: fdisjointWl (vars_tm_ren_sub fw) _.
    by apply: fdisjointWr (vars_tm_ren_sub _) _.
  have/=:= @unif_ren f f' (mk_renfA Iy Dy fy') (mk_renfA Ix Dx fx') (mk_renfA Iw Dw fw) (mk_renfA Iz Dz fz) H'.
  by rewrite U1; case: unify => // ?/(_ isT).
Qed.

Lemma fresh_tm_inj_ fv (m:{fmap V -> V}) t:
  fresh (codomf m) <= fv ->
   injectiveb m -> injectiveb (fresh_tm fv m t).2.
Proof.
  elim : t m fv => //=[v|f Hf a Ha] m fv F I; last first.
    rewrite push; apply/Ha/Hf => //.
    apply/fresh_subc => //.
  case: ifP => vm//; apply/injectiveP => -[x xP]-[y yP].
  rewrite !ffunE ![val _]/= => H1; apply/val_inj => /=.
  move: xP yP H1; rewrite !inE.
  case: eqP => xv/= xm; case: eqP => yv/= ym; subst => //.
    by rewrite in_fnd => H; have:= fresh_sub_notin F => /codomfP[]; exists y; rewrite in_fnd H.
    by rewrite in_fnd => H; have:= fresh_sub_notin F => /codomfP[]; exists x; rewrite in_fnd-H.
  by rewrite !in_fnd// => /(injectiveP _ I)[].
Qed.

Lemma fresh_tm_inj0 n t: injectiveb (fresh_tm n.+1 fmap0 t).2.
Proof. by apply/fresh_tm_inj_; rewrite (injectiveb0,codomf0)//freshP0. Qed.

Lemma good_ren_fresh n q: fresh (vars q) <= n -> renaming_forP q (fresh_tm n fmap0 q).2.
Proof.
  move=> H.
  rewrite/renaming_forP; split.
    by rewrite fresh_tm_inj_//(injectiveb0,codomf0)//freshP0; destruct n.
  rewrite (fsubset_trans _ (fresh_tm_sub1 _ _ _))//.
  split => //.
  apply: (@fresh_tm_idempotent 0); rewrite//?(codomf0,idempotent_ren0,fdisjointX0,fsubsetUl)//.
  by rewrite/sum_mt domf0 codomf0 !fsetU0 !freshPU freshP1 H andbT; destruct n.
Qed.

Definition min_maxS (s:{fset V}) m M :=
  forall x, IV x \in s -> m <= x < M.

Lemma min_max_fresh_tm r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_tm M r q in
  min_maxS (codomf x.2) m x.1.
Proof.
  elim: q M r => /=[p|v|f Hf a Ha] M r// mm MM; last by (rewrite push; apply/Ha/Hf; rewrite//(leq_trans mm)//fresh_sub).
  case: fndP => vr//=; rewrite codomf_setN//.
  move=> x; rewrite 2!inE; case: eqP => [[->]|]; first by rewrite mm/=.
  by move=> xm H; have /andP[->/leq_trans->]:= MM x H.
Qed.

Lemma min_max_fresh_atom r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_atom M r q in
  min_maxS (codomf x.1.2) m x.1.1.
Proof. by case: q => //=t mm MM; rewrite !push/=; apply: min_max_fresh_tm. Qed.

Lemma min_max_fresh_atoms r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_atoms M r q in
  min_maxS (codomf x.1.2) m x.1.1.
Proof.
  elim: q M r => //=[x xs IH] M r// mm MM; rewrite !push/=.
  by apply/min_max_fresh_atom/IH/MM/mm/leq_trans/fresh_atoms_sub.
Qed.

Lemma min_maxP s:
  min_maxS s 0 (fresh s).
Proof.
  move=> x xs; rewrite leq0n/=; case: (boolP (_ < _)) => //=.
  by rewrite -leqNgt => /fresh_sub_notin; rewrite xs.
Qed.

Lemma min_max_fresh_tm0 fv q:
  let x := fresh_tm fv fmap0 q in
  min_maxS (codomf x.2) fv x.1.
Proof.
  move=> H/=.
  have MM : min_maxS (codomf fmap0) fv fv by move=> x; rewrite /= codomf0.
  by have := @min_max_fresh_tm fmap0 fv fv q (leqnn _) (MM _).
Qed.

Lemma min_maxU a b m M:
  min_maxS a m M -> min_maxS b m M -> min_maxS (a `|` b) m M.
Proof. by move=> M1 M2 x; rewrite inE => /orP[/M1|/M2]. Qed.

Lemma min_max_fresh_rules fv r:
  let x := fresh_rules fv r in
  min_maxS (v_prog x.2) fv x.1.
Proof.
  elim: r fv => //=r rs IH m; rewrite !push/= v_prog_cons.
  apply: min_maxU; last first.
    move=> x H; have /andP[->/= Hx] := IH m x H.
    by apply/leq_trans/fresh_rule_sub.
  set X:= (fresh_rules _ _).1.
  rewrite/fresh_rule; case: r => h b; rewrite /varsU_rhead/varsU_rprem !push/=.
  set Y:= fresh_tm _ _ _.
  apply: min_maxU .
    have/= H:= @min_max_fresh_tm0 X h.
    rewrite -/Y in H.
    move=> x y.
    have:= vars_tm_ren_sub (fresh_tm_sub1 X fmap0 h).
    rewrite-/Y => Hx.
    have /andP[Hl Hr] := H _ (fsubsetP Hx _ y).
    apply/andP; split; last first.
      by apply/leq_trans/fresh_atoms_sub.
    apply/leq_trans/Hl/fresh_rules_sub.
  elim: b => //-[|t]/= xs {}IH; rewrite !push/=vars_atoms_cons/=.
    by rewrite fset0U.
  apply: min_maxU; last first.
    move=> x H.
    have/andP[-> {}IH]/=:= IH x H.
    apply: leq_trans IH _.
    by apply/leq_trans/fresh_sub.
  clear IH.
  set F := fresh_atoms _ _ _.
  set Z := fresh_tm _ _ _.
  have xx: m <= F.1.1.
    apply/leq_trans/fresh_atoms_sub/leq_trans/fresh_sub/fresh_rules_sub.
  have yy: min_maxS (codomf F.1.2) m F.1.1.
    have kk : m <= Y.1 by apply/leq_trans/fresh_sub/fresh_rules_sub.
    have zz : min_maxS (codomf Y.2) m Y.1.
      apply/min_max_fresh_tm; first by apply/fresh_rules_sub.
      by rewrite codomf0//.
    have/= H := @min_max_fresh_atoms Y.2 m Y.1 xs kk zz.
    rewrite -/F in H.
    by move=> x Hx; have /andP[->{}H] := H x Hx.
  have/= H:= @min_max_fresh_tm F.1.2 m F.1.1 t xx yy.
  rewrite-/Z/= in H.
  move=> x y.
  have:= vars_tm_ren_sub (fresh_tm_sub1 F.1.1 F.1.2 t).
  rewrite-/Z => Hx.
  by have/andP[->/=->] := H _ (fsubsetP Hx _ y).
Qed.

Lemma min_max_S_disj s1 s2 m1 m2 M1 M2:
  M1 <= m2 ->
  min_maxS s1 m1 M1 ->
  min_maxS s2 m2 M2 ->
  s1 # s2.
Proof.
  move=> mm H1 H2; apply/fdisjointP => -[x] xs1.
  case: (boolP (_ \in _)) => //xs2.
  have /andP[m1x xM1] := H1 _ xs1.
  have /andP[m2x xM2] := H2 _ xs2.
  have {xM1} xm2 := leq_trans xM1 mm.
  have:= leq_trans xm2 m2x.
  by rewrite ltnn.
Qed.

Lemma H_head_ren sP fv1 fv2 t xs fx fy q:
  fresh (vars q) <= fx -> fresh (vars q) <= fy ->
  fresh (vars t) <= (fresh_rules fv1 xs).1 ->
  fresh (vars t) <= (fresh_rules fv2 xs).1 ->
  (lang.rename (fresh_rules fv1 xs).1 fmap0 t).1.1 <= fx ->
  (lang.rename (fresh_rules fv2 xs).1 fmap0 t).1.1 <= fy ->
  H_head u sP ((lang.rename fx fmap0 q).2) ((lang.rename (fresh_rules fv1 xs).1 fmap0 t).2) =
  H_head u sP ((lang.rename fy fmap0 q).2) ((lang.rename (fresh_rules fv2 xs).1 fmap0 t).2).
Proof.
  move=> qx qy tr1 tr2.
  rewrite/lang.rename/=.
  set X:= fresh_tm _ _ _.
  set Y:= fresh_tm _ _ _.
  set W:= fresh_tm _ _ _.
  set Z:= fresh_tm _ _ _.
  move=> H1 H2/=.
  replace W.2 with (ren_map (renaming_forPM (good_ren_fresh qx))) => //.
  replace Z.2 with (ren_map (renaming_forPM (good_ren_fresh qy))) => //.
  replace X.2 with (ren_map (renaming_forPM (good_ren_fresh tr1))) => //.
  replace Y.2 with (ren_map (renaming_forPM (good_ren_fresh tr2))) => //.
  apply: H_head_ren_aux; rewrite//=-/X-/W-/Y-/Z.
    have /= := @min_max_fresh_tm0 fx q.
    have /= := @min_max_fresh_tm0 (fresh_rules fv1 xs).1 t.
    rewrite -/X-/W fdisjoint_sym.
    by apply/min_max_S_disj.
  have /= := @min_max_fresh_tm0 fy q.
  have /= := @min_max_fresh_tm0  (fresh_rules fv2 xs).1 t.
  rewrite -/Y-/Z fdisjoint_sym.
  by apply/min_max_S_disj.
Qed.

Lemma callable_rename1 p fv1 hd mp: 
  (get_tm_hd (lang.rename fv1 mp hd).2 == inl p) = (get_tm_hd hd == inl p).
Proof.
  case:eqP; case:eqP => //= H1 H2.
    by move/callable_rename: H1 => /(_ _ _ H2).
  by have:= H2 (proj2 (callable_rename _ _ _ _) _); auto.
Qed.

Lemma fresh_tm_idempotent0' vt t:
  fresh (vars t) <= vt -> idempotent_ren (fresh_tm vt fmap0 t).2.
Proof. by move=> H; rewrite (@fresh_tm_idempotent0 0)///sum_mt domf0 codomf0 !fsetU0 freshPU H andbT freshP1; destruct vt. Qed.

Lemma select_head_ren sP rs fx fy fv1 fv2 hd:
  let FRS1 := fresh_rules fv1 rs in
  let FRS2 := fresh_rules fv2 rs in
  fresh (v_prog rs) <= fv1 -> fresh (v_prog rs) <= fv2 ->
  fresh (vars hd) <= fv1 ->  fresh (vars hd) <= fv2 ->
  FRS1.1 <= fx ->  FRS2.1 <= fy ->
  select_head u sP ((lang.rename fx fmap0 hd).2) FRS1.2 = [::] ->
  select_head u sP ((lang.rename fy fmap0 hd).2) FRS2.2 = [::].
Proof.
  rewrite/=.
  elim: rs fv1 fv2 => //= x xs IH fv1 fv2.
  rewrite !push !v_prog_cons !freshPU -!andbA/=.
  move => /and3P[h1 b1 r1] /and3P[h2 b2 r2] v1 v2/= F1 F2.
  rewrite !head_fresh_rule.
  case H: H_head => //= S.
  rewrite (IH fv1)//; only 2,3: by apply: (leq_trans (fresh_rule_sub _ _)); eassumption.
  replace (H_head _ _ _ _) with (@None (lang.S)) => //.
  rewrite-H.
  have Fx: fresh (vars hd) <= fx.
    by apply/leq_trans/F1/leq_trans/fresh_rule_sub/leq_trans/fresh_rules_sub.
  have Fy: fresh (vars hd) <= fy.
    by apply/leq_trans/F2/leq_trans/fresh_rule_sub/leq_trans/fresh_rules_sub.
  have renx : renaming_forP hd (fresh_tm fx fmap0 hd).2.
    repeat split.
      by apply: fresh_tm_inj_ injectiveb0; rewrite codomf0 freshP0; destruct fx.
      by apply: fresh_tm_idempotent0'.
    by apply: fresh_tm_sub1.
  have renz : renaming_forP (head x) (fresh_tm (fresh_rules fv1 xs).1 fmap0 (head x)).2.
    repeat split.
      by apply: fresh_tm_inj_ injectiveb0; rewrite codomf0 freshP0; apply/leq_trans/fresh_rules_sub; destruct fv1.
      by apply/fresh_tm_idempotent0'/leq_trans/fresh_rules_sub.
    by apply/fsubset_trans/fresh_tm_sub1.
  have reny : renaming_forP hd (fresh_tm fy fmap0 hd).2.
    repeat split.
      by apply: fresh_tm_inj_ injectiveb0; rewrite codomf0 freshP0; destruct fy.
      by apply: fresh_tm_idempotent0'.
    by apply: fresh_tm_sub1.
  have renw : renaming_forP (head x) (fresh_tm (fresh_rules fv2 xs).1 fmap0 (head x)).2.
    repeat split.
      by apply: fresh_tm_inj_ injectiveb0; rewrite codomf0 freshP0; apply/leq_trans/fresh_rules_sub; destruct fv2.
      by apply/fresh_tm_idempotent0'/leq_trans/fresh_rules_sub.
    by apply/fsubset_trans/fresh_tm_sub1.
  have ->//= := @H_head_ren_aux sP (head x) hd (renaming_forPM renz) (renaming_forPM renw) (renaming_forPM renx) (renaming_forPM reny).
    have /= := @min_max_fresh_tm0 fx hd.
    have /= := @min_max_fresh_tm0 (fresh_rules fv1 xs).1 (head x).
    rewrite fdisjoint_sym.
    apply/min_max_S_disj.
    apply/leq_trans/F1; destruct x; rewrite/fresh_rule !push/=.
    by apply/leq_trans/fresh_atoms_sub.
  have /= := @min_max_fresh_tm0 fy hd.
  have /= := @min_max_fresh_tm0 (fresh_rules fv2 xs).1 (head x).
  rewrite fdisjoint_sym.
  apply/min_max_S_disj.
  apply/leq_trans/F2; destruct x; rewrite/fresh_rule !push/=.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma mut_exclP p fv c s1:
  mut_excl u p -> 
    tm_is_det p (deref s1 c) ->
      all_but_last (fun x => has_cut_seq x.2) (bc u p fv c s1).2.
Proof.
  rewrite/bc.
  case: p => [rs sP]/=+TD.
  case: ifP => //= /negbFE AS.
  rewrite/mut_excl !push/=.
  move=> /andP[GM].
  set vp := fresh (v_prog rs).
  have:= leqnn vp; rewrite{1}/vp.
  set va := fresh (_ `|` _).
  have:= leqnn va; rewrite{1}/va.
  move: va vp.
  elim: rs => [|[hd bo] rs IH]//= va vp.
  rewrite !push !v_prog_cons/= (fsetUC _ (v_prog _)) fsetUA freshPU /varsU_rhead/varsU_rprem/= (freshPU (vars _)) => /and3P[S1 Sh Sb].
  rewrite !freshPU => /and3P[S2 Sh' Sb'].
  move=> /andP[+ ME].
  have {}IH := IH _ _ S1 S2 ME.
  rewrite/mut_excl_head/fresh_rule !push/= !has_cut_seq_fresh/=.
  case H: H => [s2|]//=; rewrite !push/= {}IH andbT/=.
  move: TD; rewrite/tm_is_det.
  case X: get_tm_hd => [p|]//=; case: fndP => //pP DP.
  rewrite (proj2 (callable_rename _ hd p _))//; last first.
    apply/eqP.
    have [Hx Hy [p' [pP']]] := HP H.
    by move /eqP: Hx; rewrite X eq_sym callable_rename1.
  rewrite in_fnd DP/= has_cut_seq_fresh.
  case has_cut_seq; first by case select.
  case S: select_head => //=.
  have ->// : (select u sP (deref s1 c) (fresh_rules va rs).2 s1) = [::].
  apply: HSH (isSomeP H) _ => //; cycle -1.
    move: S.
    set n := fst _; set m := fst _.
    apply: select_head_ren => //.
    by move: S1; rewrite !freshPU -!andbA => /and5P[]//.
  - by apply: idempotent_deref_disjoint.
  - apply: fdisjointWl (ren_mp (fresh_tm_sub1 _ _ _)) _.
    rewrite fdisjoint_sym.
    apply: min_max_S_disj; cycle -2.
      apply: min_max_fresh_rules.
      apply : @min_max_fresh_tm0 _ hd.
    by [].
  - apply: min_max_S_disj; last first.
      apply: min_max_fresh_rules.
      apply: min_maxP.
    apply/leq_trans/S1.
    by rewrite !freshUU !leq_max leqnn orbT.
  - apply: fdisjointWr (ren_mp (fresh_tm_sub1 _ _ _)) _.
    apply: min_max_S_disj; cycle -2.
      apply: min_maxP.
      apply: min_max_fresh_tm0.
    apply/leq_trans/fresh_rules_sub/leq_trans/S1.
    by rewrite !freshUU !leq_max leqnn orbT.
  - apply: min_max_S_disj; cycle -2.
      apply: min_maxP.
      apply: min_max_fresh_rules.
    apply/leq_trans/S1.
    by rewrite -2!fsetUA 2!freshUU !leq_max leqnn orbT.
  - apply: fdisjointWr (ren_mp (fresh_tm_sub1 _ _ _)) _.
    apply: min_max_S_disj; cycle 1.
      apply: min_maxP.
      apply: min_max_fresh_tm0.
    apply/leq_trans/fresh_rules_sub/leq_trans/S1.
    by rewrite -fsetUA 2!freshUU !leq_max leqnn orbT.
Qed.

Print  Assumptions  mut_exclP.


Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

Definition all_cut p :=  all_rs_cut (rules p).

Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

Lemma all_cut_select_head sP t rs fv:
  all_rs_cut rs ->
  all_rs_cut (select_head u sP t (fresh_rules fv rs).2).
Proof.
  elim: rs fv t => //=[[hd bo]]/= rs IH fv t /andP[H1 H2].
  rewrite !push/= head_fresh_rule/=; case: ifP; last by eauto.
  by rewrite/=/fresh_rule !push/= IH//has_cut_seq_fresh /= H1.
Qed.

Lemma all_cut_mut_excl p: good_modes p.(sig) -> all_cut p -> mut_excl u p.
Proof.
  rewrite/all_cut/mut_excl push/= => ->/=.
  case: p => /= r s.
  set n := fresh _; have:= leqnn n; rewrite {1}/n; move: n.
  elim r => //= [[hd bo]] rs/= IH n; rewrite !push/= v_prog_cons/=/varsU_rhead/varsU_rprem/=.
  rewrite !freshPU -andbA => /and3P[hn bn rn] /andP[cb cr].
  rewrite IH//andbT/fresh_rule/mut_excl_head !push/=.
  set R := ren _ _.
  case X: tm_is_det => //=.
  case S: select_head => //= [r' rs'].
  rewrite has_cut_seq_fresh /=cb.
  have:= all_cut_select_head s R n cr.
  by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
Qed.



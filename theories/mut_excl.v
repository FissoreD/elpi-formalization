From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif fresh.

Section mut_excl.
  Variable u : Unif.

  Fixpoint H_head inp ml (q : Tm) (h: Tm) : bool :=
    match ml,q,h with
    | 0, Tm_P c, Tm_P c1 => c == c1
    | ml.+1, (Tm_App q a1), (Tm_App h a2) => 
      ((inp != 0) || u.(unify) a1 a2 fmap0) && H_head inp.-1 ml q h
    | _, _, _ => false
    end.
  
  Fixpoint select_head (query : Tm) inp modes (rules: list R) : (seq R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head query inp modes rules in
      if H_head inp modes query rule.(head) then rule :: tl else tl
    end.
  
  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    let query := r.(head) in
    match get_tm_hd query with
      | inl kp =>
        match sig.[? kp] with 
          | Some (inp, sig) => 
            if is_det_sig sig then 
              let md := (get_modes_rev query sig) in
              let rs := select_head query (md - inp) md rules in
              all_but_last (fun x => has_cut_seq x.(premises)) (r::rs)
            (* ignoring checking for vars *)
            else true
          (*a callable against a rigid term non in sig OK: failure at runtime*)
          | None => true
          end
      | _ => true (*OK: vars and data heads correspond to runtime failures *)
    end.

  Fixpoint mut_excl_aux sig rules :=
    match rules with
    | [::] => true
    | x :: xs => mut_excl_head sig x xs && mut_excl_aux sig xs
    end.

  Definition mut_excl pr :=
    let: (fv, rules) := fresh_rules fset0 pr.(rules) in
    mut_excl_aux pr.(sig) rules.


     (* sufficient modes length for callable t *)
  Fixpoint suff_mode (t:Tm) (m:nat) :=
    match m, t with
    | 0, Tm_P _ => true
    | m.+1, Tm_App x _ => suff_mode x m
    | _, _ => false
    end.

  Lemma H_suff_mode inp l q fv hd s1 s2 md:
    H u inp l q (rename fv hd md).2 s1 = Some s2 -> suff_mode hd l.
  Proof.
    rewrite/rename !push/=.
    move: (fresh_tm _ _ _) => -[]/= _.
    elim: l inp q hd s1 s2 {fv md} => //=.
      move=> _ []//=p hd s1 s2 b; case: eqP => ///esym/[dup].
      by move=>/ren_isP[p'->]/=.
    move=> m IH inp []//=f1 a1 hd s1 s2 fv.
    case R: ren => //=[f a].
    move: (R) => /ren_isApp[f2[a2?]]/=; subst; move: R.
    rewrite ren_app => -[<- _].
    case H: H => //= _.
    apply: IH H.
  Qed.

  (* Definition callable t := match get_tm_hd t with inl t => Some t | _ => None end. *)

  Lemma H_callable inp m t1 t2 s1 s2 p:
    H u inp m t1 t2 s1 = Some s2 ->
    get_tm_hd t1 = inl p ->
    get_tm_hd t2 = inl p.
  Proof.
    elim: m inp t1 t2 s1 s2 p => //=.
      by move=> inp []//= p []//p' s1 s2; case: eqP => //-[->].
    move=> m IH inp []//f1 a1 []//f2 a2 s1 s2 p.
    case H: H => //= _.
    by apply: IH H.
  Qed.

  Lemma callable_ren m hd p: get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. elim: hd => //= v; rewrite ren_V//. Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed.

  Lemma is_det_cder s s1 c: tm_is_det s c -> get_tm_hd (deref s1 c) = get_tm_hd c.
  Proof. by elim: c s. Qed.

  Lemma is_det_lookup p c s (pP: p \in domf s):
    get_tm_hd c = inl p -> tm_is_det s c -> is_det_sig s.[pP].2.
  Proof. by elim: c p s pP => //=p1 p2 s pP [->]; rewrite/tm_is_det/=in_fnd//. Qed.

  Lemma count_tm_ag_deref s c p: 
    get_tm_hd c = inl p -> count_tm_ag (deref s c) = count_tm_ag c.
  Proof. by elim: c p s => //=f Hf a Ha p s H; rewrite (Hf p)//. Qed.

  Lemma get_modes_rev_deref c p s1 s: 
    get_tm_hd c = inl p -> get_modes_rev (deref s1 c) s = get_modes_rev c s.
  Proof. by move=> H; rewrite/get_modes_rev/sigtm_rev/sigtm (count_tm_ag_deref _ H)//. Qed.

  Lemma count_tm_ag_H inp d1 d2 s1 s2 m p:
    H u inp m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      count_tm_ag d1 = count_tm_ag d2.
  Proof.
    elim: d1 d2 s1 s2 inp m p => //=[p|f Hf a Ha] d2 s1 s2 inp m l.
      by case: m => //=; case: eqP => //<-.
    case: m => //= m; case: d2 => //= f1 a1; case H: H => //[s1']/= M C.
    by f_equal; apply: Hf H C.
  Qed.

  Lemma get_modes_rev_H inp d1 d2 s1 s2 m l p:
    H u inp m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      get_modes_rev d1 l = get_modes_rev d2 l.
  Proof. by move=> H C; rewrite/get_modes_rev/sigtm_rev/sigtm (count_tm_ag_H H C). Qed.

  Lemma disjointH m f f1 s1 s1': 
    [disjoint vars_tm f & domf s1] ->
    [disjoint vars_tm f & vars_tm f1] ->
      H u 0 m f f1 s1 = Some s1' ->
        exists x, domf s1' = domf s1 `|` x /\ x `<=` vars_tm f1.
  Proof.
    elim: m f f1 s1 s1' => //=.
      move=> []//= f a f1 s1 s1' ; case: eqP => //=<-/= _ [<-].
      by exists fset0; rewrite fsetU0.
    move=> n IH f f1 s1 s1'.
    case: f => //=f2 a2; case: f1 => //=f3 a3/=.
    rewrite disjointUl => /andP[D1 D2].
    rewrite fdisjointXU !fdisjointUX.
    move=> /andP[/andP[D6 D7] /andP[D8 D9]].
    case H: H => //=[s1''] M.
    have [x {IH}[H1 H2]] := IH _ _ _ _ D1 D6 H.
    have HH : [disjoint vars_tm a2 & domf s1''].
      rewrite H1 disjointUr D2.
      by apply/disjoint_sub/H2.
    have [y [H3 H4]] := matching_disj HH D9 M.
    rewrite H3 H1; exists (x `|` y).
    rewrite fsetUA; split => //.
    by rewrite fsubUset !fsubsetU//(H2,H4)//orbT.
  Qed.

  Lemma SHS inp m c hd2 hd1 (s1 s2:Sigma):
    [disjoint vars_tm hd1 & vars_tm hd2] ->
    [disjoint vars_tm c & vars_tm hd1] ->
    [disjoint vars_tm c & vars_tm hd2] ->
    [disjoint (vars_tm c) & (domf s1)] ->
    H u inp m c hd1 s1 = Some s2 ->
    H_head inp m hd1 hd2 = false ->
    H u inp m c hd2 s1 = None.
  Proof.
    elim: m inp c hd1 hd2 s1 s2 => //=.
      move=> inp []//=p hd1 hd2 s1 s2 _ _ _ _.
      case: eqP => //<-[->]; case: hd2 => //=[]p1/eqP; case: eqP; congruence.
    move=> m IH inp c h1 h2 s1 s2.
    case: c => //=f a; case: h1 => //=f1 a1; case: h2 => //=f2 a2.
    rewrite !fdisjointUX !fdisjointXU.
    move=> /andP[/andP[D1 D2] /andP[D3 D4]].
    move=> /andP[/andP[D5 D6] /andP[D7 D8]].
    move=> /andP[/andP[D9 D10] /andP[D11 D12]].
    move=> /andP[D13 D14].
    case H1: H => //=[s1'].
    case HH: H_head; rewrite (andbT,andbF)//=; last first.
      by rewrite (IH _ _ _ _ _ _ _ _ _ _ H1 HH)//=.
    case: eqP => //= INP.
    case H2: H => //=[s1''] M U; subst; simpl in HH, H1, H2.
    have Dy: [disjoint vars_tm a & domf s1''].
      have [x [Hx Hy]] := disjointH D13 D9 H2.
      rewrite Hx disjointUr D14.
      by apply/disjoint_sub/Hy.
    have Dx: [disjoint vars_tm a & domf s1'].
      have [x [Hx Hy]] := disjointH D13 D5 H1.
      rewrite Hx disjointUr D14.
      by apply/disjoint_sub/Hy.
    have {}M := isSomeP M.
    have {}M := matching_subst1 Dx M.
    have {}M := matching_monotone M.
    case M2: matching => //=.
    have {}M2 := isSomeP M2.
    have {}M2 := matching_subst1 Dy M2.
    have {}M2 := matching_monotone M2.
    have {}U1:= match_unif M.
    have {}U2:= match_unif M2.
    rewrite unif_sym in U1.
    by rewrite (unif_trans U1 U2) in U.
  Qed.

  Lemma acyclic_sigma_dis c s:
    acyclic_sigma s -> [disjoint vars_tm (deref s c) & domf s].
  Proof.
    move=> H; elim: c => //=; only 1, 2: by rewrite fdisjoint0X.
      move=> v; case: fndP => //= vs; last by rewrite fdisjoint1X.
      rewrite fdisjoint_sym.
      apply: disjoint_sub H _.
      apply/codom_vars_sub.
    by move=> f Hf a Ha; rewrite disjointUl Hf.
  Qed.

  Lemma HSH inp m hd pr s1 s2 c:
    acyclic_sigma s1 ->
    [disjoint (vars_tm hd) & (varsU (map varsU_rule pr))] ->
    [disjoint (vars_tm (deref s1 c)) & (varsU (map varsU_rule pr))] ->
    [disjoint (vars_tm (deref s1 c)) & vars_tm hd] ->
    H u inp m (deref s1 c) hd s1 = Some s2 ->
    select_head hd inp m pr = [::] ->
    (select u (deref s1 c) inp m pr s1).2 = [::].
  Proof.
    elim: pr inp m hd s1 s2 c => //= -[hd bo] rs IH/= inp m hd' s1 s2 c AS.
    rewrite disjointUr => /andP[D1 D2].
    rewrite disjointUr => /andP[D3 D4] D5 HH.
    case HHead: H_head => //= SH.
    have {}IH := IH _ _ _ _ _ _ AS D2 D4 D5 HH SH.
    rewrite (SHS _ _ _ _ HH HHead)//=.
      by move: D1; rewrite/varsU_rule disjointUr/varsU_rhead/= => /andP[->].
      by move: D3; rewrite/varsU_rule disjointUr/varsU_rhead/= => /andP[->].
    by apply/acyclic_sigma_dis.
  Qed.

  Lemma ren_cat x t z: vars_tm t `<=` domf z -> (ren z t) = ren (x+z) t.
  Proof.
    elim: t z x => //=.
      move=> v z x; rewrite fsub1set !ren_V => H.
      by rewrite lookup_cat H/=.
    move=> f Hf a Ha z x; rewrite fsubUset => /andP[H1 H2].
    rewrite !ren_app (Ha _ x)//(Hf _ x)//.
  Qed.

  Lemma H_head_ren_aux m inp hd q x y z w:
    refresh_for y hd -> refresh_for x hd ->
    refresh_for z q -> refresh_for w q ->
    [disjoint codomf z & vars_tm q `|` vars_tm (ren x hd)] ->
    [disjoint codomf w & vars_tm q `|` vars_tm (ren y hd)] ->
    H_head inp m (ren z q) (ren x hd) = false ->
    H_head inp m (ren w q) (ren y hd) = false.
  Proof.
    rewrite !disjointUr => ++++ /andP[++]/andP[].
    elim: m inp hd q x y z w => [|m IH] inp hd q x y z w//=.
      case: q => //=[p|v]; last by rewrite !ren_V.
      by case: hd => //=[v]; rewrite !ren_V//.
    case: q  => //=[?|f1 a1]; first by rewrite !ren_V.
    case: hd => //=[?|f2 a2]; first by rewrite !ren_V.
    rewrite !good_ren_app => /andP[gyf2 gya2] /andP[gxf1 gxa1] /andP[gzf1 gza1] /andP[gwf1 gwa1].
    rewrite !disjointUr => /andP[H1 H2] /andP[H3 H4] /andP[H5 H6] /andP[H7 H8].
    case: eqP => H; subst => //=; last apply: IH => //; last first.
    case U: unify => [s'|]/= H.
      case : unify => //= _; apply/IH/H => //=.
    case H_head; rewrite (andbT,andbF)//=.
    move /isNoneP: U; rewrite -/(ren z) -/(ren x) -/(ren w) -/(ren y) in H3 H4 H7 H8 *.
    apply: contraNF.
    by apply/unif_ren.
  Qed.

  Lemma good_ren_fresh fv t: refresh_for (fresh_tm  (vars_tm t `|` fv) empty t).2 t.
  Proof.
    set X := _ `|` _.
    have:= @fresh_tm_def X empty t.
    rewrite /=fsub0set fsubsetUl injectiveb0 => /(_ isT isT isT).
    move=> [x [H1 HH I1 D1]]; rewrite cat0f in H1.
    rewrite /refresh_for H1 I1 andbT.
    have:= fresh_tm_sub1 X empty t; rewrite H1 => ->.
    rewrite-H1; apply/fresh_tm_disjoint; rewrite ?(fdisjoint0X, codomf0, fdisjointX0, fsubsetUl)//.
  Qed.

  Lemma H_head_ren inp m fv1 fv2 t xs fx fy q:
    vars_tm (rename (fresh_rules fv1 xs).1 t empty).2 `<=` fx ->
    vars_tm (rename (fresh_rules fv2 xs).1 t empty).2 `<=` fy ->
    H_head inp m (rename fx q empty).2 (rename (fresh_rules fv1 xs).1 t empty).2 = false ->
    H_head inp m (rename fy q empty).2 (rename (fresh_rules fv2 xs).1 t empty).2 = false.
  Proof.
    move=> H1 H2.
    rewrite/rename!push/= in H1 H2 *.
    apply/H_head_ren_aux; only 1-4: by apply: good_ren_fresh.
      rewrite disjointUr disj_codom0L; apply/disjoint_sub/H1/disj_codom0R.
    rewrite disjointUr disj_codom0L; apply/disjoint_sub/H2/disj_codom0R.
  Qed.

  Lemma select_head_ren rs fx fy fv1 fv2 inp m hd:
    let FRS1 := fresh_rules fv1 rs in
    let FRS2 := fresh_rules fv2 rs in
    FRS1.1 `<=` fx ->
    FRS2.1 `<=` fy ->
    select_head (rename fx hd empty).2 inp m FRS1.2 = [::] ->
    select_head (rename fy hd empty).2 inp m FRS2.2 = [::].
  Proof.
    elim: rs fx fy fv1 fv2 inp m hd => //= x xs IH fx fy fv1 fv2 inp m hd; rewrite !push/=.
    move=> H2 H3.
    case H: H_head => //=.
    move: H; rewrite !head_fresh_rule => H.
    rewrite /fresh_rule!push/= in H2 H3.
    have {}H2' := fsubset_trans (fresh_atoms_sub _ _ _) H2.
    have {}H3' := fsubset_trans (fresh_atoms_sub _ _ _) H3.
    have {}H2' := fsubset_trans (vars_tm_rename _ _) H2'.
    have {}H3' := fsubset_trans (vars_tm_rename _ _) H3'.
    rewrite (H_head_ren H2' H3' H).
    apply: IH; (apply:fsubset_trans; first apply: fresh_rule_sub); rewrite/fresh_rule?push//=.
  Qed.

  Lemma mut_exclP p fv c s1:
    (* acyclic_sigma s1 -> *)
    mut_excl p -> 
      tm_is_det p.(sig) c ->
        all_but_last (fun x => has_cut_seq x.2) (bc u p fv c s1).2.
  Proof.
    rewrite/bc.
    case: p => [rs s]/=+TD.
    rewrite (is_det_cder _ TD).
    case: ifP => //= /negbFE AS.
    case DR: get_tm_hd => //=[p].
    case: fndP => //= pP.
    rewrite/mut_excl !push/=.
    elim: rs s c s1 fv p pP DR TD AS => [|[hd bo] rs IH]//= s c s1 fv p pP DF TD AS.
    rewrite !push/=.
    move=> /andP[+ ME].
    have:= IH _ _ _ _ _ pP DF TD AS ME.
    set FRS1 := fresh_rules _ _.
    set FRS2 := fresh_rules _ _.
    set FS1 := fresh_rule _ _.
    set FS2 := fresh_rule _ _.
    move=> {}IH.
    case H: H => [s2|]//=; rewrite?push/=IH//=andbT.
    move: H; rewrite/FS2.
    rewrite/FS1 head_fresh_rule/=/fresh_rule/=!push/=.
    rewrite/mut_excl_head.
    set FC2:= rename _ _ _.
    set FC1:= rename _ _ _.
    move=> H/=.
    have := H_callable H.
    rewrite (callabe_some_deref _ DF) {1}/FC1{1}/FC2 => /(_ _ erefl)/callable_rename.
    move=> /[dup] DF1/callable_rename ->.
    rewrite in_fnd push (is_det_lookup _ DF)//=.
    move: H; rewrite{2}/FC2 get_modes_rev_rename (get_modes_rev_deref _ _ DF) => H.
    have:= get_modes_rev_H s.[pP].2 H (callabe_some_deref _ DF).
    rewrite (get_modes_rev_deref _ _ DF){1}/FC1 get_modes_rev_rename.
    move: H => +<-; move: (get_modes_rev _ _) => m H.
    have := H_suff_mode H.
    rewrite !has_cut_seq_fresh.
    case CS: has_cut_seq; first by case: select => [?[|[]]].
    case SH: select_head => //SM _.
    have/(_  (vars_sigma s1 `|` vars_tm (deref s1 c) `|` fv)):= select_head_ren (fsubset_refl _) (fsubset_refl _) SH.
    rewrite -/FRS2-/FC2.
    move=> HS.
    rewrite (HSH _ _ _ _ H HS)//=.
      by rewrite/FC2; apply/disjoint_varsU.
      apply/fdisjointWl/disjoint_varsU1.
      by rewrite -fsetUA fsetUC -!fsetUA fsubsetUl.
    rewrite fdisjoint_sym.
    apply/disjoint_sub.
    apply/vars_tm_rename_disjoint => //.
      by rewrite codomf0.
      by rewrite codomf0 fdisjointX0.
    apply/fsubset_trans/fresh_rules_sub.
    rewrite -fsetUA fsetUC -!fsetUA.
    apply/fsubsetUl.
  Qed.

  Print  Assumptions  mut_exclP.


  Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

  Definition all_cut p :=  all_rs_cut (rules p).

  Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
  Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

  Lemma all_cut_select_head c i m rs fv:
    all_rs_cut rs ->
    all_rs_cut (select_head c i m (fresh_rules fv rs).2).
  Proof.
    elim: rs m fv c => //=[[hd bo]]/= rs IH m fv c /andP[H1 H2].
    rewrite !push/= fun_if/= IH//= andbT; case: ifP => //=.
    by rewrite premises_fresh_rule//= has_cut_seq_fresh//.
  Qed.

  Lemma all_cut_mut_excl p: all_cut p -> mut_excl p.
  Proof.
    rewrite/all_cut/mut_excl push/=.
    case: p => /= + s.
    elim => //= [[hd bo]] rs/= IH; rewrite !push/=.
    move=> /andP[HBO] H; rewrite IH// andbT.
    rewrite/fresh_rule !push/=/mut_excl_head/=.
    case tm: get_tm_hd => //=[p]; case: fndP => //= kp.
    rewrite push.
    case: ifP => // ds.
    set R1 := rename _ _ _.
    case S: select_head => //=[r' rs'].
    rewrite has_cut_seq_fresh HBO/=.
    set X := rename (fresh_rules fset0 rs).1 hd empty.
    have:= all_cut_select_head R1.2 (get_modes_rev R1.2 (s.[kp]).2 - (s.[kp]).1) (get_modes_rev R1.2 s.[kp].2) fset0 H.
    by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
  Qed.
End mut_excl.



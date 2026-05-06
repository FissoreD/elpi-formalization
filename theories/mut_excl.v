From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif fresh.

Section mut_excl.
  (* Variable u : Unif. *)

  Fixpoint H_head (ml: seq mode) (q : seq Tm) (h: seq Tm) : bool :=
    match ml,q,h with
    | _, [::], [::] => true
    | m :: tl, x :: xs, y :: ys => 
      ((m != input) || unify x y fmap0) && H_head tl xs ys
    | _, _, _ => false
    end.
  
  Fixpoint select_head (hd : P) (args: seq Tm) (md: seq mode) (rules: list R) : (seq R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head hd args md rules in
      let hd' := get_tm_hd rule.(head) in
      let args' := flatten_term rule.(head) in
      if inl hd != hd' then tl
      else if H_head md args args' then rule :: tl else tl
    end.
  
  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    let query := r.(head) in
    let hd := get_tm_hd query in
    match hd with
      | inl kp =>
        match sig.[? kp] with 
          | Some sig => 
            if is_det_sig sig then 
              let args := flatten_term query in
              let rs := select_head kp args (flatten_mode sig) rules in
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

  Definition all_inp := all (eq_op input).

  Fixpoint good_mode m :=
    match m with
    | [::] => true
    | output :: xs => good_mode xs
    | input :: xs => all_inp xs
    end.

  Definition good_modes (s: sigT) :=
    [forall x : domf s, good_mode (flatten_mode s.[valP x])].

  Definition mut_excl pr :=
    let: (fv, rules) := fresh_rules fset0 pr.(rules) in
    good_modes pr.(sig) && mut_excl_aux pr.(sig) rules.

     (* sufficient modes length for callable t *)
  (* Fixpoint suff_mode (t:Tm) (m:nat) :=
    match m, t with
    | 0, Tm_P _ => true
    | m.+1, Tm_App x _ => suff_mode x m
    | _, _ => false
    end.

  Lemma H_suff_mode md l q fv hd s1 s2 md:
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
  Qed. *)

  (* Lemma H_callable md t1 t2 s1 s2 p:
    H u md t1 t2 s1 = Some s2 ->
    get_tm_hd t1 = inl p ->
    get_tm_hd t2 = inl p.
  Proof.
    elim: md t1 t2 s1 s2 p => //=.
      by move=> []//= p []//p' s1 s2; case: eqP => //-[->].
    move=> [m _] tl IH []//f1 a1 []//f2 a2 s1 s2 p.
    case H: H => //= _.
    by apply: IH H.
  Qed. *)

  Lemma callable_ren m hd p:
    get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. 
    elim: hd => //= [q|d|v|f Hf a Ha]; rewrite ?(ren_P,ren_D,ren_app)//=.
    by have [x ->] := ren_VE m v.
  Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed.

  (* Lemma callable_rename_subst fv hd p mp: 
    get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed. *)

  Lemma is_det_cder s s1 c: tm_is_det s c -> get_tm_hd (deref s1 c) = get_tm_hd c.
  Proof. 
    elim: c s => //=[p|f Hf a Ha] s; rewrite ?deref_P//.
    rewrite tm_is_det_app deref_App/=; apply: Hf.
  Qed.

  Lemma is_det_lookup p c s (pP: p \in domf s):
    get_tm_hd c = inl p -> tm_is_det s c -> is_det_sig s.[pP].
  Proof. by elim: c p s pP => //=p1 p2 s pP [->]; rewrite/tm_is_det/=in_fnd//. Qed.

  Lemma count_tm_ag_deref s c p: 
    get_tm_hd c = inl p -> count_tm_ag (deref s c) = count_tm_ag c.
  Proof. elim: c p s => //[p|f Hf a Ha] q s/= H; rewrite (deref_App, deref_P)//=(Hf q)//. Qed.

  (* Lemma get_modes_rev_deref c p s1 s: 
    get_tm_hd c = inl p -> get_modes (deref s1 c) s = get_modes c s.
  Proof. move=> H; rewrite/get_modes (count_tm_ag_deref _ H)//. Qed. *)

  (* Lemma count_tm_ag_H d1 d2 s1 s2 m p:
    H u m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      count_tm_ag d1 = count_tm_ag d2.
  Proof.
    elim: d1 d2 s1 s2 m p => //=[p|f Hf a Ha] d2 s1 s2 m l.
      by case: m => //=[|[]]//; case: eqP => //<-//.
    case: m => //= -[m _] ms; case: d2 => //= f1 a1; case H: H => //[s1']/= M C.
    by f_equal; apply: Hf H C.
  Qed. *)

  (* Lemma get_modes_rev_H d1 d2 s1 s2 m l p:
    H u m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      get_modes d1 l = get_modes d2 l.
  Proof. move=> H C; rewrite/get_modes (count_tm_ag_H H C)//. Qed. *)

  Lemma all_inp_cons x xs: all_inp (x::xs) -> all_inp xs.
  Proof. by move=> /andP[]. Qed.

  Definition vars_tms t := varsU (map vars_tm t).

  Lemma vars_tms_cons x xs: vars_tms (x::xs) = vars_tm x `|` vars_tms xs.
  Proof. by []. Qed.

  Definition u := mk_Unif unify matching.

  Lemma disjointH m f f1 s1 s1': 
    all_inp m ->
    [disjoint (vars_tms f) & domf s1] ->
    [disjoint (vars_tms f) & vars_tms f1] ->
      H u m f f1 s1 = Some s1' ->
        exists x, domf s1' = domf s1 `|` x /\ x `<=` vars_tms f1.
  Proof.
    elim: m f f1 s1 s1' => //=.
      move=> []//= []// f1 s1 s1' _ _ [<-].
      by exists fset0; rewrite fsetU0.
    move=> [] ms IH f f1 s1 s1'//=.
    case: f => //=; case: f1 => //=.
    move=> x xs y ys AI.
    rewrite !vars_tms_cons.
    rewrite disjointUl => /andP[D1 D2].
    rewrite fdisjointXU !fdisjointUX.
    move=> /andP[/andP[D6 D7] /andP[D8 D9]].
    case H: H => //=[s1''] M.
    have [w {IH}[H1 H2]] := IH _ _ _ _ AI D2 D9 H.      
    have [| k [H3 H4]] := matching_disj _ D6 M.
      rewrite H1 disjointUr D1 (fdisjointWr H2)//.
    rewrite H3 H1; exists (w `|` k).
    rewrite fsetUA; split => //.
    by rewrite fsubUset !fsubsetU//(H2,H4)//orbT.
  Qed.

  Lemma all_inp_good_mode l: all_inp l -> good_mode l.
  Proof. elim: l => //= -[]//. Qed.

  Lemma all_inp_good_modeM m tl:
    match m with
    | input => all_inp tl
    | output => good_mode tl
    end -> good_mode tl.
  Proof. by case: m => ///all_inp_good_mode. Qed.

  Lemma SHS m c hd2 hd1 (s1 s2:Sigma):
    good_mode m ->
    [disjoint vars_tms hd1 & vars_tms hd2] ->
    [disjoint vars_tms c & vars_tms hd1] ->
    [disjoint vars_tms c & vars_tms hd2] ->
    [disjoint (vars_tms c) & (domf s1)] ->
    H u m c hd1 s1 = Some s2 ->
    H_head m hd1 hd2 = false ->
    H u m c hd2 s1 = None.
  Proof.
    elim: m c hd1 hd2 s1 s2 => //=.
      by move=> []//=[]//[]//.
    move=> m tl IH c h1 h2 s1 s2 GM.
    case: c; case: h1 => //; case: h2 => //.
    move=> q qs x xs y ys.
    rewrite !vars_tms_cons.
    rewrite !fdisjointUX !fdisjointXU.
    move=> /andP[/andP[D1 D2] /andP[D3 D4]].
    move=> /andP[/andP[D5 D6] /andP[D7 D8]].
    move=> /andP[/andP[D9 D10] /andP[D11 D12]].
    move=> /andP[D13 D14].
    case H1: H => //=[s1'].
    case HH: H_head; rewrite (andbT,andbF)//=; last first.
      by rewrite (IH _ _ _ _ _ _ _ _ _ _ H1 HH)//= (all_inp_good_modeM GM).
    case: m GM => //= INP.
    case H2: H => //=[s1''] M U; subst; simpl in HH, H1, H2.
    have Dy: [disjoint vars_tm y & domf s1''].
      have [| |zz [Hx Hy]] := disjointH INP _ _ H2 => //.
      rewrite Hx disjointUr D13 (fdisjointWr Hy)//.
    have Dx: [disjoint vars_tm y & domf s1'].
      have [| |zz [Hx Hy]] := disjointH INP _ _ H1 => //.
      rewrite Hx disjointUr D13 (fdisjointWr Hy)//.
    have {}M := isSomeP M.
    have {}M := matching_subst1 Dx M.
    have {}M := matching_monotone M.
    case M2: matching => //=.
    have {}M2 := isSomeP M2.
    have {}M2 := matching_subst1 Dy M2.
    have {}M2 := matching_monotone M2.
    move: M; case M: matching => //=.
    move: M2; case M2: matching => //=.
    have {}U1:= match_unif M.
    have {}U2:= match_unif M2.
    rewrite unif_sym in U1.
    by rewrite (unif_trans (isSomeP U1) (isSomeP U2)) in U.
  Qed.

  Lemma deref_V s t:
    acyclic_sigma s -> [disjoint vars_tm (deref s t) & domf s].
  Proof.
    rewrite/deref => AS.
  Admitted.

  Lemma acyclic_sigma_dis c s:
    acyclic_sigma s -> [disjoint vars_tm (deref s c) & domf s].
  Proof.
    move=> H; elim: c => [p|d|v|f Hf a Ha]; rewrite ?(deref_P,deref_D)//=?fdisjoint0X//.
      by apply/deref_V.
    by rewrite deref_App/= disjointUl Hf.
  Qed.

  Lemma vars_tms_rcons f a: 
    vars_tms (rcons f a) = vars_tm a `|` vars_tms f.
  Proof. by elim: f a => //= x xs IH a; rewrite !vars_tms_cons IH fsetUA (fsetUC (vars_tm x)) fsetUA. Qed.

  Lemma vars_tms_flatten_term hd': 
    vars_tms (flatten_term hd') `<=` vars_tm hd'.
  Proof. elim: hd' => //= f Hf a Ha; rewrite vars_tms_rcons fsetUC fsetSU//. Qed.

  Lemma HSH m hd pr s1 s2 c pred:
    good_mode m ->
    acyclic_sigma s1 ->
    [disjoint (vars_tm hd) & (varsU (map varsU_rule pr))] ->
    [disjoint (vars_tm (deref s1 c)) & (varsU (map varsU_rule pr))] ->
    [disjoint (vars_tm (deref s1 c)) & vars_tm hd] ->
    H u m (flatten_term (deref s1 c)) (flatten_term hd) s1 = Some s2 ->
    select_head pred (flatten_term hd) m pr = [::] ->
    (select u pred (flatten_term (deref s1 c)) m pr s1).2 = [::].
  Proof.
    elim: pr m hd s1 s2 c => //= -[hd bo] rs IH/= m hd' s1 s2 c GM AS.
    rewrite disjointUr => /andP[D1 D2].
    rewrite disjointUr => /andP[D3 D4] D5 HH.
    case:eqP => //=; last by move=> _; apply:IH HH.
    move=> /esym Hd.
    case HHead: H_head => //= SH.
    have {}IH := IH _ _ _ _ _ GM AS D2 D4 D5 HH SH.
    rewrite (SHS _ _ _ _ _ HH HHead)//=.
      apply/(fdisjointWl (vars_tms_flatten_term _))/(fdisjointWr (vars_tms_flatten_term _)).
      by move: D1; rewrite/varsU_rule disjointUr/varsU_rhead/= => /andP[->].
      by apply/(fdisjointWl (vars_tms_flatten_term _))/(fdisjointWr (vars_tms_flatten_term _)).
      apply/(fdisjointWl (vars_tms_flatten_term _))/(fdisjointWr (vars_tms_flatten_term _)).
      by move: D3; rewrite/varsU_rule disjointUr/varsU_rhead/= => /andP[->].
    apply/(fdisjointWl (vars_tms_flatten_term _)).
    by apply/acyclic_sigma_dis.
  Qed.

  (* Lemma ren_cat x t z: vars_tm t `<=` domf z -> (ren z t) = ren (x+z) t.
  Proof.
    elim: t z x => //=.
      move=> v z x; rewrite fsub1set !ren_V => H.
      by rewrite lookup_cat H/=.
    move=> f Hf a Ha z x; rewrite fsubUset => /andP[H1 H2].
    rewrite !ren_app (Ha _ x)//(Hf _ x)//.
  Qed. *)

  (* Lemma flatten_term_size_rename z w q: 
    size (flatten_term (deref z q)) = size (flatten_term (deref w q)).
  Proof.
    elim: q => //=[v|f Hf a Ha]. *)

  (* Lemma flatten_term_size_ren z w q: 
    size (flatten_term (ren z q)) = size (flatten_term (ren w q)).
  Proof.
    rewrite /ren.
    elim: q z w => //=[v|f Hf a Ha] z w.
      by (do 2 case: fndP => //=) => ??; rewrite !ffunE//.
    by rewrite !size_rcons; f_equal; eauto.
  Qed. *)

  Lemma flatten_term_ren z q:
    flatten_term (ren z q) = map (ren z) (flatten_term q).
  Proof.
    elim: q => [p|d|v|f Hf a Ha]/=; rewrite ?(ren_P,ren_D,ren_app)//=; last by rewrite Hf map_rcons//.
    by have [? ->] := ren_VE z v.
  Qed.

  Lemma H_head_ren_aux m hd q x y z w:
    all (refresh_for y) hd -> all (refresh_for x) hd ->
    all (refresh_for z) q -> all (refresh_for w) q ->
    [disjoint codomf z & vars_tms q `|` vars_tms (map (ren x) hd)] ->
    [disjoint codomf w & vars_tms q `|` vars_tms (map (ren y) hd)] ->
    H_head m (map (ren z) q) (map (ren x) hd) = false ->
    H_head m (map (ren w) q) (map (ren y) hd) = false.
  Proof.
    rewrite !disjointUr => ++++ /andP[++]/andP[].
    elim: m hd q x y z w => [|m tl IH] hd q x y z w//=.
      by case: q; case: hd => //.
    case: q; case: hd => //= c cs d ds.
    move => /andP[gyf2 gya2] /andP[gxf1 gxa1] /andP[gzf1 gza1] /andP[gwf1 gwa1].
    rewrite !vars_tms_cons.
    rewrite !disjointUr => /andP[H1 H2] /andP[H3 H4] /andP[H5 H6] /andP[H7 H8].
    case: eqP => H; subst => //=; last apply: IH => //; last first.
    case U: unify => [s'|]/= H.
      case : unify => //= _; apply/IH/H => //=.
    case H_head; rewrite (andbT,andbF)//=.
    move /isNoneP: U; rewrite -/(ren z) -/(ren x) -/(ren w) -/(ren y) in H3 H4 H7 H8 *.
    apply: contraNF.
    by apply/unif_ren.
  Qed.

  Lemma good_ren_fresh s t q: 
    vars_tm t `<=` vars_tm q -> vars_tm q `<=` s -> refresh_for (fresh_tm s empty q).2 t.
  Proof.
    move=> Hx H.
    have:= @fresh_tm_def s empty q.
    rewrite/refresh_for.
    rewrite /=fsub0set injectiveb0 => /(_ isT H isT).
    move=> [x [H1 HH I1 D1]]; rewrite cat0f in H1; subst.
    rewrite -andbA; apply/and3P; split => //.
      by apply/fsubset_trans/fresh_tm_sub1.
    apply/fresh_tm_disjoint;rewrite //?(fdisjoint0X, codomf0, fdisjointX0, fsubsetUl)//.
  Qed.

  Lemma good_ren_fresh_all s t q: 
    vars_tms t `<=` vars_tm q -> vars_tm q `<=` s ->
      all (refresh_for (fresh_tm s empty q).2) t.
  Proof.
    move=> + Hx.
    elim: t => //=x xs IH.
    rewrite vars_tms_cons fsubUset => /andP[H1 H2].
    rewrite IH// andbT.
    apply/good_ren_fresh => //.
  Qed.

  (* Lemma good_ren_fresh fv t: refresh_for (fresh_tm  (vars_tm t `|` fv) empty t).2 t.
  Proof.
    set X := _ `|` _.
    have:= @fresh_tm_def X empty t.
    rewrite /=fsub0set fsubsetUl injectiveb0 => /(_ isT isT isT).
    move=> [x [H1 HH I1 D1]]; rewrite cat0f in H1.
    rewrite /refresh_for H1 I1 andbT.
    have:= fresh_tm_sub1 X empty t; rewrite H1 => ->.
    rewrite-H1; apply/fresh_tm_disjoint; rewrite ?(fdisjoint0X, codomf0, fdisjointX0, fsubsetUl)//.
  Qed.

  Lemma good_ren_fresh_all (x:{fmap V -> V}) t:
    injectiveb x -> [disjoint (domf x) & codomf x] ->
      vars_tms t `<=` domf x ->
        all (refresh_for x) t.
  Proof.
    move=> H1 H2.
    elim: t => //= y ys IH; rewrite vars_tms_cons fsubUset => /andP[Hx /IH ->].
    rewrite/refresh_for Hx H1 andbT//.
  Qed. *)

  Lemma H_head_ren m fv1 fv2 t xs fx fy q:
    vars_tm (rename (fresh_rules fv1 xs).1 t empty).2 `<=` fx ->
    vars_tm (rename (fresh_rules fv2 xs).1 t empty).2 `<=` fy ->
    H_head m (flatten_term (rename fx q empty).2) (flatten_term (rename (fresh_rules fv1 xs).1 t empty).2) = false ->
    H_head m (flatten_term (rename fy q empty).2) (flatten_term (rename (fresh_rules fv2 xs).1 t empty).2) = false.
  Proof.
    move=> H1 H2.
    rewrite/rename!push/= in H1 H2 *.
    rewrite !flatten_term_ren.
    apply/H_head_ren_aux => //=; only 1-4: by apply/good_ren_fresh_all; rewrite (vars_tms_flatten_term, fsubsetUl)//.
      rewrite disjointUr; apply/andP; split.
        by apply/fdisjointWr/disj_codom0L; rewrite vars_tms_flatten_term.
      apply/fdisjointWr/disj_codom0R.
      apply/fsubset_trans/H1.
      rewrite -flatten_term_ren vars_tms_flatten_term//.
    rewrite disjointUr; apply/andP; split.
      by apply/fdisjointWr/disj_codom0L; rewrite vars_tms_flatten_term.
    apply/fdisjointWr/disj_codom0R.
    apply/fsubset_trans/H2.
    rewrite -flatten_term_ren vars_tms_flatten_term//.
  Qed.

  Lemma callable_rename1 p fv1 hd mp: 
    (get_tm_hd (rename fv1 hd mp).2 == inl p) = (get_tm_hd hd == inl p).
  Proof.
    case:eqP; case:eqP => //= H1 H2.
      by move/callable_rename: H1 => /(_ _ _ H2).
    by have:= H2 (proj2 (callable_rename _ _ _ _) _); auto.
  Qed.

  Lemma select_head_ren p rs fx fy fv1 fv2 m hd:
    let FRS1 := fresh_rules fv1 rs in
    let FRS2 := fresh_rules fv2 rs in
    (* get_tm_hd hd = inl p -> *)
    FRS1.1 `<=` fx ->
    FRS2.1 `<=` fy ->
    select_head p (flatten_term (rename fx hd empty).2) m FRS1.2 = [::] ->
    select_head p (flatten_term (rename fy hd empty).2) m FRS2.2 = [::].
  Proof.
    elim: rs fx fy fv1 fv2 m hd => //= x xs IH fx fy fv1 fv2 m hd; rewrite !push/=.
    move=> H2 H3. rewrite !(head_fresh_rule, eq_sym (inl p), callable_rename1).
    case: eqP => //= Hd; last first.
      by apply: IH; (apply: fsubset_trans; [|eassumption]); apply/fresh_rule_sub.
    case H: H_head => //=.
    rewrite /fresh_rule!push/= in H2 H3.
    have {}H2' := fsubset_trans (fresh_atoms_sub _ _ _) H2.
    have {}H3' := fsubset_trans (fresh_atoms_sub _ _ _) H3.
    have {}H2' := fsubset_trans (vars_tm_rename _ _) H2'.
    have {}H3' := fsubset_trans (vars_tm_rename _ _) H3'.
    rewrite (H_head_ren H2' H3' H).
    apply: IH; (apply:fsubset_trans; first apply: fresh_rule_sub); rewrite/fresh_rule?push//=.
  Qed.

  (* Lemma flatten_modes_rename fs hd m mp:
    flatten_mode (rename fs hd mp).2 m = flatten_mode hd m.
  Proof. by rewrite/flatten_mode count_tm_ag_rename//. Qed. *)
  
  Lemma build_and (a b: bool): a -> b -> a && b. move: a b => [][]//. Qed.

  Lemma mut_exclP p fv c s1:
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
    move=> /and3P[GM + ME].
    have:= IH _ _ _ _ _ pP DF TD AS (build_and GM ME).
    set FRS1 := fresh_rules _ _.
    set FRS2 := fresh_rules _ _.
    set FS1 := fresh_rule _ _.
    set FS2 := fresh_rule _ _.
    move=> {}IH.
    case: eqP => //=; last by eauto.
    case H: H => [s2|]//=; rewrite?push/=IH//=andbT.
    move: H; rewrite/FS2.
    rewrite/FS1 head_fresh_rule/=/fresh_rule/=!push/=.
    rewrite/mut_excl_head.
    set FC2:= rename _ _ _.
    set FC1:= rename _ _ _.
    move=> H/= /esym/callable_rename B.
    rewrite {1}/FC1 (proj2 (callable_rename FRS1.1 hd p empty))//.
    rewrite in_fnd (is_det_lookup _ DF)//=.
    (* move: H. *)
     (* rewrite{2}/FC2 get_modes_rev_rename (get_modes_rev_deref _ _ DF) => H. *)
    (* have:= get_modes_rev_H s.[pP] H (callabe_some_deref _ DF). *)
    (* rewrite (get_modes_rev_deref _ _ DF){1}/FC1 get_modes_rev_rename. *)
    have: good_mode (flatten_mode s.[pP]).
      move: GM; rewrite /good_modes/flatten_mode.
      by move=> /forallP /(_ [` pP]); rewrite valPE.
    move: H; move: (flatten_mode _) => m H GM'.
    (* have := H_suff_mode H. *)
    rewrite !has_cut_seq_fresh.
    case CS: has_cut_seq; first by case: select => [?[|[]]].
    case SH: select_head => // _.
    have/(_  (vars_sigma s1 `|` vars_tm (deref s1 c) `|` fv)):= select_head_ren (fsubset_refl _) (fsubset_refl _) SH.
    rewrite -/FRS2-/FC2.
    move=> HS.
    rewrite (HSH _ _ _ _ _ H HS)//=.
      by rewrite/FC2; apply/disjoint_varsU.
      apply/fdisjointWl/disjoint_varsU1.
      by rewrite -fsetUA fsetUC -!fsetUA fsubsetUl.
    rewrite fdisjoint_sym.
    apply/disjoint_sub.
    apply/vars_tm_rename_disjoint => //.
    apply/fsubset_trans/fresh_rules_sub.
    rewrite -fsetUA fsetUC -!fsetUA.
    apply/fsubsetUl.
  Qed.

  Print  Assumptions  mut_exclP.


  Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

  Definition all_cut p :=  all_rs_cut (rules p).

  Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
  Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

  Lemma all_cut_select_head p t m rs fv:
    all_rs_cut rs ->
    all_rs_cut (select_head p t m (fresh_rules fv rs).2).
  Proof.
    elim: rs m fv p t => //=[[hd bo]]/= rs IH m fv p t /andP[H1 H2].
    rewrite !push/= head_fresh_rule; case:eqP => //=; last by eauto.
    case:ifP => //=; eauto.
    rewrite premises_fresh_rule/= has_cut_seq_fresh H1; eauto.
  Qed.

  Lemma all_cut_mut_excl p: good_modes p.(sig) -> all_cut p -> mut_excl p.
  Proof.
    rewrite/all_cut/mut_excl push/= => ->/=.
    case: p => /= + s.
    elim => //= [[hd bo]] rs/= IH; rewrite !push/=.
    move=> /andP[HBO] H; rewrite IH// andbT.
    rewrite/fresh_rule !push/=/mut_excl_head/=.
    case tm: get_tm_hd => //=[p]; case: fndP => //= kp.
    (* rewrite push. *)
    case: ifP => // ds.
    set R1 := rename _ _ _.
    case S: select_head => //=[r' rs'].
    rewrite has_cut_seq_fresh HBO/=.
    set X := rename (fresh_rules fset0 rs).1 hd empty.
    have:= all_cut_select_head p (flatten_term R1.2) (flatten_mode s.[kp]) fset0 H.
    by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
  Qed.
End mut_excl.



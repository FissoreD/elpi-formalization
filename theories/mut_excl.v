From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars fresh unif.

Section mut_excl.
  Variable u : Unif.

  (* returns if all inputs can be unified *)
  (* inputs come before outputs *)
  (* outputs are neutral for this function *)
  Fixpoint H_head (ml: seq mode) (q : seq Tm) (h: seq Tm) : bool :=
    match ml,q,h with
    (* here we return false if m == input and x and y can't unify
       this means that the two heads are non overlapping *)
    | m :: tl, x :: xs, y :: ys => 
      ((m != input) || lang.unify u y x fmap0) && H_head tl xs ys
    | _, _, _ => true
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

  Definition all_out := all (eq_op output).

  Fixpoint good_mode m :=
    match m with
    | [::] => true
    | input :: xs => good_mode xs
    | output :: xs => all_out xs
    end.

  Definition good_modes (s: sigT) :=
    [forall x : domf s, good_mode (flatten_mode s.[valP x])].

  Definition mut_excl pr :=
    let: (fv, rules) := fresh_rules fset0 pr.(rules) in
    good_modes pr.(sig) && mut_excl_aux pr.(sig) rules.

  Lemma callable_ren m hd p:
    get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. by elim: hd => //= [q|d|v|f Hf a Ha]. Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed.

  Lemma is_det_cder s s1 c: tm_is_det s c -> get_tm_hd (deref s1 c) = get_tm_hd c.
  Proof. elim: c s => //=[p|f Hf a Ha] s; rewrite ?deref_P//. Qed.

  Lemma is_det_lookup p c s r (pP: p \in domf s):
    get_tm_hd c = inl p -> tm_is_det {|rules := r; sig := s|} c -> is_det_sig s.[pP].
  Proof. by elim: c p s pP => //=p1 p2 s pP [->]; rewrite/tm_is_det/=in_fnd//. Qed.

  Lemma count_tm_ag_deref s c p: 
    get_tm_hd c = inl p -> count_tm_ag (deref s c) = count_tm_ag c.
  Proof. elim: c p s => //f Hf a Ha q s/= H; rewrite (Hf _ _ H)//. Qed.

  Lemma all_inp_cons x xs: all_out (x::xs) -> all_out xs.
  Proof. by move=> /andP[]. Qed.

  Definition vars_tms t := varsU (map vars_tm t).

  Lemma vars_tms_cons x xs: vars_tms (x::xs) = vars_tm x `|` vars_tms xs.
  Proof. by []. Qed.
End mut_excl.

Lemma all_inp_good_mode l: all_out l -> good_mode l.
Proof. elim: l => //= -[]//. Qed.

Lemma all_out_good_modeM m tl:
  match m with
  | output => all_out tl
  | input => good_mode tl
  end -> good_mode tl.
Proof. by case: m => ///all_inp_good_mode. Qed.

Lemma vars_tms_rcons f a: 
  vars_tms (rcons f a) = vars_tm a `|` vars_tms f.
Proof. by elim: f a => //= x xs IH a; rewrite !vars_tms_cons IH fsetUA (fsetUC (vars_tm x)) fsetUA. Qed.

Lemma vars_tms_flatten_term hd': 
  vars_tms (flatten_term hd') `<=` vars_tm hd'.
Proof. elim: hd' => //= f Hf a Ha; rewrite vars_tms_rcons fsetUC fsetSU//. Qed.

Lemma fdisjoint_ftl s q : [disjoint vars_tm s & q] -> [disjoint vars_tms (flatten_term s) & q].
Proof. by apply/fdisjointWl/vars_tms_flatten_term. Qed.

Lemma fdisjoint_ftr s q : [disjoint q & vars_tm s] -> [disjoint q & vars_tms (flatten_term s)].
Proof. by apply/fdisjointWr/vars_tms_flatten_term. Qed.

Lemma fdisjoint_ft2 s q : [disjoint vars_tm q & vars_tm s] -> 
  [disjoint vars_tms (flatten_term q) & vars_tms (flatten_term s)].
Proof. by move=> H; apply/fdisjointWr/fdisjoint_ftl/H/vars_tms_flatten_term. Qed.

Definition u := mk_Unif unify matching.

Lemma not_in_deref_L s l:
  domf s # vars_tms l -> map (deref s) l = l.
Proof.
  elim: l => //= x xs H; rewrite vars_tms_cons fdisjointXU => /andP[D1 /H->].
  by rewrite not_in_deref//.
Qed.


Lemma SHS fv1 fv2 m c hd2 hd1 (s1 s2:Sigma):
  acyclic s1 -> acyclic s2 ->
  all (eq_op input) m ->
  [disjoint vars_sigma s1 & vars_tms hd2] -> 
  [disjoint vars_sigma s2 & vars_tms hd1] -> 
  [disjoint vars_tms hd1 & vars_tms hd2] ->
  [disjoint vars_tms c & vars_tms hd1] ->
  [disjoint vars_tms c & vars_tms hd2] ->
  [disjoint domf s1 & vars_tms c] ->
  [disjoint domf s2 & vars_tms c] ->
  vars_tms c `<=` fv1 ->
  vars_tms c `<=` fv2 ->
  H u fv1 m c hd1 s1 ->
  H u fv2 m c hd2 s2 ->
  H_head u m hd1 hd2.
Proof.
  elim: m c hd1 hd2 s1 s2 => //=.
  move=> []// tl IH c h1 h2 s1 s2 A1 A2 /andP[_ GM].
  case: c => [|q qs]; case: h1 => [|h1 h1s]; case: h2 => [|h2 h2s]//=.
  rewrite !vars_tms_cons.
  rewrite 2!fdisjointXU => /andP[V1 V2] /andP[V3 V4].
  rewrite ?fdisjointUX !fdisjointXU.
  move=> /andP[/andP[D1 D2] /andP[D3 D4]].
  move=> /andP[/andP[D5 D6] /andP[D7 D8]].
  move=> /andP[/andP[D9 D10] /andP[D11 D12]].
  (* move=> /andP[Da Db] /andP[Dc Dd]. *)
  move=> /andP[D13 D14] .
  move=> /andP[D15 D16] .
  rewrite !fsubUset => /andP[S1 S2] /andP[S3 S4].
  case M1: matching => [s1'|]//=.
  case M2: matching => [s2'|]//=.
  move=> H1 H2; apply/andP; split.
    apply: matching_unify_transP (isSomeP M2) (isSomeP M1); rewrite//?not_in_deref//.
    by rewrite fdisjoint_sym.
    by rewrite fdisjoint_sym.
    by rewrite fdisjoint_sym.
  have Hx := matching_ext1 M1.
  have Hy := matching_ext1 M2.
  have A1' := matching_acyclic A1 M1.
  have A2' := matching_acyclic A2 M2.
  rewrite !(@not_in_deref _ q)// in Hx Hy.
  apply/IH/H2/H1 => //.
  - apply: fdisjointWl (matching_ext3 A1 M1) _.
    by rewrite 2!fdisjointUX -andbA; apply/and3P; split => //.
  - apply: fdisjointWl (matching_ext3 A2 M2) _.
    rewrite 2!fdisjointUX -andbA; apply/and3P; split => //.
    by rewrite fdisjoint_sym.
  - apply: fdisjointWl Hx _.
    rewrite fdisjointUX; apply/andP; split => //.
    apply/fdisjointP => x.
    rewrite !inE => /andP[+ _].
    by apply/contra/fsubsetP.
  - apply: fdisjointWl Hy _.
    rewrite fdisjointUX; apply/andP; split => //.
    apply/fdisjointP => x.
    rewrite !inE => /andP[+ _].
    by apply/contra/fsubsetP.
Qed.

Fixpoint size_input m :=
  match m with
  | input :: m => (size_input m).+1
  | _ => 0
  end.

Definition tk_input T m := @take T (size_input m).

Lemma H_sublist fv n m q h s: H u fv m q h s -> H u fv (take n m) (take n q) (take n h) s.
Proof.
  elim: n m q h s => [|n IH] m q h s; first by rewrite !take0.
  case: m => [|m ms]; case: q => [|q qs]; case: h => [|h hs]//=.
  case: m => //=.
    case M: matching => //=[s']; auto.
  case U: unify => //=[s']; auto.
Qed.

Lemma H_head_all_out u m q h: all_out m -> H_head u m q h.
Proof. elim: m q h => //=-[]//=m IH [//|_ l] [//|_ l']; apply: IH. Qed.

Lemma H_head_sublist m q h: good_mode m -> 
  H_head u (tk_input m m) (tk_input m q) (tk_input m h) -> H_head u m q h.
Proof.
  elim: m q h => // -[] ms IH q h/=; last first.
    by move=> /H_head_all_out; case: q => //; case: h => // _ l1 _ l2 _.
  by case: q => //= q qs; case: h => //= h hs gm/andP[-> /IH ->]//.
Qed.

Lemma vars_tm_take_sub n a: vars_tms (take n a) `<=` vars_tms a.
Proof.  
  elim: n a => // [|n IH] t; first by rewrite take0.
  by destruct t => //=; rewrite !vars_tms_cons; apply/fsetUS/IH.
Qed.

Lemma disjoint_takel n a b:
  [disjoint vars_tms a & b] -> [disjoint vars_tms (take n a) & b].
Proof. by apply/fdisjointWl/vars_tm_take_sub. Qed.

Lemma disjoint_taker n a b:
  [disjoint b & vars_tms a] -> [disjoint b & vars_tms (take n a)].
Proof. by rewrite !(fdisjoint_sym b); apply: disjoint_takel. Qed.

Lemma disjoint_take2 m n a b:
  [disjoint vars_tms b & vars_tms a] -> [disjoint vars_tms (take m b) & vars_tms (take n a)].
Proof. by move=> H; apply/disjoint_takel/disjoint_taker. Qed.

Lemma disjoint_takeLr T n a f (b: seq T):
  [disjoint a & vars_tms (map f b)] -> [disjoint a & vars_tms (map f (take n b))].
Proof.
  move=> H; apply/fdisjointWr/H.
  elim: n b {H} => [|n IH] b; first by rewrite take0.
  by case: b => //=x xs; rewrite !vars_tms_cons; apply/fsetUS/IH.
Qed.

Lemma good_mode_take_inp m: good_mode m ->
  all (eq_op input) (take (size_input m) m).
Proof. by elim: m => //=-[]. Qed.

Lemma all_out_size_input m: all_out m -> size_input m = 0.
Proof. by elim: m => //=-[]. Qed.

Lemma get_frozen_vars_sub m t : good_mode m ->
  vars_tms (take (size_input m) t) = get_frozen_vars m t.
Proof.
  elim: m t => //=[|m ms IH] t; first by rewrite take0.
  case: m; case: t => //= x xs; last first.
    by move=> /[dup] /all_inp_good_mode/IH<-/all_out_size_input->; rewrite take0.
  rewrite vars_tms_cons => /IH ->//.
Qed.

Definition v_prog pr := varsU (map varsU_rule pr).

Lemma v_prog_cons x xs: v_prog (x::xs) = varsU_rhead x `|` varsU_rprem x `|` v_prog xs.
Proof. by []. Qed.


Lemma HSH m hd pr s1 c pred: good_mode m -> acyclic s1 ->
  [disjoint domf s1 & vars_tms c] ->
  [disjoint vars_tms hd & v_prog pr] ->
  [disjoint vars_tms c & v_prog pr] ->
  [disjoint vars_tms c & vars_tms hd] ->
  [disjoint vars_sigma s1 & v_prog pr] ->
  [disjoint vars_sigma s1 & vars_tms hd] ->
  H u (get_frozen_vars m c) m c hd s1 ->
  select_head u pred hd m pr = [::] ->
  (select u pred c m pr s1).2 = [::].
Proof.
  elim: pr m hd s1 c => //= -[hd bo] rs IH/= m hd' s1 c GM AS D.
  rewrite !v_prog_cons /varsU_rhead /varsU_rprem/=.
  rewrite !fdisjointXU -!andbA => /and3P[hh' hb' hr'] /and3P[ch cb cr] ch' ++ H1.
  move=> /and3P[Dh Db Dr] Dh'.
  case:eqP => //=; last by move=> _; apply:IH.
  move=> /esym Hd.
  case HH: H_head => //= S1.
  have {S1} IH := IH _ _ _ _ GM AS D hr' cr ch' Dr Dh' H1 S1.
  case H2: H => [s'|]//{IH}; apply isSomeP in H2.
  exfalso; apply: (negP (negbT HH)) => {HH}.
  apply: H_head_sublist (GM) _.
  have H1' := H_sublist (size_input m) H1.
  have H2' := H_sublist (size_input m) H2.
  apply: SHS H1' H2' => //.
  - by apply/good_mode_take_inp.
  - by apply: disjoint_taker; apply: fdisjoint_ftr _.
  - by apply: disjoint_taker.
  - by apply: disjoint_take2; apply: fdisjoint_ftr.
  - by apply: disjoint_take2.
  - by apply: disjoint_take2; apply: fdisjoint_ftr _.
  - by apply/disjoint_taker.
  - by apply/disjoint_taker.
  - by rewrite get_frozen_vars_sub.
  - by rewrite get_frozen_vars_sub.
Qed.

Lemma flatten_term_ren z q:
  flatten_term (ren z q) = map (ren z) (flatten_term q).
Proof. by elim: q => [p|d|v|f Hf a Ha]; rewrite//= map_rcons Hf. Qed.

Lemma H_head_ren_aux m hd q x y z w:
  all (refresh_for y) hd -> all (refresh_for x) hd ->
  all (refresh_for z) q -> all (refresh_for w) q ->
  [disjoint codomf z & codomf x] ->
  H_head u m (map (ren z) q) (map (ren x) hd) = false ->
  H_head u m (map (ren w) q) (map (ren y) hd) = false.
Proof.
  move=> ++++ D2.
  elim: m hd q => [|m tl IH] hd q//.
  case: q; case: hd => //= c cs d ds.
  move => /andP[gyf2 gya2] /andP[gxf1 gxa1] /andP[gzf1 gza1] /andP[gwf1 gwa1].
  case: m => //=; last by apply: IH.
  case U: unify => [s'|]/= H.
    case : unify => //= _; apply/IH/H => //=.
  case H_head; rewrite (andbT,andbF)//=.
  move /isNoneP: U.
  apply: contraNF.
  apply/unif_ren => //.
  apply: fdisjointWl (vars_tm_ren_sub (proj1 (andP gxf1))) _.
  apply: fdisjointWr (vars_tm_ren_sub (proj1 (andP gzf1))) _.
  by rewrite fdisjoint_sym.
Qed.

Lemma good_ren_fresh s t q: 
  vars_tm t `<=` vars_tm q -> vars_tm q `<=` s -> refresh_for (fresh_tm s empty q).2 t.
Proof.
  move=> Hx H.
  have:= @fresh_tm_def s empty q.
  rewrite/refresh_for.
  rewrite /=fsub0set injectiveb0 => /(_ isT H isT).
  move=> [x [H1 HH I1 D1]]; rewrite cat0f in H1; subst.
  apply/andP; split => //.
  by apply/fsubset_trans/fresh_tm_sub1.
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

Lemma H_head_ren m fv1 fv2 t xs fx fy q:
  (lang.rename (fresh_rules fv1 xs).1 t empty).1.1 `<=` fx ->
  (lang.rename (fresh_rules fv2 xs).1 t empty).1.1 `<=` fy ->
  H_head u m (flatten_term (lang.rename fx q empty).2) (flatten_term (lang.rename (fresh_rules fv1 xs).1 t empty).2) = false ->
  H_head u m (flatten_term (lang.rename fy q empty).2) (flatten_term (lang.rename (fresh_rules fv2 xs).1 t empty).2) = false.
Proof.
  move=> H1 H2.
  rewrite/lang.rename!push/= in H1 H2 *.
  rewrite !flatten_term_ren.
  apply/H_head_ren_aux => //=; only 1-4: by apply/good_ren_fresh_all; rewrite (vars_tms_flatten_term, fsubsetUl)//.
  apply: fdisjointWr (disj_codom0R _ _).
  apply: fsubset_trans (fresh_tm_codom2 _ _ _) _.
  rewrite codomf0 fset0U//.
Qed.

Lemma callable_rename1 p fv1 hd mp: 
  (get_tm_hd (lang.rename fv1 hd mp).2 == inl p) = (get_tm_hd hd == inl p).
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
  select_head u p (flatten_term (lang.rename fx hd empty).2) m FRS1.2 = [::] ->
  select_head u p (flatten_term (lang.rename fy hd empty).2) m FRS2.2 = [::].
Proof.
  elim: rs fx fy fv1 fv2 m hd => //= x xs IH fx fy fv1 fv2 m hd; rewrite !push/=.
  move=> H2 H3.
  rewrite !(head_fresh_rule, eq_sym (inl p), callable_rename1).
  case: eqP => //= Hd; last first.
    apply: IH.
      by apply/fsubset_trans/H2/fresh_rule_sub.
    by apply/fsubset_trans/H3/fresh_rule_sub.
  case H: H_head => //=.
  rewrite /fresh_rule!push/= in H2 H3.
  have {}H2' := fsubset_trans (fresh_atoms_sub _ _ _) H2.
  have {}H3' := fsubset_trans (fresh_atoms_sub _ _ _) H3.
  have {}H2' := fsubset_trans (vars_tm_rename _ _) H2'.
  have {}H3' := fsubset_trans (vars_tm_rename _ _) H3'.
  case HH: H_head; last first.
    apply: IH; (apply:fsubset_trans; first apply: fresh_rule_sub); rewrite/fresh_rule?push//=.
  exfalso; apply: negP (negbT (negbF HH)); rewrite negbK; apply: negbT.
  apply: H_head_ren H.
    by apply: fsubset_trans H2; apply: fsubset_trans (fresh_atoms_sub _ _ _).
  by apply: fsubset_trans H3; apply: fsubset_trans (fresh_atoms_sub _ _ _).
Qed.

Lemma build_and (a b: bool): a -> b -> a && b. by move=> ??; apply/andP. Qed.

Lemma mut_exclP p fv c s1:
  mut_excl u p -> 
    tm_is_det p c ->
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
  set FC2:= lang.rename _ _ _.
  set FC1:= lang.rename _ _ _.
  move=> H/= /esym/callable_rename B.
  rewrite {1}/FC1 (proj2 (callable_rename _ hd p empty))//.
  rewrite in_fnd (is_det_lookup _ DF TD)//=.
  have: good_mode (flatten_mode s.[pP]).
    move: GM; rewrite /good_modes/flatten_mode.
    by move=> /forallP /(_ [` pP]); rewrite valPE.
  move: H; move: (flatten_mode _) => m H GM'.
  apply isSomeP in H.
  rewrite !has_cut_seq_fresh.
  case CS: has_cut_seq; first by case: select => [?[|[]]].
  case SH: select_head => // _.
  have {SH}/(_  (vars_sigma s1 `|` vars_tm (deref s1 c) `|` fv)) := select_head_ren (fsubset_refl _) (fsubset_refl _) SH.
  rewrite -/FRS2-/FC2.
  move=> HS.
  have ->// : (select u p (flatten_term (deref s1 c)) m FRS2.2 s1).2 = [::].
  apply: HSH H HS => //=.
  - by apply: fdisjoint_ftr (acyclic_deref_disjoint _ AS).
  - by apply: fdisjoint_ftl (disjoint_varsU _ _).
  - by apply/fdisjoint_ftl/fdisjointWl/disjoint_varsU1/fsubsetP => x H; rewrite !inE H orbT.
  - rewrite fdisjoint_sym; apply/fdisjoint_ft2/fdisjointWr/vars_tm_rename_disjoint.
    by apply/fsubset_trans/fresh_rules_sub/fsubsetP => x H; rewrite !inE H orbT.
  - by apply: fdisjointWl (disjoint_varsU1 _ _); rewrite -fsetUA fsubsetUl.
  - apply: fdisjoint_ftr.
    rewrite fdisjoint_sym; apply: fdisjointWr (vars_tm_rename_disjoint _ _).
    by apply: fsubset_trans (fresh_rules_sub _ _); rewrite -fsetUA fsubsetUl.
Qed.

Print  Assumptions  mut_exclP.


Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

Definition all_cut p :=  all_rs_cut (rules p).

Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

Lemma all_cut_select_head p t m rs fv:
  all_rs_cut rs ->
  all_rs_cut (select_head u p t m (fresh_rules fv rs).2).
Proof.
  elim: rs m fv p t => //=[[hd bo]]/= rs IH m fv p t /andP[H1 H2].
  rewrite !push/= head_fresh_rule; case:eqP => //=; last by eauto.
  case:ifP => //=; eauto.
  rewrite premises_fresh_rule/= has_cut_seq_fresh H1; eauto.
Qed.

Lemma all_cut_mut_excl p: good_modes p.(sig) -> all_cut p -> mut_excl u p.
Proof.
  rewrite/all_cut/mut_excl push/= => ->/=.
  case: p => /= + s.
  elim => //= [[hd bo]] rs/= IH; rewrite !push/=.
  move=> /andP[HBO] H; rewrite IH// andbT.
  rewrite/fresh_rule !push/=/mut_excl_head/=.
  case tm: get_tm_hd => //=[p]; case: fndP => //= kp.
  (* rewrite push. *)
  case: ifP => // ds.
  set R1 := lang.rename _ _ _.
  case S: select_head => //=[r' rs'].
  rewrite has_cut_seq_fresh HBO/=.
  set X := lang.rename (fresh_rules fset0 rs).1 hd empty.
  have:= all_cut_select_head p (flatten_term R1.2) (flatten_mode s.[kp]) fset0 H.
  by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
Qed.



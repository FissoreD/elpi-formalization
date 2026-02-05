From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif.


Section mut_excl.
  Variable u : Unif.

  Fixpoint H_head (ml : list mode) (q : Callable) (h: Callable) : bool :=
    match ml,q,h with
    | [::], Callable_P c, Callable_P c1 => c == c1
    | [:: i & ml], (Callable_App q a1), (Callable_App h a2) => u.(unify) a1 a2 fmap0 && H_head ml q h
    | [:: o & ml], (Callable_App q a1), (Callable_App h a2) => H_head ml q h
    | _, _, _ => false
    end.
  
  (* Definition unif_head := H_head empty. *)

  Fixpoint select_head (query : Callable) (modes:list mode) (rules: list R) : (seq R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head query modes rules in
      if H_head modes query rule.(head) then rule :: tl else tl
    end.
  
  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    let query := r.(head) in
    match tm2RC (Callable2Tm query) with
      | None => true (*a callable against a non rigid term is OK: failure at runtime*)
      | Some (query, kp) =>
        match sig.[? kp] with 
          | Some sig => 
            if is_det_sig sig then 
              let rs := select_head query (get_modes_rev query sig) rules in
              all_but_last (fun x => has_cut_seq x.(premises)) (r::rs)
            (* ignoring checking for vars *)
            else true
          (*a callable against a rigid term non in sig OK: failure at runtime*)
          | None => true
          end
      end.

  Fixpoint mut_excl_aux sig rules :=
    match rules with
    | [::] => true
    | x :: xs => mut_excl_head sig x xs && mut_excl_aux sig xs
    end.

  Definition mut_excl sig rules :=
    let: (fv, rules) := fresh_rules fset0 rules in
    mut_excl_aux sig rules.

  Lemma head_fresh_rule fv r:
    head (fresh_rule fv r).2 = (fresh_callable fv r.(head)).2.
  Proof.
    destruct r; rewrite/fresh_rule/= 1!push.
    case bc: fresh_atoms => [fv' A']//=.
  Qed.

  Lemma head_fresh_premises fv r:
    premises (fresh_rule fv r).2 = (fresh_atoms (fresh_callable fv r.(head)).1 r.(premises)).2.
  Proof.
    destruct r; rewrite/fresh_rule/= 1!push.
    generalize (fresh_callable fv head) => -[{}fv/=b].
    case FA: fresh_atoms => [b1 a']//=.
  Qed.

     (* sufficient modes length for callable t *)
  Fixpoint suff_mode (t:Callable) (m:seq mode) :=
    match m, t with
    | [::], Callable_P _ => true
    | [:: _ & xs], Callable_App x _ => suff_mode x xs
    | _, _ => false
    end.

  Lemma HH q' hd qp m :
    suff_mode hd m -> tm2RC (Callable2Tm hd) = Some (q', qp) ->
    H_head m q' hd.
  Proof.
    elim: hd m qp q' => //=[p [|_ _]|f Hf a [|m0 ms]]//= qp q' sm.
      by move=> [<-]; rewrite //= eqxx.
    case X: tm2RC => [[q2 qp2]|]//=[??]; subst.
    have:= Hf _ _ _ sm X.
    case: m0 => //=; case: H_head => //=.
    by rewrite unif_refl.
  Qed.

  Lemma H_head_refl m t: suff_mode t m -> H_head m t t.
  Proof.
    elim: m t => //=[|m l IH] []//=.
    move=> c t H; case: m; auto.
    have:= IH c H; case: H_head => //= > _.
    by rewrite unif_refl.
  Qed.

  Lemma tm2RC_rigid_deref c1 d1 h1 d2 h2 s1 s2 fv1 fv m c:
    tm2RC (Callable2Tm (fresh_callable fv1 c1).2) = Some (d1, h1) ->
    H u m d2 (fresh_callable fv c1).2 s1 = Some s2 ->
    tm2RC c = Some (d2, h2) -> h1 = h2.
  Proof.
    elim: c1 d1 h1 d2 h2 s1 s2 fv fv1 m c => //=[p|f Hf r] d1 h1 d2 h2 s1 s2 fv fv1 m c.
      move=> [??]; subst.
      case: m => /=[|[] _]; case: d2 => //p; case: eqP => //=-> _.
      elim: c h1 h2 => //=[>[<-<-]|]//f Hf a Ha h1 h2.
      by case X: tm2RC => //[[c1 p1]][//].
    rewrite !push/=.
    case H: tm2RC => [[C P]|]//=[??]; subst.
    have {H}Hf := Hf _ _ _ _ _ _ _ _ _ _ H.
    case m => [|[]]//=; case: d2 => //= c1 t1 l1;
    case H: H => //=[s3]; have {}Hf := Hf _ _ _ _ _ _ _ H;
    case: c => //= f' a'; case tm: tm2RC => //=[[c' p']]/= + [???]; subst;
    have:= Hf _ _ tm => //.
  Qed.

  Lemma tm2RC_get_modes d1 d2 h2 s1 s2 fv m c l:
    H u m d2 (fresh_callable fv d1).2 s1 = Some s2 ->
    tm2RC c = Some (d2, h2) -> 
      get_modes_rev d1 l = get_modes_rev d2 l.
  Proof.
    elim: d1 d2 h2 s1 s2 fv m c l => //=[p|f Hf r] d2 h2 s1 s2 fv m c l.
      by case: m => //=[|[] _]; case: d2 => //=.
    rewrite !push/=.
    case m => [|[]]//=; case: d2 => //= c1 t1 l1;
    case H: H => //=[s3]; have {}Hf := Hf _ _ _ _ _ _ _ _ H;
    case: c => //= f' a'; case tm: tm2RC => //=[[c' p']]/= + [???]; subst;
    have:= Hf _ _ _ tm => //; case: l => //=;
    rewrite/get_modes_rev/=/sigtm_rev/sigtm/=!add0n => m1 ml mr IH _;
    by rewrite !rev_cons/=!map_rcons/= IH.
  Qed.


  Lemma H_suff_mode l q fv hd s1 s2:
    H u l q (fresh_callable fv hd).2 s1 = Some s2 -> suff_mode hd l.
  Proof.
    elim: l hd q s1 s2 fv => //=.
      move=> hd []//= p s1 s2 fv; case fc: fresh_callable => [fv' [p'|]]/=//.
      case: eqP => //? [?]; subst.
      by case: hd fc => //= c t; rewrite !push.
    move=> m l IH hd q s1 s2 fv.
    case: m; case: q => //= c t; case fc: fresh_callable => [fv' [|f a]]//=;
    case H: H => [s3|]//=; move: fc; case: hd => //=[f' a']; rewrite !push;
    move=> [???]; subst => H1; apply: IH H.
  Qed.

  Lemma tm2RC_Callable hd:
    exists r, tm2RC (Callable2Tm hd) = Some r /\ r.1 = hd.
  Proof.
    elim: hd => //=[p|f [[c p] [H1 H2]] a]; first by repeat eexists.
    rewrite H1; subst; repeat eexists.
  Qed.

  Lemma fsetUE0 {T: choiceType} (A B:{fset T}):
    A `|` B = fset0 -> A = fset0 /\ B = fset0.
  Proof.
    move=> /fsetP H; split; apply/fsetP => x;
    have := H x; rewrite in_fsetU; case xA: (_ \in A) => //=.
  Qed.

  Lemma fsetU0E {T: choiceType} (A B:{fset T}):
    A = fset0 -> B = fset0 -> A `|` B = fset0.
  Proof. by move=> ->->; rewrite fsetU0. Qed.

  (* f X 3 = f 4 X non unifica, ma se cambio le variabili allora si, attenzione! *)


  Lemma vars_tm2rc t x:
    tm2RC t = Some x ->
    vars_tm (Callable2Tm x.1) = vars_tm t.
  Proof.
    elim: t x => //=[q|f Hf a Ha][c p]; first by move=> [<-].
    case X: tm2RC => //[[c' p']][<-<-]/=.
    by rewrite (Hf _ X).
  Qed.

  Lemma varsUP x l:
    forall t, x \in vars_tm t -> t \in l -> x \in varsU [seq vars_tm e | e <- l].
  Proof.
    elim: l x => //= x xs IH v t H.
    rewrite in_fsetU in_cons => /orP[/eqP|] H1; subst; first by rewrite H.
    by rewrite (IH _ _ H H1) orbT.
  Qed.

  Lemma codom_sub v (s1:Sigma) (vP : v \in domf s1): 
    vars_tm s1.[vP] `<=` varsU [seq vars_tm e | e <- codom s1].
  Proof.
    apply/fsubsetP => x H.
    have: s1.[vP] \in codom s1 by apply/codomP; repeat eexists.
    move: H; generalize (s1.[vP]) (codom s1) => +l; clear.
    by apply: varsUP.
  Qed.

  Lemma vars_deref t fv s1:
    vars_tm t `<=` fv ->
    vars_sigma s1 `<=` fv ->
    vars_tm (deref s1 t) `<=` fv.
  Proof.
    elim: t fv s1 => //[v|f Hf a Ha] fv s1/=.
      move=> H1; case: fndP => vP//=.
      rewrite/vars_sigma fsubUset /codom_vars => /andP[H2 H3].
      apply/fsubset_trans/H3/codom_sub.
    rewrite 2!fsubUset => /andP[H1 H2] H3.
    rewrite Hf//Ha//.
  Qed.

  Lemma tm2RC_Callable2 c s1 fv r:
    vars_tm (Callable2Tm c) `<=` fv -> vars_sigma s1 `<=` fv ->
    tm2RC (deref s1 (Callable2Tm c))  = Some r ->
      vars_tm (Callable2Tm r.1) `<=` fv.
  Proof.
    elim: c s1 fv r => [p|f Hf a] s1 fv r/=; first by move=> H1 H2 [<-]//.
    rewrite fsubUset => /andP[S1 S2] S3; case H: tm2RC => [[c p]|]//=[<-]/=.
    by rewrite fsubUset (Hf _ _ _ S1 S3 H) vars_deref//.
  Qed.

  Lemma fresh_tm_domf_sub f m a:
    domf m `<=` domf (fresh_tm f m a).2.
  Proof.
    elim: a m f => //=[v|f Hf a Ha] m fs.
      by case: (fndP m) => //= H; rewrite fsubsetU// mem_fsetD1// fsubset_refl.
    rewrite !push/=; apply/fsubset_trans/Ha/Hf.
  Qed.

  Lemma fresh_tm_sub1 fv m t:
    vars_tm t `<=` domf (fresh_tm fv m t).2.
  Proof.
    elim: t fv m => //=[v|f Hf a Ha] fv m.
      rewrite !fsub1set.
      by case: (fndP m) => //=; rewrite in_fsetU in_fset1 eqxx orbT.
    rewrite !push/= !fsubUset; apply/andP; split; last by apply: Ha.
    apply/fsubset_trans/fresh_tm_domf_sub/Hf.
  Qed.

  Lemma fresh_tm_sub_all fv t:
    let x := fresh_tm (vars_tm t `|` fv) empty t in
      [/\ domf x.2 `<=` x.1, codomf x.2 `<=` x.1 & vars_tm t `<=` domf x.2].
  Proof.
    set vt := vars_tm _ `|` _.
    move=> ft.
    have->//:= @fresh_tm_dom vt empty t (fsubsetUl _ _) (fsub0set _).
    have->//:= @fresh_tm_codom_fv vt empty t; last by rewrite codomf0 fsub0set.
    by have->:= fresh_tm_sub1 vt empty t.
  Qed.

  Lemma vars_tm_rename fv t:
    vars_tm (rename fv t).2 `<=` (rename fv t).1.
  Proof.
    rewrite/rename push/=.
    set vt := vars_tm _ `|` _.
    set ft := fresh_tm vt _ _.
    have/=[]:= fresh_tm_sub_all fv t; rewrite -/ft.
    move=> H1 H2 H3.
    have:= fsubset_trans H3 H1; move: H1 H2; clear H3.
    clear; rewrite/ren; move: vt ft => _ []/=.
    elim: t => //=[v|f Hf a Ha] fs mp.
      case: fndP => //= H1; rewrite ffunE/= valPE.
      move=> H2 /fsubsetP /(_ mp.[H1]) H H3.
      by rewrite fsub1set; apply/H/codomfP; exists v; rewrite in_fnd.
    rewrite !fsubUset => H3 H4 /andP[H1 H2].
    apply/andP; split; [apply: Hf|apply: Ha] => //.
  Qed.

  Lemma disjoint_sub {T: choiceType} (s1 s2 s3: {fset T}):
    s1 `&` s2 = fset0 ->
    s3 `<=` s2 -> s1 `&` s3 = fset0.
  Proof.
    move=> /fsetP I /fsubsetP S; apply/fsetP => x.
    have:= I x; have:= S x.
    rewrite !in_fsetI; case: (x \in s1) => //=.
    by case: (_ \in s3) => //=->//.
  Qed.

  Lemma codom_sub1 {T : choiceType} (b: {fmap T -> T}) r :
    codomf b.[\r] `<=` codomf b.
  Proof.
    apply/fsubsetP => x /codomfP [v].
    rewrite fnd_restrict; case: ifP => //= H; case: fndP => // vb [?]; subst.
    by apply/codomfP; exists v; rewrite in_fnd.
  Qed.

  Lemma fresh_good_codom_aux x fv m t: 
    fv `<=` x ->
    fv `&` codomf m = fset0 -> fv `&` codomf (fresh_tm x m t).2 = fset0.
  Proof.
    elim: t m fv x => //=[v|f Hf a Ha] m fv x H1 H2.
      case: (fndP m) => //=.
      move=> H; rewrite codomf_cat.
      rewrite fsetIUr; apply/fsetU0E; last first.
        apply/disjoint_sub/codom_sub1/H2.
      apply/fsetP => k; rewrite in_fsetI.
      case kP: (k \in fv) => //=.
      have kx := fsubsetP H1 k kP.
      case: (boolP (_ \in _)) => ///codomfP [y].
      case: fndP => //= /[dup]; rewrite {1}in_fset1 => /eqP?; subst.
      move=> kf; rewrite ffunE => -[?]; subst.
      by rewrite freshPwr in kx.
    rewrite !push/=.
    apply/Ha/Hf => //.
    by apply/fsubset_trans/fresh_tm_sub.
  Qed.

  Lemma fresh_good_codom fv t: fv `&` codomf (fresh_tm fv empty t).2 = fset0.
  Proof. by apply/fresh_good_codom_aux; rewrite// codomf0 fsetI0. Qed.

  Lemma ren_mp m t:
    vars_tm t `<=` domf m -> vars_tm (ren m t) `<=` codomf m.
  Proof.
    rewrite/ren.
    elim: t => //[v|f Hf a Ha]/=.
      rewrite fsub1set => H.
      rewrite in_fnd//=ffunE valPE/= fsub1set.
      by apply/codomfP; exists v; rewrite in_fnd.
    rewrite !fsubUset => /andP[H1 H2].
    by rewrite Hf//Ha//.
  Qed.

  Lemma vars_tm_rename_disjoint fv t:
    vars_tm (rename fv t).2 `&` fv = fset0.
  Proof.
    rewrite/rename push/=.
    have[]/=:= fresh_tm_sub_all fv t.
    set vt := vars_tm _ `|` _.
    have /= := fresh_good_codom vt t.
    set ft := fresh_tm vt _ _.
    move=> D H1 H2 VT.
    have VTR := ren_mp VT.
    rewrite fsetIC.
    apply: disjoint_sub VTR.
    rewrite !(fsetIC _ (codomf _)) in D *.
    apply: disjoint_sub D _.
    by rewrite/vt fsubsetUr.
  Qed.

  Lemma disjoint_tm_sub t1 t2 fv2:
    vars_tm t1 `<=` fv2 ->
    disjoint_tm (rename fv2 t2).2 t1.
  Proof.
    have:= vars_tm_rename_disjoint fv2 t2.
    rewrite/rename !push/=.
    set vt := (vars_tm _ `|` _).
    set ft := (fresh_tm _ _ _).
    by apply: disjoint_sub.
  Qed.

  Lemma disjoint_comm a b: disjoint_tm a b = disjoint_tm b a.
  Proof. rewrite/disjoint_tm fsetIC//. Qed.


  Lemma H_head_None m q hd1 hd2 s1 s2 fv1 fv2 fv3 fv4:
    vars_tm (Callable2Tm q) `<=` fv1 -> vars_sigma s1 `<=` fv1 ->
    vars_tm (Callable2Tm q) `<=` fv4 -> vars_sigma s1 `<=` fv4 ->
    (fresh_callable fv3 hd2).1 `<=` fv2 ->
    H u m q (fresh_callable fv1 hd1).2 s1 = Some s2 ->                                (*q   ~  hd1*)
    H_head m (fresh_callable fv2 hd1).2 (fresh_callable fv3 hd2).2 = false ->  (*hd1 <> hd2*)
    H u m q (fresh_callable fv4 hd2).2 s1 = None.                                     (*hd2 <> q*)
  Proof.
    elim: m q hd1 hd2 s1 s2 fv1 fv2 fv3 fv4 => [|x xs IH] q hd1 hd2 s1 s2 fv1 fv2 fv3 fv4/=.
      case: q => //=; case: hd1 => //=; last by move=>>; rewrite !push.
      case: hd2 => /=; last by move=>>; rewrite !push.
      move=> >; repeat case: eqP => //; congruence.
    case: q => //=; first by case: x.
    move=> qf qa.
    case: hd1 => /=; first by case: x.
    move=> hd0f hd0a.
    rewrite !push/=.
    case: hd2 => /=; first by case: x.
    move=> hd1f hd1a.
    rewrite !push/=.
    rewrite !(fsubUset _ (vars_tm (Callable2Tm qf))) => /andP[D1 D2] DS1 /andP[D3 D4] DS2 D5.
    have {}IH := IH _ hd0f _ _ _ _ _ _ _ D1 DS1 D3 DS2.
    case: x; last first.
      case H: H => //=[s1'] U HD.
      rewrite (IH _ _ _ _ _ H HD)//=.
      by apply/fsubset_trans/D5/rename_sub.
    move: D5.
    set F3:= fresh_callable _ _.
    set F1:= fresh_callable _ _.
    set F2:= fresh_callable _ _.
    set F4:= fresh_callable _ _.
    case H: H => //=[s1'] D5 M.
    case HH: H_head; rewrite (andbF, andbT)/=; last first.
      rewrite (IH _ _ _ _ _ H HH)//=.
      apply/fsubset_trans/D5/rename_sub.
    case U: unify => //= _.
    clear IH.
    case X: lang.H => //[s1'']/=.
    apply: unif_help U M.
      apply: disjoint_tm_sub.
      rewrite/F2/=; apply/fsubset_trans/fresh_callable_sub.
      apply/fsubset_trans/D5/vars_tm_rename.
    - rewrite/F1 disjoint_comm; apply/disjoint_tm_sub.
      by apply/fsubset_trans/fresh_callable_sub.
    - rewrite/F4 disjoint_comm; apply/disjoint_tm_sub.
      by apply/fsubset_trans/fresh_callable_sub.
  Qed.

  Lemma select_head_nil fv fv1 fv2 fv3 rs hd s1 s2 q m:
    let FC := fresh_rules fv2 rs in
    vars_tm (Callable2Tm q) `<=` fv1 -> vars_sigma s1 `<=` fv1 ->
    vars_tm (Callable2Tm q) `<=` fv -> vars_sigma s1 `<=` fv ->
    FC.1 `<=` fv3 ->
    (* vars_tm (Callable2Tm (fresh_callable fv3 hd).2) `<=` vars_tm (Callable2Tm (fresh_callable fv1 hd).2) -> *)
    H u m q (fresh_callable fv1 hd).2 s1 = Some s2 ->     (*hd ~ q*)
    select_head (fresh_callable fv3 hd).2 m (FC).2 = [::] ->                       (*select hd' rs =  [::]*)
    (select u q m (fresh_rules fv rs).2 s1).2 = [::]. (*select q   rs' = [::]*) 
  Proof.
    elim: rs fv fv1 fv2 hd s1 s2 q m => //=.
    move=> x xs IH fv fv1 fv2 hd s1 s2 q m D1 S1 D2 S2 + H.
    rewrite !push/= => HH.
    case Hd: H_head => //= SH.
    have D3 : (fresh_rules fv2 xs).1 `<=` fv3.
      by apply/fsubset_trans/HH/fresh_rule_sub.
    have {}IH := IH _ _ _ _ _ _ _ _ D1 S1 D2 S2 D3 H SH.
    case H1: lang.H => [s1'|]//=.
    rewrite !push/= {}IH.
    exfalso.
    case: x HH Hd H1 => /= hd0 pm0.
    rewrite !head_fresh_rule/=; clear SH.
    move: H.
    set FR1:= fresh_rules _ _.
    set FR2:= fresh_rules _ _.
    set hdF1:= fresh_callable _ _.
    set hdF2:= fresh_callable _ _.
    set hd0F1:= fresh_callable _ _.
    set hd0F:= fresh_callable _ _.
    move=> + B => H1 H2.
    rewrite (H_head_None _ _ _ _ _ H1 H2)//.
      by apply/fsubset_trans/fresh_rules_sub.
    - by apply/fsubset_trans/fresh_rules_sub.
    apply/fsubset_trans/B.
    rewrite /fresh_rule/=!push/=.
    apply/fresh_atoms_sub.
  Qed.

  (* Lemma count_tm_ag_fresh: *)

  Lemma get_modes_rev_fresh fs hd m:
    get_modes_rev (fresh_callable fs hd).2 m = get_modes_rev hd m.
  Proof.
    rewrite/get_modes_rev/sigtm_rev; do 2 f_equal.
    rewrite/sigtm/=; f_equal.
    elim: hd fs {m} => //= f Hf a fs; rewrite !push/= Hf//.
  Qed.

  Lemma suff_mode_fresh hd m fv:
    suff_mode hd m -> suff_mode (fresh_callable fv hd).2 m.
  Proof.
    elim: hd m fv => //=f Hf a []//=m ml fv H.
    rewrite !push/= Hf//.
  Qed.

  Lemma has_cut_seq_fresh fv1 fv2 bo:  
    has_cut_seq (fresh_atoms fv1 bo).2 = has_cut_seq (fresh_atoms fv2 bo).2.
  Proof.
    elim: bo fv1 fv2 => //= x xs IH fv1 fv2; rewrite !push/= (IH fv1 fv2)//.
    by case: x => //=c; rewrite !push//=.
  Qed.

  Lemma mut_exclP s rs fv c s1:
    vars_tm (Callable2Tm c) `<=` fv ->
    vars_sigma s1 `<=` fv ->
    mut_excl s rs -> 
      tm_is_det s c ->
        all_but_last (fun x => has_cut_seq x.2) (bc u {|sig:=s; rules := rs|} fv c s1).2.
  Proof.
    rewrite/bc.
    case DR: tm2RC => //=[[q p]].
    case: fndP => //= pP.
    rewrite/mut_excl !push/=.
    (* move: fset0. *)
    elim: rs s c s1 fv q p pP DR => [|[hd bo] rs IH]//= s c s1 fv q p pP DF D1 D2 + TD.
    rewrite !push/=.
    move=> /andP[+ ME].
    have:= IH _ _ _ _ _ _ pP DF D1 D2 ME TD.
    set FRS1 := fresh_rules _ _.
    set FRS2 := fresh_rules _ _.
    set FS1 := fresh_rule _ _.
    set FS2 := fresh_rule _ _.
    move=> {}IH.
    case H: H => [s2|]//; rewrite !push/={}IH andbT.
    have TD' := tiki_taka DF TD H.
    move: H; rewrite/FS2.
    rewrite/FS1 head_fresh_rule/=/fresh_rule/=!push/=.
    rewrite/mut_excl_head.
    set FC1:= fresh_callable _ _.
    set FC2:= fresh_callable _ _.
    have [[? p1] [H1 /=H2]]:= tm2RC_Callable FC2.2; subst; rewrite H1.
    move=> H.
    have ? := tm2RC_rigid_deref H1 H DF; subst.
    rewrite in_fnd//=.
    move: TD'; rewrite/FS2 head_fresh_rule/= -/FC1 => TD'.
    have:= tm_is_det_tm2RC s1 TD; rewrite DF => -[q'[p' [kp' [[??] IS]]]]; subst.
    rewrite (bool_irrelevance kp' pP) in IS.
    clear kp'.
    have := H_suff_mode H.
    have MEQ := (tm2RC_get_modes _ H DF).
    rewrite -{}MEQ in H *.
    rewrite{1}/FC2 get_modes_rev_fresh IS.
    move: H; generalize (get_modes_rev hd s.[pP]) as m => m H SM.
    rewrite (has_cut_seq_fresh _ FC1.1).
    case CS: has_cut_seq; first by case: select => [?[|[]]].
    case SH: select_head => //.
    (* have Hx := vars_deref D1 D2. *)
    have Hy := tm2RC_Callable2 D1 D2 DF.
    rewrite (select_head_nil _ _ _ _ _ H SH)//=;
    by rewrite/FRS1;apply/fsubset_trans/fresh_rules_sub.
  Qed.

End mut_excl.



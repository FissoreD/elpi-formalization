From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif.


Section mut_excl.
  Variable u : Unif.

  Fixpoint H_head (ml : list mode) (q : Tm) (h: Tm) : bool :=
    match ml,q,h with
    | [::], Tm_P c, Tm_P c1 => c == c1
    | [:: m & ml], (Tm_App q a1), (Tm_App h a2) => 
      ((m == o) || u.(unify) a1 a2 fmap0) && H_head ml q h
    | _, _, _ => false
    end.
  
  Fixpoint select_head (query : Tm) (modes:list mode) (rules: list R) : (seq R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head query modes rules in
      if H_head modes query rule.(head) then rule :: tl else tl
    end.
  
  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    let query := r.(head) in
    match get_tm_hd query with
      | inl kp =>
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

  Lemma head_fresh_rule fv r:
    head (fresh_rule fv r).2 = (rename fv r.(head) fmap0).2.
  Proof.
    destruct r; rewrite/fresh_rule/= !push.
    case bc: fresh_atoms => [fv' A']//=.
  Qed.

  Lemma premises_fresh_rule fv r:
    premises (fresh_rule fv r).2 = 
      let fh := fresh_tm (vars_tm r.(head) `|` fv) fmap0 r.(head) in
      (fresh_atoms fh.1 r.(premises) fh.2).2.
  Proof.
    destruct r; rewrite/fresh_rule/= !push/=.
    rewrite/rename !push//=.
  Qed.

     (* sufficient modes length for callable t *)
  Fixpoint suff_mode (t:Tm) (m:seq mode) :=
    match m, t with
    | [::], Tm_P _ => true
    | [:: _ & xs], Tm_App x _ => suff_mode x xs
    | _, _ => false
    end.

  Lemma H_suff_mode l q fv hd s1 s2 md:
    H u l q (rename fv hd md).2 s1 = Some s2 -> suff_mode hd l.
  Proof.
    rewrite/rename !push/=.
    move: (fresh_tm _ _ _) => -[]/= _.
    elim: l q hd s1 s2 {fv md} => //=.
      move=> []//=p hd s1 s2 b; case: eqP => ///esym/[dup].
      by move=>/ren_isP[p'->]/=.
    move=> m ms IH []//=f1 a1 hd s1 s2 fv.
    case R: ren => //=[f a].
    move: (R) => /ren_isApp[f2[a2?]]/=; subst; move: R.
    rewrite ren_app => -[<- _].
    case H: H => //= _.
    apply: IH H.
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

  (* Lemma vars_tm_rename fv t m:
    vars_tm (rename fv t m).2 `<=` (rename fv t m).1.1.
  Proof.
    rewrite/rename push/=.
    set vt := vars_tm _ `|` _.
    set ft := fresh_tm vt _ _.
    have/=[]:= fresh_tm_sub_all fv t; rewrite -/ft.
    move=> H1 H2 H3.
    have:= fsubset_trans H3 H1; move: H1 H2; clear H3.
    clear; rewrite/ren; move: vt ft => _ []/=.
    elim: t m => //[v|f Hf a Ha] fs mp m.
      rewrite [vars_tm _]/=/fresh_tm !inE cat0f codomf0 fsetU0/=.
      rewrite FmapE.fmapE.
      rewrite codomfE.
      case: fndP => //= H1; rewrite ffunE/= valPE.
      move=> H2 /fsubsetP /(_ mp.[H1]) H H3.
      by rewrite fsub1set; apply/H/codomfP; exists v; rewrite in_fnd.
    rewrite !fsubUset => H3 H4 /andP[H1 H2].
    apply/andP; split; [apply: Hf|apply: Ha] => //.
  Qed. *)

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

  (* Lemma vars_tm_rename_disjoint fv t:
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
  Qed. *)

  (* Lemma disjoint_tm_sub t1 t2 fv2:
    vars_tm t1 `<=` fv2 ->
    disjoint_tm (rename fv2 t2).2 t1.
  Proof.
    have:= vars_tm_rename_disjoint fv2 t2.
    rewrite/rename !push/=.
    set vt := (vars_tm _ `|` _).
    set ft := (fresh_tm _ _ _).
    by apply: disjoint_sub.
  Qed. *)

  Lemma disjoint_comm a b: disjoint_tm a b = disjoint_tm b a.
  Proof. rewrite/disjoint_tm fsetIC//. Qed.

  Lemma H_head_None_ren m q hd1 hd2 s1 s2 m1 m2 m3 m4:
    disjoint_tm q (ren m1 hd1) ->
    disjoint_tm q (ren m4 hd2) ->
    disjoint_tm (ren m2 hd1) (ren m3 hd2) ->
    H u m q  (ren m1 hd1) s1 = Some s2 ->           (*q   ~  hd1*)
    H_head m (ren m2 hd1) (ren m3 hd2) = false ->  (*hd1 <> hd2*)
    H u m q  (ren m4 hd2) s1 = None.                (*hd2 <> q*)
  Proof.
    rewrite/disjoint_tm.
    elim: m q hd1 hd2 s1 s2 m1 m2 m3 m4 => [|x xs IH] q hd1 hd2 s1 s2 fv1 fv2 fv3 fv4/=.
      case: q => //=p _ _.
      case: eqP => //=/esym/[dup]/ren_isP[p'->][->]/= _ _.
      case: hd2 => //=[p2|v]; rewrite !(ren_P,ren_V)//=.
      by do 2 case: eqP => //=; congruence.
    case: q => //=f1 a1.
    case: hd1 => // [?|f2 a2]; rewrite !(ren_V,ren_app)//.
    case: hd2 => // [?|f3 a3]; rewrite !(ren_V,ren_app)//=.
    rewrite !fsetIUl !fsetIUr.
    move=> /eqP; rewrite !fsetU_eq0 => /andP[/andP[/eqP H1 /eqP H2] /andP[/eqP H3 /eqP H4]].
    move=> /eqP; rewrite !fsetU_eq0 => /andP[/andP[/eqP H5 /eqP H6] /andP[/eqP H7 /eqP H8]].
    move=> /eqP; rewrite !fsetU_eq0 => /andP[/andP[/eqP H9 /eqP H10] /andP[/eqP H11 /eqP H12]].
    case H: H => //=[s1'] M.
    case: eqP => //=Md; subst.
      move=> HH; rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ H HH)//=.
    case U: unify => [sx|]//=HH.
      rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ H HH)//=.
    case H': lang.H => //=[s1''].
    destruct x => //=.
    apply/unif_help/M/U; rewrite/disjoint_tm//.
  Qed.

  (* Lemma H_head_None m q hd1 hd2 s1 s2 fv1 fv2 fv3 fv4:
    vars_tm q `<=` fv1 -> vars_sigma s1 `<=` fv1 ->
    vars_tm q `<=` fv4 -> vars_sigma s1 `<=` fv4 ->
    (rename fv3 hd2).1 `<=` fv2 ->
    H u m q (rename fv1 hd1).2 s1 = Some s2 ->                 (*q   ~  hd1*)
    H_head m (rename fv2 hd1).2 (rename fv3 hd2).2 = false ->  (*hd1 <> hd2*)
    H u m q (rename fv4 hd2).2 s1 = None.                      (*hd2 <> q*)
  Proof.
    rewrite/rename !push/=.
    move=> V1 V2 V3 V4 V5 H HH.
    apply:H_head_None_ren H HH; rewrite/disjoint_tm.
      set X:= (rename fv1 hd1); set Y := ren _ _.
      replace Y with X.2 by rewrite/X/Y/rename!push//.
      by rewrite fsetIC; apply/disjoint_tm_sub.
    - set X:= (rename fv4 hd2); set Y := ren _ _.
      replace Y with X.2 by rewrite/X/Y/rename!push//.
      by rewrite fsetIC; apply/disjoint_tm_sub.
    move: V5.
    (* set K := fresh_tm _ _ _. *)
    set X:= (rename fv2 hd1); set Y := ren _ _.
    replace Y with X.2 by rewrite/X/Y/rename!push//.
    set Z:= (rename fv3 hd2); set W := ren _ _.
    replace W with Z.2 by rewrite/Z/W/rename!push//.
    set K := fresh_tm _ _ _; move=> H.
    apply/disjoint_tm_sub/fsubset_trans/H.
    replace K.1 with Z.1 by rewrite/K/Z/rename!push//.
    apply: vars_tm_rename.
  Qed. *)

  (*Lemma select_head_nil fv fv1 fv2 fv3 rs hd s1 s2 q m:
    let FC := fresh_rules fv2 rs in
    vars_tm (q) `<=` fv1 -> vars_sigma s1 `<=` fv1 ->
    vars_tm (q) `<=` fv -> vars_sigma s1 `<=` fv ->
    FC.1 `<=` fv3 ->
    H u m q (rename fv1 hd).2 s1 = Some s2 ->         (*hd ~ q*)
    select_head (rename fv3 hd).2 m (FC).2 = [::] ->  (*select hd' rs =  [::]*)
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
    set hdF1:= rename _ _.
    set hdF2:= rename _ _.
    set hd0F1:= rename _ _.
    set hd0F:= rename _ _.
    move=> + B => H1 H2.
    rewrite (H_head_None _ _ _ _ _ H1 H2)//.
      by apply/fsubset_trans/fresh_rules_sub.
    - by apply/fsubset_trans/fresh_rules_sub.
    apply/fsubset_trans/B.
    rewrite /fresh_rule/=!push/=.
    apply/fresh_atoms_sub.
  Qed. *)

  Lemma get_modes_rev_rename fs hd m mp:
    get_modes_rev (rename fs hd mp).2 m = get_modes_rev hd m.
  Proof.
    rewrite/get_modes_rev/sigtm_rev; do 2 f_equal.
    rewrite/sigtm/=; f_equal.
    rewrite/rename !push/=.
    move: (fresh_tm _ _ _) => -[/= _].
    elim: hd => //[v|a Ha f Hf] b.
      by rewrite ren_V.
    by rewrite ren_app/= Ha.
  Qed.

  Lemma has_cut_seq_fresh fv1 bo mp:  
    has_cut_seq (fresh_atoms fv1 bo mp).2 = has_cut_seq bo.
  Proof.
    elim: bo fv1 => //= x xs IH fv1; rewrite !push/= IH//.
    by case: x => //=c; rewrite !push//=.
  Qed.

  (* Definition callable t := match get_tm_hd t with inl t => Some t | _ => None end. *)

  Lemma H_callable m t1 t2 s1 s2 p:
    H u m t1 t2 s1 = Some s2 ->
    get_tm_hd t1 = inl p ->
    get_tm_hd t2 = inl p.
  Proof.
    elim: m t1 t2 s1 s2 p => //=.
      by move=> []//= p []//p' s1 s2; case: eqP => //-[->].
    move=> m ms IH []//f1 a1 []//f2 a2 s1 s2 p.
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
    get_tm_hd c = inl p -> tm_is_det s c -> is_det_sig s.[pP].
  Proof. by elim: c p s pP => //=p1 p2 s pP [->]; rewrite/tm_is_det/=in_fnd//. Qed.

  Lemma count_tm_ag_deref s c p: 
    get_tm_hd c = inl p -> count_tm_ag (deref s c) = count_tm_ag c.
  Proof. by elim: c p s => //=f Hf a Ha p s H; rewrite (Hf p)//. Qed.

  Lemma get_modes_rev_deref c p s1 s: 
    get_tm_hd c = inl p -> get_modes_rev (deref s1 c) s = get_modes_rev c s.
  Proof. by move=> H; rewrite/get_modes_rev/sigtm_rev/sigtm (count_tm_ag_deref _ H)//. Qed.

  Lemma count_tm_ag_H d1 d2 s1 s2 m p:
    H u m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      count_tm_ag d1 = count_tm_ag d2.
  Proof.
    elim: d1 d2 s1 s2 m p => //=[p|f Hf a Ha] d2 s1 s2 m l.
      by case: m => //=; case: eqP => //<-.
    case: m => //= m ms; case: d2 => //= f1 a1; case H: H => //[s1']/= M C.
    by f_equal; apply: Hf H C.
  Qed.

  Lemma get_modes_rev_H d1 d2 s1 s2 m l p:
    H u m d1 d2 s1 = Some s2 ->
    get_tm_hd d1 = inl p -> 
      get_modes_rev d1 l = get_modes_rev d2 l.
  Proof. by move=> H C; rewrite/get_modes_rev/sigtm_rev/sigtm (count_tm_ag_H H C). Qed.

  Lemma mut_exclP p fv c s1:
    vars_tm c `<=` fv ->
    vars_sigma s1 `<=` fv ->
    mut_excl p -> 
      tm_is_det p.(sig) c ->
        all_but_last (fun x => has_cut_seq x.2) (bc u p fv c s1).2.
  Proof.
    rewrite/bc.
    case: p => [rs s]/=+++TD.
    rewrite (is_det_cder _ TD).
    case DR: get_tm_hd => //=[p].
    case: fndP => //= pP.
    rewrite/mut_excl !push/=.
    elim: rs s c s1 fv p pP DR TD => [|[hd bo] rs IH]//= s c s1 fv p pP DF TD D1 D2.
    rewrite !push/=.
    move=> /andP[+ ME].
    have:= IH _ _ _ _ _ pP DF TD D1 D2 ME.
    set FRS1 := fresh_rules _ _.
    set FRS2 := fresh_rules _ _.
    set FS1 := fresh_rule _ _.
    set FS2 := fresh_rule _ _.
    move=> {}IH.
    case H: H => [s2|]//; rewrite !push/={}IH andbT.
    move: H; rewrite/FS2.
    rewrite/FS1 head_fresh_rule/=/fresh_rule/=!push/=.
    rewrite/mut_excl_head.
    set FC1:= rename _ _ _.
    set FC2:= rename _ _ _.
    move=> H/=.
    have := (H_callable H).
    (* have /esym := H_callable H. *)
    rewrite (callabe_some_deref _ DF) {1}/FC1{1}/FC2 => /(_ _ erefl)/callable_rename.
    move=> /[dup] DF1/callable_rename ->.
    rewrite in_fnd (is_det_lookup _ DF)//=.
    move: H; rewrite{2}/FC2 get_modes_rev_rename (get_modes_rev_deref _ _ DF) => H.
    have:= get_modes_rev_H s.[pP] H (callabe_some_deref _ DF).
    rewrite (get_modes_rev_deref _ _ DF){1}/FC1 get_modes_rev_rename.
    move: H => +<-; move: (get_modes_rev _ _) => m H.
    have := H_suff_mode H.
    rewrite !has_cut_seq_fresh.
    case CS: has_cut_seq; first by case: select => [?[|[]]].
    case SH: select_head => //SM.
    have Hx := vars_deref D1 D2.
    (* rewrite (select_head_nil _ _ _ _ _ H SH)//=;
    by rewrite/FRS1;apply/fsubset_trans/fresh_rules_sub. *)
  Admitted.


  Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

  Definition all_cut p :=  all_rs_cut (rules p).

  Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
  Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

  Lemma all_cut_select_head c m rs fv:
    all_rs_cut rs ->
    all_rs_cut (select_head c m (fresh_rules fv rs).2).
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
    case: ifP => // ds; case S: select_head => //=[r' rs'].
    rewrite has_cut_seq_fresh HBO/=.
    set X := rename (fresh_rules fset0 rs).1 hd empty.
    have:= all_cut_select_head X.2 (get_modes_rev X.2 s.[kp]) fset0 H.
    by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
  Qed.
End mut_excl.



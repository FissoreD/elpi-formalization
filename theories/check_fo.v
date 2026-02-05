From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl.

Section checker.

  Definition check_atom sP (a: A) :=
    match a with
    | cut => true
    | call t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)
  Fixpoint check_atoms (sP :sigT) (s: seq A) :=
    match s with
    | [::] => true
    | cut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | call c :: xs => (tm_is_det sP c || has_cut_seq xs) && check_atoms sP xs
    end.

  Definition check_rule sP head prems :=
    (tm_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules sP rules :=
    all (fun x => check_rule sP x.(head) x.(premises)) rules.
End checker.

Lemma callable_is_det_fresh sP fv hd:
  tm_is_det sP (fresh_callable fv hd).2 =
    tm_is_det sP hd.
Proof.
  rewrite/tm_is_det.
  elim: hd fv => //= a Ha t fv.
  by rewrite !push/= -(Ha fv).
Qed.

Lemma tm_is_det_comb sP f a:
  tm_is_det sP (Callable_App f a) = tm_is_det sP f.
Proof. by rewrite/tm_is_det/=. Qed.

Lemma tm_is_det_fresh sP c c' sv sv':
  tm_is_det sP c ->
  fresh_callable sv c = (sv', c') ->
  tm_is_det sP c'.
Proof.
  elim: c c' sv sv' => //=.
    by move=> k c' sv sv' + [_ <-]//.
  move=> f Hf a c' sv sv'.
  case X: fresh_callable => [sv2 f'].
  case Y: rename => [sv3 a'] + [_ <-].
  rewrite !tm_is_det_comb => H.
  by apply/Hf/X.
Qed.

Lemma fresh_has_cut sv xs sv' xs':
  has_cut_seq xs -> fresh_atoms sv xs = (sv', xs') -> has_cut_seq xs'.
Proof.
  elim: xs sv xs' sv' => //= x xs IH sv xs' sv'.
  case Fs: fresh_atoms => [b' a'].
  case Fa: fresh_atom => [b2 a2]/=+[_<-]/=.
  move=> /orP [/eqP?|]; subst; first by move: Fa => /=[_<-].
  by move=> H; rewrite (IH _ _ _ H Fs) orbT.
Qed.

Lemma check_atom_fresh sP x x' sv sv':
  check_atom sP x ->
  fresh_atom sv x = (sv', x') ->
  check_atom sP x'.
Proof.
  destruct x => //=; first by move=> _ [_ <-].
  case X: fresh_callable => [svE c'] H [_ <-]/=.
  by apply/tm_is_det_fresh/X.
Qed.

Lemma all_check_atom_fresh sP xs xs' sv sv':
  all (check_atom sP) xs ->
  fresh_atoms sv xs = (sv', xs') ->
  all (check_atom sP) xs'.
Proof.
  elim: xs xs' sv sv' => //=; first by move=> > _ [_ <-].
  move=> x xs IH xsE sv svE /andP[H1 H2].
  case Fs: fresh_atoms => [sv' xs'].
  case Fa: fresh_atom => [sv2 xs2] [_ <-]/=.
  rewrite (IH _ _ _ _ Fs)//andbT.
  by apply/check_atom_fresh/Fa.
Qed.

Lemma check_atoms_fresh sP sv bo sv' bo':
  check_atoms sP bo ->
    fresh_atoms sv bo = (sv', bo') ->
    check_atoms sP bo'.
Proof.
  elim: bo bo' sv sv' => //=.
    move=> > _ [_ <-]//.
  move=> //= x xs IH bo' sv sv'.
  case Fs: fresh_atoms => [b' xs'].
  case Fa: fresh_atom => [b2 a2] + [_ <-]/=.
  destruct x; move: Fa => /=.
    move=> [_<-].
    move=> /orP[] H; apply/orP.
      by rewrite (all_check_atom_fresh H Fs); left.
    by right; apply/IH/Fs.
  case X: fresh_callable => [b3 c'][_<-] /andP[+/IH-/(_ _ _ _ Fs)->].
  rewrite andbT.
  by move=> /orP[/tm_is_det_fresh -/(_ _ _ _ X)|/fresh_has_cut-/(_ _ _ _ Fs)]->//; rewrite orbT.
Qed.

Section check.
  Variable u : Unif.
  (* Variable p : program. *)


  Fixpoint has_cut A :=
    match A with
    | TA cut => true
    | TA (call _) => false
    | KO => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut_seq B0 && has_cut B)
    | Or _ _ _ => false
    end.


  Fixpoint det_tree_seq sP L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP x || has_cut_seq xs) && det_tree_seq sP xs
    end.


  Definition no_alt A := next_alt (success A) A == None.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is OK due to the cut in LHS of Or
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)
  
  *)
  Fixpoint det_tree (sP:sigT) A :=
    match A with
    | TA cut => true
    | TA (call a) => tm_is_det sP a
    | KO | OK => true
    | And A B0 B =>
        det_tree sP B && 
        if no_alt A
        then det_tree sP A || has_cut B
        else
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          (det_tree sP A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq sP B0 (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree sP B
    | Or (Some A) _ B =>
        det_tree sP A && 
        if has_cut A then det_tree sP B 
        else (B == KO) 
    end.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim_tree A => /=.
      (* by move=> /andP[/is_ko_cutl->].
      by move=> /is_ko_cutl. *)
    rewrite fun_if/=.
    case:ifP => // sA.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[->/HB->]; rewrite orbT//.
  Qed.

  Lemma has_cut_seq_has_cut_big_and l:
    has_cut (big_and l) = has_cut_seq l.
  Proof. by elim: l => //[[|c]] xs IH//=; rewrite IH Bool.andb_diag. Qed.

  (* Lemma cut_followed_by_det_has_cut {sP l}:
      check_atoms sP l -> has_cut_seq l.
  Proof. rewrite/check_atoms. elim: l => //= -[|c] l _ //=. Qed. *)

  Lemma det_tree_big_and sP L:
    det_tree sP (big_and L) = det_tree_seq sP L.
  Proof.
    elim: L => //=-[|c] L ->.
      by rewrite orTb andTb andbb.
    rewrite has_cut_seq_has_cut_big_and /= [RHS]andbC.
    by case: det_tree_seq => //=; case: has_cut_seq => //=; rewrite orbC //= andbC.
  Qed.

  Lemma cut_followed_by_det_nfa_and {sP bo} :
    check_atoms sP bo -> det_tree_seq sP bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      by elim: l {IH} => //= x xs IH /andP[->]/IH->.
    by move=> /andP[->]/=.
  Qed.

  Lemma no_alt_cutl A: success A -> no_alt (cutl A).
  Proof. by rewrite /no_alt success_cut => ->; rewrite next_alt_cutl. Qed.

  Lemma det_tree_cutl {sP A}: success A -> det_tree sP (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= => /andP[sA sB]/=.
    by rewrite sA HA// HB//no_alt_cutl//.
  Qed.

  Lemma check_rules_cons sP x xs : check_rules sP (x :: xs) = check_rule sP (head x) (premises x) && check_rules sP xs.
  by []. Qed.

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
  Qed.

  Lemma det_tree_fresh sP sv bo:
    det_tree_seq sP bo -> det_tree_seq sP (fresh_atoms sv bo).2.
  Proof.
    elim: bo sv => //= [x xs] IH sv /andP[H1 /IH -/(_ sv)].
    case Fs: fresh_atoms => [b' a'].
    case Fa: fresh_atom => [b2 a2]/=->; rewrite andbT {IH}.
    move/orP: H1 => [|] H.
      by rewrite (check_atom_fresh H Fa).
    by rewrite (fresh_has_cut H Fs) orbT.
  Qed.

  (* Lemma mut_exclP *)

  Lemma check_rulesP s rs c fv s1:
    check_rules s rs ->
    tm_is_det s c ->
    all (fun x => check_atoms s x.2) (bc u {| rules := rs; sig := s |} fv c s1).2.
  Proof.
    rewrite/bc.
    case DR: tm2RC => //=[[q p]].
    case: fndP => //= pP.
    rewrite push/=.
    case X: fresh_rules => [fv1 rs']/=.
    generalize (get_modes_rev q s.[pP]) => md.
    generalize fv1 => fv2.
    rewrite push/=.
    elim: rs md rs' s c s1 fv q p {pP} fv1 DR X => //=[|[hd bo] rs IH] md rs' s c s1 fv q p fv1 DR ++ TD.
      move=> [_ <-]//.
    case FS: fresh_rules => [fv3 rs3].
    case FR: fresh_rule => [fv4 r'][??]/=/andP[H1 H2]; subst.
    move=> /=.
    have {}IH := IH _ _ _ _ _ _ _ _ _ DR FS H2 TD.
    case H: H => //=; last by apply: IH.
    rewrite !push/=.
    have TD' := tiki_taka DR TD H.
    move: FR.
    rewrite/fresh_rule !push/=.
    case X: fresh_atoms => [fs2 f']/= => -[??]; subst => /=.
    rewrite /= callable_is_det_fresh in TD'.
    move: H1; rewrite/check_rule TD'/= => ?.
    rewrite (check_atoms_fresh _ X)//=.
    apply: IH.
  Qed.

  Lemma deref_empty t:
    deref empty t = t.
  Proof. by elim: t => //= [v|f -> a ->//]; case: fndP => //=. Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim_tree A => //=.
    rewrite success_and.
    by move=> /orP[/HA->|/andP[+ /HB->]]//; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof. by apply/contraTF => /has_cut_success->. Qed.

  Lemma step_has_cut_help p sv A s: 
    has_cut A -> has_cut (step u p sv s A).2 \/ is_cb (step u p sv s A).1.2.
  Proof.
    elim: A s sv; try by move=> /=; auto.
    - by move=> []//=; auto.
    - move=> A HA B0 B HB s sv /=.
      rewrite !push/= => /orP[].
        move=> cA; rewrite has_cut_success//=.
        by have [->|] := HA s sv cA; auto.
      case/andP=> cB0 cB.
      move: (HB (get_subst s A) sv cB).
      case: ifP => sA/=; rewrite cB0/=.
        by move=> [->|->]; rewrite ?orbT; auto.
      by rewrite cB; rewrite orbT; auto.
  Qed.

  Lemma step_keep_cut p A s sv: 
    has_cut A -> is_cb (step u p sv s A).1.2 = false -> 
      has_cut (step u p sv s A).2.
  Proof. move/step_has_cut_help => /(_ p sv s)[]//->//. Qed.

  Lemma succ_failF_no_alt A: success A = false -> failed A = false -> no_alt A = false.
  Proof. by rewrite/no_alt => -> /failedF_next_alt ->//. Qed.


  Goal forall sP s, det_tree sP (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma step_next_alt {sP A} : 
    det_tree sP A -> success A ->
      next_alt true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[? _].
      by rewrite HA.
  Qed.

  Lemma build_na_is_dead {sP A}:
    det_tree sP A -> success A ->
      next_alt true A = None.
  Proof. move=> H2 H3; rewrite (step_next_alt H2)//=. Qed.

  Lemma has_cut_next_alt {A R b}: 
    has_cut A -> next_alt b A = Some R -> has_cut R.
  Proof.
    elim_tree A R b => /=.
    - case: t => //= _ [<-]//.
    - move=> /orP[].
        move=> cA.
        case: ifP => sA.
          case X: next_alt => // [A'|].
            by move=> [<-]/=; rewrite cA.
          by case nA: next_alt => //=[A'][<-]/=; rewrite (HA _ _ _ nA).
        case: ifP => //= fA.
          by case nA: next_alt => //[A'][<-]/=; rewrite (HA _ _ _ nA).
        by move=> [<-]/=; rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= sA.
        case X: next_alt => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: next_alt => //[A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and  cB0 orbT.
      case: ifP=> fA.
        case X: next_alt => //= [A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and cB0 orbT.
      by move=> [<-]/=; rewrite cB0 cB orbT.
  Qed.

  Lemma next_alt_no_alt b A A' : next_alt b A  = Some A' -> success A = b -> no_alt A = false.
  Proof. by rewrite /no_alt=> + -> => ->. Qed.

  Lemma no_free_alt_next_alt {sP A R b}:
    det_tree sP A -> next_alt b A = Some R -> det_tree sP R.
  Proof.
    elim_tree A R b => /=.
    - by case: b => // _ [<-].
    - by move=> _ [<-]//.
    - move=>/andP[fA].
      case nA: next_alt => [A'|].
        move=> + [<-]/=;rewrite (HA _ _ _ nA)//=.
        case: ifP => //= cA.
          rewrite (has_cut_next_alt _ nA)//.
        by move=> /eqP?; subst; rewrite if_same.
      case nB: next_alt => //=[B']+[<-]/=.
      case: ifP => [|_ /eqP] => ?; subst => // H.
      by rewrite (HB _ _ _ nB).
    - by case nB: next_alt => //=[B']H[<-]/=; apply: (HB B' b).
    - move=> /andP[dB +].
      case sA: (success A).
        case nB: next_alt => [B'|] => [+ [<-/=]|].
          rewrite (HB B' b)//=.
          case cB: (has_cut B); first by rewrite (has_cut_next_alt cB nB).
          case cB': (has_cut B'); rewrite /= orbC //= ?orbT.
          by rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[-> //].
        case nA: next_alt => [A'|] //= + [<-/=].
        rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (next_alt_no_alt nA)//.
        rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
        by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
      case fA : (failed A) => [|] => [|+ [<-/=]]; last by rewrite dB.
      case nA: next_alt => [A'|] => [+ [<-/=]|//].
      rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (next_alt_no_alt nA)//.
      rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
      by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
  Qed.

  Definition check_program_aux sig pr := 
    mut_excl u sig pr && check_rules sig pr.

  Definition check_program pr := 
    check_program_aux pr.(sig) pr.(rules).
  
  Lemma is_det_big_or pr c fv fv' s0 r0 rs s1:
    vars_tm (Callable2Tm c) `<=` fv ->
    vars_sigma s1 `<=` fv ->
    check_program pr -> tm_is_det (sig pr) c -> 
    bc u pr fv c s1 = (fv', (s0, r0) :: rs) ->
    det_tree (sig pr) (big_or r0 rs).
  Proof.
    rewrite /bc/check_program/check_program_aux.
    case: pr => rules s/= => ++/andP[].
    case X: tm2RC => //=[[q qp]].
    case: fndP => //= kP.
    move=> ++++ H.
    have [q'[qp' [H1 [H2 H3]]]] := tm_is_det_tm2RC s1 H.
    move=> D1 D2 ME CR.
    have := mut_exclP D1 D2 ME H.
    have := check_rulesP fv s1 CR H.
    rewrite/bc X/= in_fnd.
    case: fresh_rules => [a rs'].
    case: select => /= fv2 rs'' ++ [??]; subst => /=/andP[].
    clear.
    elim: rs s r0 => //= [|[s0 r0] rs IH] sp r1 H1; 
    rewrite /=det_tree_big_and//cut_followed_by_det_nfa_and//.
    move=> /andP[Cr0 HL] /andP[cb].
    rewrite has_cut_seq_has_cut_big_and cb.
    by move=> /IH-/(_ sp)//=; auto.
  Qed.

  Lemma step_no_free_alt pr sv s1 A r: 
    vars_tree A `<=` sv ->
    vars_sigma s1 `<=` sv ->
    check_program pr -> det_tree pr.(sig) A -> 
      step u pr sv s1 A = r ->
        det_tree pr.(sig) r.2.
  Proof.
    move=> ++ H + <-; clear r.
    elim_tree A s1.
    - case: t => [|c]//=; rewrite !push/=.
      case bc: bc => //=[fv'[|[s0 r0]rs]]//= V1 V2 H1.
      by apply: is_det_big_or bc.
    - rewrite/=2!fsubUset -andbA => /and3P[S1 S2 S3] S4 /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - rewrite /=fsubUset => /andP[S1 S2] S3.
      by rewrite /=!push; move=> /HB/=->.
    - rewrite step_and/= 2!fsubUset -andbA => /and3P[S1 S2 S3] S4 /andP[dB].
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      have S5 : vars_sigma (get_subst s1 A) `<=` sv by apply: vars_sigma_get_subst.
      rewrite (fun_if (det_tree (sig pr))).
      case SA: success.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb; first by case/orP=> [->//|/step_keep_cut->]; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /no_alt /sA failed_step//= SA.
      rewrite (succ_failF_no_alt SA fA) => /andP[+ ->]/=.
      by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
  Qed.

  Definition is_det u p s fv A := forall b s' B fv',
    run u p fv s A s' B b fv' -> B = None.

  Lemma run_next_alt s fv p A: 
    vars_tree A `<=` fv ->
    vars_sigma s `<=` fv ->
    check_program p -> 
      det_tree p.(sig) A -> is_det u p s fv A.
  Proof.
    rewrite/is_det.
    move=> D1 D2 H1 H2 b s' B ? H3.
    elim_run H3 H1 H2 D1 D2.
    - apply: build_na_is_dead H2 SA.
    - have [H3 H4] := vars_tree_step_sub_flow D1 D2 eA.
      apply: (IH H1 _ H3 H4).
      by apply: step_no_free_alt eA.
    - have D3:= vars_tree_next_alt_sub_flow D1 nA.
      apply: IH => //.
      by apply/no_free_alt_next_alt/nA.
  Qed.

  Lemma main s fv p t:
    vars_tm (Callable2Tm t) `<=` fv ->
    vars_sigma s `<=` fv ->
    check_program p -> tm_is_det p.(sig)  t -> 
      is_det u p s fv (TA (call t)).
  Proof.
    move=> H1 fA HA H2.
    apply: run_next_alt => //=.
  Qed.

  Print Assumptions  main.
  
  (* Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == cut end.
    
    Definition AllTailCut p := (all tail_cut (rules p)).

    Lemma cut_in_prem_tail_cut : AllTailCut p -> check_program u p.
    Proof.
      case: p; rewrite/AllTailCut/check_program/=.
      move=> rules sig H; apply/andP; split.
        elim: rules sig H => //= x xs IH sig /andP[H1 H2].
        rewrite IH//andbT.
        rewrite/mut_excl_head/=.
        case: tm2RC => [[c p']|]//; case: fndP => //= kP.
        case: ifP => //= HD.
        case: x H1 => /= hd pm; clear -H2.
        rewrite/tail_cut/=.
        elim: pm hd xs H2 => //= x xs IH.
        generalize sig.[kP].
        move : (sig.[kP]) => /=.
      move=> H; apply/andP; split. move: H; case: p.
      rewrite /AllTailCut /check_program.
      rewrite /tail_cut /check_rules.
      remember (rules p) as RS.

      apply: sub_all => r; clear.
      rewrite /check_rule.
      case X: callable_is_det => //=.
      case: r X => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sP t:
      AllTailCut p -> tm_is_det sP t -> is_det (TA (call t)).
    Proof.
      move=> /(cut_in_prem_tail_cut sP).
      apply main.
    Qed.
  End tail_cut. *)

  (* Print Assumptions tail_cut_is_det. *)

End check.
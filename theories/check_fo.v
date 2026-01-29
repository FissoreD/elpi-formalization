From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.

Section checker.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint getS_Callable (sP: sigT) (t: Callable) : option S :=
    match t with
    | Callable_P pn => sP.[? pn]
    | Callable_App hd _ => getS_Callable sP hd
    end.

  Fixpoint callable_is_det (sP: sigT) (t:Callable) : bool :=
    match t with
    | Callable_App h _ => callable_is_det sP h
    | Callable_P k => 
      if sP.[?k] is Some s then is_det_sig s
      else false
    end.

  Definition tm_is_det (sP: sigT) (t : Callable) :=
    odflt false (omap is_det_sig (getS_Callable sP t)).

  Definition check_atom sP (a: A) :=
    match a with
    | cut => true
    | call t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)
  Fixpoint check_atoms (sP :sigT) (s: seq A) :=
    match s with
    | [::] => false
    | cut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | call _ :: xs => check_atoms sP xs
    end.

  Definition check_rule sP head prems :=
    (callable_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules sP rules :=
    all (fun x => check_rule sP x.(head) x.(premises)) rules.

  Definition check_program sP pr := 
    check_rules sP (rules pr).
End checker.

Definition has_cut_seq:= (has (fun x => cut == x)).

Section check.

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
        [&& (((next_alt (success A) A == None) || (has_cut_seq B0)) && has_cut B) || det_tree sP A, 
          det_tree sP B & ((next_alt (success A) A == None) || det_tree_seq sP B0)]
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

  Lemma cut_followed_by_det_has_cut {sP l}:
      check_atoms sP l -> has_cut_seq l.
  Proof. rewrite/check_atoms. elim: l => //= -[|c] l _ //=. Qed.

  Lemma det_tree_big_and sP L:
    det_tree sP (big_and L) = det_tree_seq sP L.
  Proof.
    elim: L => //= [[|c]]//= L IH; rewrite IH Bool.andb_diag.
      by rewrite orbT.
    case: tm_is_det; case: det_tree_seq; rewrite?(andbF, andbT, orbT, orbF)//=.
    by rewrite has_cut_seq_has_cut_big_and Bool.andb_diag.
  Qed.

  Lemma cut_followed_by_det_nfa_and {sP bo} :
    check_atoms sP bo -> det_tree_seq sP bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      by elim: l {IH} => //= x xs IH /andP[->]/IH->.
    by move=> /[dup] /cut_followed_by_det_has_cut -> /IH-> /[!orbT].
  Qed.

  Lemma no_free_alt_cutl {sP A}: success A -> det_tree sP (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= success_cut => /andP[/[dup]/HA->->/HB->].
    by rewrite orbT next_alt_cutl.
  Qed.

  Variable u : Unif.
  Variable p : program.

  Lemma tiki_taka {sP s s3 modes t q pn hd1}:
    let t' := tm2RC (deref s (Callable2Tm t)) in
    t' = Some (q, pn) ->
    tm_is_det sP t ->
      H u modes q hd1 s = Some s3 ->
        callable_is_det sP hd1.
  Proof.
    move=>/=.
    elim: modes q pn hd1 t s s3 => //=.
      move=> []//=k kp hd1 t s1 s2.
      case: hd1 => //={}k0.
      case: eqP => //=?; subst k0.
      move=> ++ [?]; subst.
      destruct t => //=; last by case: tm2RC => //=[[]].
      by move=> [->->]/=; rewrite/tm_is_det/=; case: fndP.
    move=> m //ml IH q pn hd t s1 s2 H1 H2 H3.
    have {H3}: exists f1 a1 f2 a2,
      q = Callable_App f1 a1 /\
      hd = Callable_App f2 a2 /\
      (obind (matching u a1 a2) (H u ml f1 f2 s1) = Some s2 \/
      obind (unify u a1 a2) (H u ml f1 f2 s1) = Some s2).
    by move: H3; destruct m, q, hd => //; repeat eexists; auto.
    move=> [f1 [a1 [f2 [a2 [?[?]]]]]]; subst.
    case e: H => //=[s3|]; last by case.
    move: H2; rewrite/tm_is_det/=.
    case: t H1 => //= c t.
    case H : tm2RC => //=[[h1' hp]] [??]?; subst => /=.
    case X: getS_Callable => //[S] H1/= H2.
    by apply: IH H _ e; rewrite/tm_is_det X//.
  Qed.

  Lemma check_rules_cons sP x xs : check_rules sP (x :: xs) = check_rule sP (head x) (premises x) && check_rules sP xs.
  by []. Qed.

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
Qed.

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

  Lemma callable_is_det_fresh sP fv hd:
    callable_is_det sP (fresh_callable fv hd).2 =
      callable_is_det sP hd.
  Proof.
    elim: hd fv => //= a Ha t fv.
    case F: fresh_callable => [fv' a']/=.
    case F': fresh_tm => [fv'' a'']/=.
    by rewrite -(Ha fv) F.
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
    case Y: fresh_tm => [sv3 a'] + [_ <-].
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
    elim: bo bo' sv sv' => //= x xs IH bo' sv sv'.
    case Fs: fresh_atoms => [b' a'].
    case Fa: fresh_atom => [b2 a2] + [_ <-]/=.
    destruct x; move: Fa => /=.
      move=> [_<-].
      move=> /orP[] H; apply/orP.
        by rewrite (all_check_atom_fresh H Fs); left.
      by right; apply/IH/Fs.
    case X: fresh_callable => [b3 c'][_<-] H.
    by apply/IH/Fs.
  Qed.


  Lemma select_same2 vx vy q m rs s:
    (select u vx q m rs s).2 = (select u vy q m rs s).2.
  Proof.
    elim: rs vx vy q m s => //= r rs IH vx vy q m s.
    case: H => //=?; rewrite !push//=; f_equal; auto.
  Qed.

  Lemma is_det_no_free_alt {sP t s1 fv}:
    check_rules sP p.(rules) -> tm_is_det sP t -> 
      det_tree sP (backchain u p fv s1 t).2.
  Proof.
    rewrite /backchain/bc.
    case X: tm2RC => //=[[q qp]].
    case: p => rules sig1 /=.
    case: fndP => //= kP.
    generalize (get_modes_rev q sig1.[kP]).
    clear kP sig1 p => l.
    rewrite !push/=.
    generalize (fresh_rules fv rules).1.
    elim: rules s1 t q qp X fv l => //.
    move=> [] hd bo rules IH s t q qp X fv l/=f /andP[ck1 ck2] dett.
    have {}IH := IH _ _ _ _ X _ _ _ ck2 dett.
    rewrite !push/=.
    case H: H => /= [s2|]; last first.
      by rewrite (select_same2 _ ((fresh_rules fv rules).1)).
    have Hx := tiki_taka X dett H.
    rewrite head_fresh_rule/=callable_is_det_fresh in Hx.
    move/orP: ck1 => []; first by rewrite Hx.
    rewrite !push/=.
    have {IH}:= IH fv l f.
    rewrite head_fresh_premises/=.
    case S: select => [fv' [|[r0 s0] rs]]/=; rewrite det_tree_big_and.
      move => _ /cut_followed_by_det_nfa_and.
      by move=> /det_tree_fresh->.
    move=> Ha Hb.
    have ? : check_atoms sP (fresh_atoms (fresh_callable (fresh_rules fv rules).1 hd).1 bo).2.
      case W: fresh_atoms.
      by apply/check_atoms_fresh/W.
    rewrite cut_followed_by_det_nfa_and//.
    rewrite has_cut_seq_has_cut_big_and//.
    rewrite (@cut_followed_by_det_has_cut sP)//=.
  Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim_tree A => //=.
    rewrite success_and.
      (* by move=> /andP[/is_ko_success].
      by move=> /is_ko_success. *)
    by move=> /orP[/HA->|/andP[+ /HB->]]//; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof. by apply/contraTF => /has_cut_success->. Qed.

  Lemma step_has_cut_help sv A s: 
    has_cut A -> has_cut (step u p sv s A).2 \/ is_cb (step u p sv s A).1.2.
  Proof.
    elim: A s sv; try by move=> /=; auto.
    - by move=> []//=; auto.
    (* - move=> A HA s1 B HB s sv /=/andP[kA kB].
      by rewrite !push is_ko_step //=kA; left.
    - by move=> s1 B HB s sv /= kB; rewrite !push is_ko_step//=; auto. *)
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

  Lemma step_keep_cut A s sv: 
    has_cut A -> is_cb (step u p sv s A).1.2 = false -> 
      has_cut (step u p sv s A).2.
  Proof. move/step_has_cut_help => /(_ sv s)[]//->//. Qed.

  Lemma step_no_free_alt {sP sv s1 A r} : 
    check_program sP p -> det_tree sP A -> 
      step u p sv s1 A = r ->
        det_tree sP r.2.
  Proof.
    move=> H + <-; clear r.
    elim_tree A s1 => /=.
    - by case: t => [|c]//=; rewrite push => /is_det_no_free_alt->//.
    - move=> /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> Hy Hz; rewrite step_keep_cut in Hz.
    - by rewrite !push; move=> /HB/=->.
    - rewrite !push.
      case: ifP => sA/=/and3P[H1 H2 H3].
        rewrite [success _]fun_if success_cut if_same sA HB//.
        case: ifP => CB.
          by rewrite next_alt_cutl eqxx/= no_free_alt_cutl// orbT.
        rewrite H3.
        move/orP: H1 => [|->]; last by rewrite orbT//.
        move=> /andP[-> /step_keep_cut->]//.
      case fA: (failed A).
        by rewrite failed_step//=sA H3 H1 H2.
      move: H1 H3; rewrite (next_alt_not_failed fA)//=.
      move=> + ->; rewrite H2 !orbT !andbT.
      move=> /orP[|/HA->]; last by rewrite !orbT.
      by move=> /andP[->->]; rewrite !orbT.
  Qed.

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
    - move=> A HA l B HB /[!success_and].
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0]/andP[sA sB].
        rewrite success_has_cut// in cB.
      rewrite success_failed//sA.
      rewrite HB//HA//.
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
    (* - by move=>/andP[kA kB]; rewrite !is_ko_next_alt//. *)
    (* - by move=>/is_ko_next_alt->. *)
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
    - move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case sA: success; rewrite sA in cB0, fB0.
          have:= HB _ b fB.
          case X: next_alt => // [B'|].
            by move=> /(_ _ erefl) fD [<-]/=; rewrite sA cB0 fB0 (HB _ _ fB X) (has_cut_next_alt _ X)//= orbT.
          move=> _; case Y: next_alt => //[A'][<-]/=.
          rewrite Y/= in cB0, fB0.
          by rewrite has_cut_seq_has_cut_big_and det_tree_big_and fB0 cB0 !orbT.
        case: ifP => fA; last first.
          rewrite next_alt_not_failed//= in cB0, fB0.
          by move=> [<-]/=; rewrite cB0/= cB/= fB fB0 !orbT.
        case nA: next_alt => //=[A'][<-]/=.
        rewrite nA/= in cB0, fB0.
        by rewrite cB0 fB0 has_cut_seq_has_cut_big_and det_tree_big_and fB0 cB0 !orbT.
      case sA: success; rewrite sA in fB0.
        case nB: next_alt => [B'|].
          by move=> [<-]/=; rewrite (HB _ _ _ nB)//= fA sA/= fB0 !orbT.
        case nA: next_alt => [A'|]//=[<-]/=.
        rewrite nA/= in fB0.
        by rewrite (HA _ _ _ nA)// det_tree_big_and fB0 !orbT.
      case: ifP => FA; last first.
        rewrite next_alt_not_failed//= in fB0.
        by move=>[<-]/=; rewrite fA fB fB0 !orbT.
      case X: next_alt => // [A'][<-]/=.
      rewrite X/= in fB0.
      by rewrite det_tree_big_and fB0 (HA _ false)//= !orbT.
  Qed.

  Lemma step_next_alt_failed {sP sv sv' A B C s b}:
    check_program sP p ->
      det_tree sP A -> step u p sv s A = (sv', Failed, B) ->
        next_alt b B = Some (C) -> det_tree sP C.
  Proof.
    move=> H1 H2 H3 H4.
    have /= H5 := step_no_free_alt H1 H2 H3.
    by have:= no_free_alt_next_alt H5 H4.
  Qed.

  Definition is_det A := forall b s sv s' B fv',
    run u p sv s A s' B b fv' -> B = None.

  Lemma run_next_alt {sP A}: 
    check_program sP p -> 
      det_tree sP A -> is_det A.
  Proof.
    rewrite/is_det.
    move=> H1 H2 b s sv s' B ? H3.
    elim: H3 H2; clear -H1 => //.
    - move=> s1 s2 A B _ sA _ <- fA.
      have:= build_na_is_dead fA sA.
      case: next_alt => //=.
    - move=> s1 s2 r A B n sv sv' ? eA rB IH fA.
      by apply/IH/(step_no_free_alt H1 fA eA).
    - move=> s1 s2 r A B n sv sv' ? eA rB IH fA.
      by apply/IH/(step_no_free_alt H1 fA eA).
    - move=> s1 s2 A B r n sv ? fA nA H IH FA.
      by apply/IH/no_free_alt_next_alt/nA.
  Qed.

  Lemma main {sP t}:
    check_program sP p -> tm_is_det sP t -> 
      is_det (TA (call t)).
  Proof.
    move=> H1 fA HA.
    apply: run_next_alt H1 _ HA.
    apply: fA.
  Qed.

  Print Assumptions  main.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == cut end.
    
    Definition AllTailCut p := (all tail_cut (rules p)).

    Lemma cut_in_prem_tail_cut sP: AllTailCut p -> check_program sP p.
    Proof.
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
  End tail_cut.

  Print Assumptions tail_cut_is_det.

End check.
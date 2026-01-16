From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.
From det Require Import finmap ctx lang.

(* Lemma tm2RC_kp {t1 k} : 
  tm2RC t1 = Some (RCallable_Kp k) -> t1 = Tm_Kp k.
Proof.
  case: t1 k => //=.
  - move=> k1 k2 []; congruence.
  - move=> h b k; case X: tm2RC => //.
Qed. *)

(* Lemma deref_kp {s1 t k}:
  tm2RC (deref s1 t) = Some (RCallable_Kp k) ->
    (t = Tm_Kp k) \/ (exists v, t = Tm_V v /\ sigma s1 v = Some (Tm_Kp k)).
Proof.
  case: t k => //=.
  - move=> k1 k2 []; left; congruence.
  - move=> v k; case x: sigma => [t1|]//=.
    move=>/tm2RC_kp?; subst.
    right; by eexists.
  - move=> h b k; case X: tm2RC => //.
Qed. *)

Section checker.
  (* Definition sigV := V -> option S. *)

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint getS_Callable (sP: sigT) (t: Callable) : option S :=
    match t with
    | Callable_Kp pn => sP.[? pn]
    | Callable_V vn => None
    | Callable_Comb hd _ => getS_Callable sP hd
    end.

  Fixpoint rcallable_is_det (sP: sigT) (t:RCallable) : bool :=
    match t with
    | RCallable_Comb h _ => rcallable_is_det sP h
    | RCallable_Kp k => 
      if sP.[?k] is Some s then is_det_sig s
      else false
    end.

  Definition tm_is_det (sP: sigT) (t : Callable) :=
    odflt false (omap is_det_sig (getS_Callable sP t)).

  Definition check_atom sP (a: A) :=
    match a with
    | ACut => true
    | ACall t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)

  Fixpoint check_atoms (sP :sigT) (s: seq A) :=
    match s with
    | [::] => false
    | ACut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | ACall _ :: xs => check_atoms sP xs
    end.


  Definition check_rule sP head prems :=
    (rcallable_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules sP rules :=
    all (fun x => check_rule sP x.(head) x.(premises)) rules.

  Definition check_program sP := 
    forall pr, check_rules sP (rules pr).
End checker.

Definition has_cut_seq:= (has (fun x => ACut == x)).

Section check.

  Fixpoint has_cut A :=
    match A with
    | CutS => true
    | CallS _ _ => false
    | Bot | Dead => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut_seq B0.2 && has_cut B)
    | Or _ _ _ => is_ko A
    end.


  Lemma has_cut_cut {B}: has_cut (cutr B).
  Proof. 
    elim: B => //=.
    - move=> ?????; rewrite !is_ko_cutr//.
    - by move=> A ->.
  Qed.

  Lemma has_cut_dead {A}: is_dead A -> has_cut A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB/andP[/is_dead_is_ko->/is_dead_is_ko->]//.
    - move=> A HA B0 B HB dA; rewrite HA//.
  Qed.

  Fixpoint det_tree_seq sP L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP x || has_cut_seq xs) && det_tree_seq sP xs
    end.

  (* a tree is deterministic if it call deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is OK due to the cut in LHS of Or
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)
  
  *)
  Fixpoint det_tree (sP:sigT) A :=
    match A with
    | CutS => true
    | CallS _ a => tm_is_det sP a
    | Bot | OK => true
    | Dead => true
    | And A B0 B =>
      (is_ko A) || 
        [&& (((next_alt (success A) A == None) || (has_cut_seq B0.2)) && has_cut B) || det_tree sP A, 
          det_tree sP B & ((next_alt (success A) A == None) || det_tree_seq sP B0.2)]
    | Or A _ B =>
        det_tree sP A && 
          if has_cut A then det_tree sP B else (B == cutr B)
    end.

  Lemma no_alt_cut {sP A}: det_tree sP (cutr A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB cutr2 eqxx if_same.
    + move=> A HA B0 B HB /=; rewrite is_ko_cutr//.
  Qed.

  Lemma no_alt_dead {sP A}: is_dead A -> det_tree sP A.
  Proof.
    elim: A => //.
    + move=> A HA s B HB /=/andP[dA]; rewrite HA// has_cut_dead//.
    + move=> A HA B0 B HB /=dA; rewrite is_dead_is_ko//.
  Qed.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[kA kB]; rewrite fun_if/= is_ko_cutr kA !is_ko_cutl// if_same//.
    move=> A HA B0 B HB /=; rewrite fun_if/=.
    rewrite !has_cut_cut/=.
    case:ifP => // sA.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[->/HB->]; rewrite orbT//.
  Qed.

  Lemma has_cut_seq_has_cut_big_and p l:
    has_cut (big_and p l) = has_cut_seq l.
  Proof. by elim: l => //[[|c]] xs IH//=; rewrite IH Bool.andb_diag. Qed.

  Lemma cut_followed_by_det_has_cut {sP l}:
      check_atoms sP l -> has_cut_seq l.
  Proof. rewrite/check_atoms. elim: l => //= -[|c] l _ //=. Qed.

  Lemma det_tree_det_tree_seq sP p L:
    det_tree sP (big_and p L) = det_tree_seq sP L.
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
    elim: A => //=.
      move=> A HA s B HB/=.
      case: ifP => dA/= succ; rewrite !(HA,HB,cutr2,eqxx,no_alt_cut,if_same)//=.
      rewrite no_alt_dead//has_cut_dead//.
    move=> A HA B0 B HB /=/andP[sA sB].
    rewrite sA/= HB//HA//= !orbT/= .
    by rewrite success_cut sA next_alt_cutl orbT.
  Qed.

  Variable u : Unif.

  Lemma tiki_taka {sP s s3 modes t q pn hd1}:
    let t' := tm2RC (deref s (Callable2Tm t)) in
    t' = Some (q, pn) ->
    tm_is_det sP t ->
      H u modes q hd1 s = Some s3 ->
        rcallable_is_det sP hd1.
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
      q = RCallable_Comb f1 a1 /\
      hd = RCallable_Comb f2 a2 /\
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

  Axiom fresh_rule_id: forall V R, fresh_rule V R = R.
  Lemma fresh_rules_help_id V R: (fresh_rules_help V R) = R.
  Proof. 
    elim: R V => //= x xs IH V; rewrite fresh_rule_id/= IH//.
  Qed.

  Lemma fresh_rules_id V R: (fresh_rules V R) = R.
  Proof. apply: fresh_rules_help_id. Qed.

  Lemma is_det_no_free_alt {sP t s1} {p:program}:
    check_rules sP p.(rules) -> tm_is_det sP t -> 
      det_tree sP (big_or u p s1 t).
  Proof.
    rewrite /big_or/F.
    case X: tm2RC => //=[[q qp]].
    case: p => rules sig1 /=.
    generalize {| rules := rules; sig := sig1 |} as pr => pr.
    case: fndP => //=.
    elim: rules s1 t pr q qp X => //=.
    move=> [] hd bo rules IH s/= t p q qp X qpP /andP[H1 H1'] H2.
    case H: H => /= [s2|]; last first.
      rewrite fresh_rules_help_id.
      have:= IH _ _ _ _ _ X qpP H1' H2.
      by rewrite fresh_rules_id.
    clear IH.
    move: H.
    rewrite fresh_rule_id fresh_rules_help_id.
    move: H1 => /orP[]; last first.
      move=> + _.
      elim: rules H1' bo => //=.
        move=> _ bo.
        rewrite det_tree_det_tree_seq.
        apply cut_followed_by_det_nfa_and.
      move=> [] hd1 bo1/= l IH /andP [H3 H4] bo H1.
      case H: H => [s3|]//=; last first.
        by apply: IH.
      rewrite det_tree_det_tree_seq.
      rewrite cut_followed_by_det_nfa_and//=.
      rewrite has_cut_seq_has_cut_big_and.
      rewrite (cut_followed_by_det_has_cut H1).
      rewrite IH//=.
      move: H3 => /orP[] => //.
      move=> /eqP H3; exfalso.
      have /= := tiki_taka X H2 H; congruence.
    move=> /eqP H3 H4.
    have /= := tiki_taka X H2 H4; congruence.
  Qed.

  Lemma expand_has_cut_help {A s}: 
    has_cut A -> has_cut (get_tree (step u s A)) \/ is_cutbrothers (step u s A).
  Proof.
    elim: A s; try by move=> /=; auto.
    - move=> A HA s1 B HB s /=/andP[kA kB].
      case: ifP => dA.
        by rewrite get_tree_Or/= kA (is_ko_step _ kB)/=; auto.
      by rewrite is_ko_step//= kA; auto.
    - move=> A HA B0 B HB s /=/orP[].
        move=> /(HA s); case: step => [|||] C/= []//; auto => cC.
        - by rewrite cC /=; left.
        - by rewrite cC /=; left.
        left; rewrite get_tree_And /=.
        by case: ifP; rewrite ?cC // has_cut_cutl.
      case/andP=> cB0 cB.
      case: step => [|||] C/=; rewrite ?cB ?cB0 ?orbT; auto.
      move: (HB (get_substS s C)).
      by case: step => [|||] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
  Qed.

  Lemma step_keep_cut {A s}: 
    has_cut A -> is_cutbrothers (step u s A) = false -> 
      has_cut (get_tree (step u s A)).
  Proof. move/expand_has_cut_help => /(_ s)[]//->//. Qed.

  Lemma expand_no_free_alt {sP s1 A r} : 
    check_program sP -> det_tree sP A -> 
      step u s1 A = r ->
        det_tree sP (get_tree r).
  Proof.
    move=> H + <-; clear r.
    elim: A s1 => //.
    - move=> p t s1 /=.
      apply: is_det_no_free_alt.
      by have:= H p.
    - move=> A HA s B HB s1 /=/andP[fA].
      case: ifP => //= cA.
        move=> nnB.
        case: ifP => //= dA.
          have:= HB s1 nnB.
          by case: step => //= [|||] C nnC/=; rewrite get_tree_Or/=fA/=cA?HB//.
        have:= HA s1 fA.
        have := @expand_has_cut_help _ s1 cA.
        case X: step => //= -[]// + ->; rewrite ?nnB ?no_alt_cut //=; try by case: has_cut.
        by rewrite cutr2 eqxx if_same.
      move/eqP->.
      case: ifP => [dA|].
        rewrite get_tree_Or/=cA no_alt_dead//=is_ko_step//=?is_ko_cutr//cutr2//.
      have:= HA s1 fA => + dA.
      case Y: step => /=->; rewrite !cutr2 eqxx no_alt_cut if_same//.
    - move=> A HA [p l] B HB s /=.
      move=>/orP[].
        move=>kA; rewrite is_ko_step//=kA//.
      rewrite step_and/=.
      case sA: success =>/and3P[H1 H2 H3]/=.
        have scA: success (cutl A) by rewrite success_cut.
        rewrite get_tree_And/=.
        rewrite ![success _]fun_if [is_ko _]fun_if.
        rewrite !success_is_ko//= sA scA !if_same/=.
        rewrite HB//=.
        case: ifP => CB.
          by rewrite next_alt_cutl eqxx/= no_free_alt_cutl// orbT/=.
        rewrite H3.
        move/orP: H1 => [|->]; last by rewrite orbT//.
        move=> /andP[-> /step_keep_cut->]//.
      case fA: (failed A).
        by rewrite failed_expand//=sA H3 H1 H2 orbT.
      move: H1 H3; rewrite (next_alt_not_failed fA)//=.
      move=> + H1; rewrite H1 H2 orbT !andbT/=.
      move=>/orP[|/HA->]; last by rewrite !orbT.
      by move=> /andP[->->]; rewrite !orbT.
  Qed.

  Goal forall sP s, det_tree sP (Or OK s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB /=/andP[kA kB].
      rewrite !is_ko_success// if_same//.
    - move=> A HA B0 B HB /=/orP[].
        by move=>/HA->.
      by move=>/andP[] _/HB->; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; case: ifP => dA.
        rewrite is_dead_is_ko//=; apply: success_is_ko.
      move=>/success_is_ko->//.
    - by move=> A HA B0 B HB/=/andP[]/HA->/HB->; rewrite andbF.
  Qed.

  Lemma expand_next_alt {sP A} : 
    check_program sP -> det_tree sP A -> success A ->
      next_alt true A = None.
  Proof.
    move=> H; elim: A => //=.
    - move=> A HA s B HB /andP[nA IH].
      case: ifP => [dA sB|dA sA].
        rewrite HB//.
        move: IH; case: ifP => //.
        move=> _ /eqP->; rewrite no_alt_cut//.
      rewrite HA//.
      move: IH; case: ifP.
        move=> /has_cut_success; congruence.
      move=> _ /eqP->; rewrite next_alt_cutr//.
    - move=> A HA [p l] B HB /orPT[].
        move=> /is_ko_success->//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0]/andP[sA sB].
        rewrite success_has_cut// in cB.
      rewrite success_failed//sA.
      rewrite HB//HA//.
  Qed.

  Lemma build_na_is_dead {sP A}:
    check_program sP -> det_tree sP A -> success A ->
      (build_na A (next_alt true A)) = dead A.
  Proof. move=> H1 H2 H3; by rewrite (expand_next_alt H1)//=. Qed.

  Lemma has_cut_next_alt {A B b}: 
    has_cut A -> next_alt b A = Some B -> has_cut B.
  Proof.
    elim: A B b => //.
    - move=>/=[]?//? _ [<-]//.
    - move=> A HA s1 B HB C b/=.
      move=>/andP[kA kB].
      by rewrite !is_ko_next_alt//; rewrite !if_same//.
    - move=> A HA [p l] B HB C b/=.
      move=> /orP[].
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

  Lemma no_free_alt_next_alt {sP A B b}:
    det_tree sP A -> next_alt b A = Some B -> det_tree sP B.
  Proof.
    elim: A B b => //=.
    - move=> /= B b _; case: ifP => // _[<-]//.
    - move=> p c B _ _ [<-]//.
    - move=> B _ _ [<-]//.
    - move=> A HA s B HB C /= b.
      move=>/andP[fA].
      case: (ifP (is_dead _)) => dA.
        rewrite has_cut_dead//.
        move=> fB.
        have:= HB _ b fB.
        case X: next_alt => //[D] /(_ _ erefl) fD[<-]/=.
        rewrite no_alt_dead//?is_dead_dead//has_cut_dead// is_dead_dead//.
      case: ifP => cA.
        move=> fB.
        have:= (HA _ b fA).
        case X: next_alt => //[D|].
          have cD:= has_cut_next_alt cA X.
          by move=> /(_ _ erefl) fD[<-]/=; rewrite fD cD fB.
        move=> _.
        have idA := @is_dead_dead A.
          case Y: next_alt => //[D].
          move=>[<-]/=.
          rewrite no_alt_dead// has_cut_dead//.
          apply: HB fB Y.
      move=>/eqP->; rewrite (is_ko_next_alt _ is_ko_cutr).
      have:= HA _ b fA.
      case: next_alt; rewrite ?if_same// => D /(_ _ erefl) fD [<-]/=.
      by rewrite fD cutr2 eqxx no_alt_cut if_same.
    - move=> A HA [p l] B HB C b /=.
      move=>/orP[].
        move=>kA.
        by rewrite is_ko_failed// is_ko_success// is_ko_next_alt//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case sA: success; rewrite sA in cB0, fB0.
          have:= HB _ b fB.
          case X: next_alt => // [B'|].
            by move=> /(_ _ erefl) fD [<-]/=; rewrite sA cB0 fB0 (HB _ _ fB X) (has_cut_next_alt _ X)//= orbT.
          move=> _; case Y: next_alt => //[A'][<-]/=.
          rewrite Y/= in cB0, fB0.
          by rewrite has_cut_seq_has_cut_big_and det_tree_det_tree_seq fB0 cB0 !orbT.
        case: ifP => fA; last first.
          rewrite next_alt_not_failed//= in cB0, fB0.
          by move=> [<-]/=; rewrite cB0/= cB/= fB fB0 !orbT.
        case nA: next_alt => //=[A'][<-]/=.
        rewrite nA/= in cB0, fB0.
        by rewrite cB0 fB0 has_cut_seq_has_cut_big_and det_tree_det_tree_seq fB0 cB0 !orbT.
      case sA: success; rewrite sA in fB0.
        case nB: next_alt => [B'|].
          by move=> [<-]/=; rewrite (HB _ _ _ nB)//= fA sA/= fB0 !orbT.
        case nA: next_alt => [A'|]//=[<-]/=.
        rewrite nA/= in fB0.
        by rewrite (HA _ _ _ nA)// det_tree_det_tree_seq fB0 !orbT.
      case: ifP => FA; last first.
        rewrite next_alt_not_failed//= in fB0.
        by move=>[<-]/=; rewrite fA fB fB0 !orbT.
      case X: next_alt => // [A'][<-]/=.
      rewrite X/= in fB0.
      by rewrite det_tree_det_tree_seq fB0 (HA _ false)//= !orbT.
  Qed.

  Lemma expand_next_alt_failed {sP A B C s b}:
    check_program sP ->
      det_tree sP A -> step u s A = Failure B ->
        next_alt b B = Some (C) -> det_tree sP C.
  Proof.
    move=> H1 H2 H3 H4.
    have /= H5 := expand_no_free_alt H1 H2 H3.
    by have:= no_free_alt_next_alt H5 H4.
  Qed.

  Lemma no_free_alt_dead {sP A}:
    is_dead A -> det_tree sP A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[dA dB]; by rewrite has_cut_dead//HA//HB.
    - by move=> A HA B0 B HB dA; rewrite is_dead_is_ko//.
  Qed.

  Definition is_det A := forall b s s' B,
    runb u s A s' B b -> is_dead B.

  Lemma runb_next_alt {sP A}: 
    check_program sP -> 
      det_tree sP A -> is_det A.
  Proof.
    rewrite/is_det.
    move=> H1 H2 b s s' B H3.
    elim: H3 H2; clear -H1 => //.
    - move=> s1 s2 A B sA _ <- fA.
      by rewrite (build_na_is_dead H1 fA sA) is_dead_dead.
    - move=> s1 s2 r A B n eA rB IH fA.
      by apply: IH; apply: expand_no_free_alt eA.
    - move=> s1 s2 r A B n eA rB IH fA.
      by apply: IH; apply: expand_no_free_alt eA.
    - move=> s1 s2 A B r n fA nA H IH FA.
      apply: IH.
      apply: no_free_alt_next_alt FA nA.
  Qed.

  Lemma main {sP p t}:
    check_program sP -> tm_is_det sP t -> 
      is_det ((CallS p t)).
  Proof.
    move=> H1 fA HA.
    apply: runb_next_alt H1 _ HA.
    apply: fA.
  Qed.

  Print Assumptions  main.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == ACut end.
    
    Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

    Lemma cut_in_prem_tail_cut sP: AllTailCut -> check_program sP.
    Proof.
      rewrite /AllTailCut /check_program.
      rewrite /tail_cut /check_rules.
      move=> + pr => /(_ pr).
      remember (rules pr) as RS.
      apply: sub_all => r; clear.
      rewrite /check_rule.
      case X: rcallable_is_det => //=.
      case: r X => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sP p t:
      AllTailCut -> tm_is_det sP t -> is_det ((CallS p t)).
    Proof.
      move=> /(cut_in_prem_tail_cut sP).
      apply main.
    Qed.
  End tail_cut.

  Print Assumptions tail_cut_is_det.

End check.
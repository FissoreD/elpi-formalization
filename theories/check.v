From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Lemma tm2RC_kp {t1 k} : 
  tm2RC t1 = Some (RCallable_Kp k) -> t1 = Tm_Kp k.
Proof.
  case: t1 k => //=.
  - move=> k1 k2 []; congruence.
  - move=> h b k; case X: tm2RC => //.
Qed.

Lemma deref_kp {s1 t k}:
  tm2RC (deref s1 t) = Some (RCallable_Kp k) ->
    (t = Tm_Kp k) \/ (exists v, t = Tm_V v /\ sigma s1 v = Some (Tm_Kp k)).
Proof.
  case: t k => //=.
  - move=> k1 k2 []; left; congruence.
  - move=> v k; case x: sigma => [t1|]//=.
    move=>/tm2RC_kp?; subst.
    right; by eexists.
  - move=> h b k; case X: tm2RC => //.
Qed.

Section checker.
  Definition sigV := V -> option S.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint getS_Callable (sP: sigT) (t: Callable) : option S :=
    match t with
    | Callable_Kp pn => Some (sP pn)
    | Callable_V vn => None (*TODO: use sV vn instead*)
    | Callable_Comb hd _ => getS_Callable sP hd
    end.

  Fixpoint rcallable_is_det (sP: sigT) (t:RCallable) : bool :=
    match t with
    | RCallable_Comb h _ => rcallable_is_det sP h
    | RCallable_Kp k => is_det_sig (sP k)
    end.

  Definition tm_is_det (sP: sigT) (t : Callable) :=
    odflt false (omap is_det_sig (getS_Callable sP t)).

  Definition check_atom sP (a: A) :=
    match a with
    | ACut => true
    | ACall t => tm_is_det sP t
    end. 

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

Section check.

  Fixpoint has_cut A :=
    match A with
    | CutS => true
    | CallS _ _ => false
    | Bot | Dead => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut B0 && has_cut B)
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
    - move=> A HA B0 _ B HB dA; rewrite HA//.
  Qed.

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
        [&& (has_cut B0 && has_cut B) || det_tree sP A, 
          det_tree sP B & det_tree sP B0]
    | Or A _ B =>
        det_tree sP A && 
          if has_cut A then det_tree sP B else (B == cutr B)
    end.

  Lemma no_alt_cut {sP A}: det_tree sP (cutr A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB cutr2 eqxx if_same.
    + move=> A HA B0 HB0 B HB /=; rewrite is_ko_cutr//.
  Qed.

  Lemma no_alt_dead {sP A}: is_dead A -> det_tree sP A.
  Proof.
    elim: A => //.
    + move=> A HA s B HB /=/andP[dA]; rewrite HA// has_cut_dead//.
    + move=> A HA B0 HB0 B HB /=dA; rewrite is_dead_is_ko//.
  Qed.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[kA kB]; rewrite fun_if/= is_ko_cutr kA !is_ko_cutl// if_same//.
    move=> A HA B0 HB0 B HB /=; rewrite fun_if/=.
    rewrite !has_cut_cut/=.
    case:ifP => // _.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[cB0] /HB->; rewrite orbT//.
  Qed.

  Lemma all_det_nfa_big_and {p sP l}: all (check_atom sP) l -> det_tree sP (big_and p l).
  Proof.
    elim: l => //= a l IH/andP[] H1 H2.
    case: a IH H1 => //= [|t] IH H1; rewrite ?H1 IH//=orbT//.
  Qed.

  Lemma cut_followed_by_det_has_cut {sP p l}:
      check_atoms sP l -> has_cut (big_and p l).
  Proof. by elim: l => //= -[]//= _ l H/H->. Qed.

  Lemma cut_followed_by_det_nfa_and {sP p bo} :
    check_atoms sP bo -> det_tree sP (big_and p bo).
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      by move=>/orP[/all_det_nfa_big_and|/IH]->; rewrite orbT.
    by move=> H; rewrite IH//!andbT andbb (cut_followed_by_det_has_cut H).
  Qed.

  Lemma no_free_alt_cutl {sP A}: det_tree sP (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      rewrite fun_if/=HA HB cutr2 eqxx no_alt_cut if_same.
      case: ifP => //dA.
      rewrite has_cut_dead//no_alt_dead//.
    move=> A HA B0 HB0 B HB /=.
    rewrite fun_if/= HA HB !has_cut_cut/= !no_alt_cut/= !orbT if_same//.
  Qed.

  Variable u : Unif.

  Lemma tiki_taka {sP s s3 modes t q hd1}:
    let t' := tm2RC (deref s (Callable2Tm t)) in
    t' = Some q ->
    tm_is_det sP t ->
      H u modes q hd1 s = Some s3 ->
        rcallable_is_det sP hd1.
  Proof.
    move=>/=.
    elim: modes q hd1 t s s3 => //=.
      move=> []//=k []//= k1 t s1 s2; case: eqP => //=<-.
      move=>/deref_kp [].
        case: t => //= k2 [->]//.
      move=> [v[]]; case: t => //.
    move=> []//ml IH []//h1 b1 []//=h2 b2 t s1 s2 H1 H2 H3.
      move: H3; case e: H => //=[s1'] H3.
      case: t H1 H2 => //= c t.
      case H : tm2RC => //=[h1'] [??]; subst => /=.
      rewrite/tm_is_det/=.
      case X: getS_Callable => //[S] H1.
      apply: IH H _ e.
      rewrite/tm_is_det X//.
    move: H3; case e: H => //=[s1'] H3.
    case: t H1 H2 => //= c t.
    case H : tm2RC => //=[h1'] [??]; subst => /=.
    rewrite/tm_is_det/=.
    case X: getS_Callable => //[S] H1.
    apply: IH H _ e.
    rewrite/tm_is_det X//.
  Qed.


  Lemma is_det_no_free_alt {sP t s1} {p:program}:
    check_rules sP p.(rules) -> tm_is_det sP t -> 
      det_tree sP (big_or u p s1 t).
  Proof.
    rewrite /big_or/F.
    case X: tm2RC => //=[q].
    case: p => rules modes sig1 /=.
    generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
    clear -X.
    elim: rules modes s1 t pr q X => //=.
    move=> [] hd bo rules IH modes s/= t p q X /andP[H1 H1'] H2.
    case H: H => /= [s2|]; last first.
      apply: IH X H1' H2.
    clear IH.
    move: H.
    move: H1 => /orP[]; last first.
      move=> + _.
      elim: rules H1' bo => //=.
        move=> _ bo.
        apply cut_followed_by_det_nfa_and.
      move=> [] hd1 bo1/= l IH /andP [H3 H4] bo H1.
      case H: H => [s3|]//=; last first.
        by apply: IH.
      rewrite (cut_followed_by_det_has_cut H1).
      rewrite cut_followed_by_det_nfa_and//=.
      rewrite IH//=.
      move: H3 => /orP[] => //.
      move=> /eqP H3; exfalso.
      have /= := tiki_taka X H2 H; congruence.
    move=> /eqP H3 H4.
    have /= := tiki_taka X H2 H4; congruence.
  Qed.

  Lemma expand_has_cut {A s}: 
    has_cut A -> has_cut (get_tree (expand u s A)) \/ is_cutbrothers (expand u s A).
  Proof.
    elim: A s; try by move=> /=; auto.
    - move=> A HA s1 B HB s /=/andP[kA kB].
      case: ifP => dA.
        rewrite (is_ko_expand _ kB)/=kA kB; auto.
      rewrite (is_ko_expand _ kA)/=kA kB; auto.
    - move=> A HA B0 _ B HB s /=/orP[].
        move=> /(HA s); case: expand => [|||] C/= []//; auto => cC.
        - by rewrite cC /=; left.
        - by rewrite cC /=; left.
        left; rewrite get_tree_And /=.
        by case: ifP; rewrite ?cC // has_cut_cutl.
      case/andP=> cB0 cB.
      case: expand => [|||] C/=; rewrite ?cB ?cB0 ?orbT; auto.
      move: (HB (get_substS s C)).
      by case: expand => [|||] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
  Qed.

  Lemma expand_no_free_alt {sP s1 A r} : 
    check_program sP -> det_tree sP A -> 
      expand u s1 A = r ->
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
          case: expand => //= [|||] C nnC/=; rewrite get_tree_Or/=fA/=cA?HB//.
        have:= HA s1 fA.
        have := @expand_has_cut _ s1 cA.
        case X: expand => //= -[]// + ->; rewrite ?nnB ?no_alt_cut //=; try by case: has_cut.
        by rewrite cutr2 eqxx if_same.
      move/eqP->.
      case: ifP => [dA|].
        rewrite get_tree_Or/=cA no_alt_dead//=is_ko_expand//=?is_ko_cutr//cutr2//.
      have:= HA s1 fA => + dA.
      case Y: expand => /=->; rewrite !cutr2 eqxx no_alt_cut if_same//.
    - move=> A HA B0 HB0 B HB s /=.
      move=>/orP[].
        move=>kA; rewrite is_ko_expand///=kA//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => //= [|||C]; try rewrite cB0 cB/= fB0 fB !orbT//.
        rewrite get_tree_And.
        rewrite /= (HB (get_substS s C)) //.
        have := @expand_has_cut _ (get_substS s C) cB.
        case H1: (is_cutbrothers (expand u (get_substS s C) B)).
          move=>_/=; rewrite has_cut_cut// no_free_alt_cutl no_alt_cut !orbT//.
        move=> []//H2; rewrite H2 fB0 cB0 orbT//.
      have:= HA s fA.
      case X: expand => //= [|||C] H1; try rewrite H1 orbT fB fB0 orbT//.
      have:= HB (get_substS s C) fB; case Y: expand => //= H2; try rewrite fB0 H2 H1 orbT !orbT//.
      rewrite !no_free_alt_cutl no_alt_cut H2 !orbT//.
  Qed.

  Goal forall sP s, det_tree sP (Or OK s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB /=/andP[kA kB].
      rewrite !is_ko_success// if_same//.
    - move=> A HA B0 HB0 B HB /=/orP[].
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
    - by move=> A HA B0 HB0 B HB/=/andP[]/HA->/HB->; rewrite andbF.
  Qed.

  Lemma expand_next_alt {sP A} : 
    check_program sP -> det_tree sP A -> success A ->
      next_alt true A = None.
  Proof.
    move=> H; elim: A => //=.
    - move=> A HA s B HB /andP[nA IH].
      case: ifP => [dA sB|dA sA].
        rewrite is_dead_next_alt// HB//.
        move: IH; case: ifP => //.
        move=> _ /eqP->; rewrite no_alt_cut//.
      rewrite HA//.
      move: IH; case: ifP.
        move=> /has_cut_success; congruence.
      move=> _ /eqP->; rewrite next_alt_cutr//.
    - move=> A HA B0 HB0 B HB /orPT[].
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
    - move=> A HA B0 HB0 B HB C b/=.
      move=> /orP[].
        move=> cA.
        case X: next_alt => // [A'|].
          case: ifP => //= fA.
            case Y: next_alt => //[B0'][<-]/=.
            by rewrite (HA _ _ cA X)//.
          case: ifP => fB.
            case Y: next_alt => //[B'|].
              move=> -[<-]/=; rewrite ?has_cut_clean_success//cA//.
            case W: next_alt => //[A''].
            case Z: next_alt => //[B0''][<-]/=.
            rewrite (HA _ _ cA W)//.
          move=>[<-]/=; rewrite cA//.
        case: ifP => //= fA.
        case: ifP => [sA|sA[<-]]/=; rewrite?cA//.
        case Y: next_alt => //[B'|].
          move=>[<-]/=; rewrite cA//.
        case W: next_alt => //[A'].
        case Z: next_alt => //[B0'][<-]/=.
        rewrite (HA _ _ cA W)//.
      move=>/andP[cB0 cB].
      case: ifP => /= fA.
        case X: next_alt => //= [A'].
        case Y: next_alt => //= [B0'] [<-]/=.
        rewrite cB0 (HB0 _ _ cB0 Y) orbT//.
      case: ifP => sA.
        case X: next_alt => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: next_alt => //[A'].
        case Z: next_alt => //[B0'][<-]/=.
        by rewrite cB0 (HB0 _ _ cB0 Z) orbT.
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
        rewrite is_dead_next_alt//.
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
    - move=> A HA B0 HB0 B HB C b /=.
      move=>/orP[].
        move=>kA.
        by rewrite is_ko_failed// is_ko_next_alt//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case: ifP => // fA.
          case X: next_alt => // [A'].
          case Y: next_alt => //[B0'] [<-]/=.
          by rewrite cB0 fB0 (has_cut_next_alt cB0 Y) (HB0 _ _ fB0 Y) orbT.
        case: ifP => sA; last first.
          by move=> [<-]/=; rewrite cB0 cB fB fB0 orbT.
        have:= HB _ b fB.
        case X: next_alt => // [B'|].
          by move=> /(_ _ erefl) fD [<-]/=; rewrite cB0  (has_cut_next_alt cB X) (HB _ _ fB X) fB0 orbT.
        move=> _; case Y: next_alt => //[A'].
        by case Z: next_alt => //[B0'][<-]/=; rewrite cB0 (has_cut_next_alt cB0 Z) (HB0 _ _ fB0 Z) fB0 orbT.
      case: ifP => // _.
        case X: next_alt => // [A'].
        case Y: next_alt => // [B0'][<-]/=.
        by rewrite (HA _ _ fA X) fB0 (HB0 _ _ fB0 Y) !orbT.
      case: ifP => sA; last first.
        by move=>[<-]/=; rewrite fA fB fB0 !orbT.
      case X: next_alt => // [B'|].
        by move=> [<-]/=; rewrite fA fB0 (HB _ _ fB X)!orbT.
      case Y: next_alt => // [A'].
      case Z: next_alt => //[B0'] [<-]/=.
      by rewrite (HA _ _ fA Y) (HB0 _ _ fB0 Z) fB0 !orbT.
  Qed.

  Lemma expand_next_alt_failed {sP A B C s b}:
    check_program sP ->
      det_tree sP A -> expand u s A = Failure B ->
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
    - by move=> A HA B0 _ B HB dA; rewrite is_dead_is_ko//.
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
    - by move=> *; rewrite is_dead_dead.
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

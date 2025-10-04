From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run_prop.

Module check (U:Unif).
  Module VS := RunP(U).
  Import Language VS Run.

  Print sigT.
  Definition sigV := V -> option S.

  Fixpoint get_head (sP: sigT) (sV: sigV) (t: Tm) : option S :=
    match t with
    | Code (p pn) => Some (sP pn)
    | Code (v vn) => sV vn
    | Data _ => Some (b Exp)
    | Comb hd _ => get_head sP sV hd
    end.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Definition det_term (sP: sigT) (sV: sigV) (t : Tm) :=
    match get_head sP sV t with 
    | None => false
    | Some sig => is_det_sig sig
    end.

  Definition det_atom sig s (a: A) :=
    match a with
    | Cut => true
    | Call t => det_term sig s t
    end.

  Fixpoint has_cut A :=
    match A with
    | Goal _ Cut => true
    | Goal _ (Call _) => false
    | Bot | Dead => true
    | OK | Top => false
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

  (* a free alternative can be reached without encountering a cutr following SLD 
  
    "((A, !, A') ; B) , C" is OK since B is not free
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)
  
  *)
  Fixpoint no_free_alt (sP:sigT) (sV:sigV) A :=
    match A with
    | Goal _ a => det_atom sP sV a
    | Top | Bot | OK => true
    | Dead => true
    (* | And (Or A1 _ A2) B0 B ->
      ((is_ko A1 || is_ko B) && (is_ko A2 || is_ko B0)) *)
    | And A B0 B =>
      (is_ko A) || 
        [&& (has_cut B0 && has_cut B) || no_free_alt sP sV A, 
          no_free_alt sP sV B & no_free_alt sP sV B0]
    | Or A _ B =>
        no_free_alt sP sV A && 
          if has_cut A then no_free_alt sP sV B else (B == cutr B) (* TODO: should be is_ko *)
    end.

  Lemma no_alt_cut {sP sV A}: no_free_alt sP sV (cutr A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB cutr2 eqxx if_same.
    + move=> A HA B0 HB0 B HB /=; rewrite is_ko_cutr//.
  Qed.

  Lemma no_alt_dead {sP sV A}: is_dead A -> no_free_alt sP sV A.
  Proof.
    elim: A => //.
    + move=> A HA s B HB /=/andP[dA]; rewrite HA// has_cut_dead//.
    + move=> A HA B0 HB0 B HB /=dA; rewrite is_dead_is_ko//.
  Qed.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[kA kB]; rewrite fun_if/= is_ko_cutr kA !is_ko_cutl// if_same//.
    move=> A HA B0 HB0 B HB /=/orP[].
      by move=>/HA->.
    move=>/andP[cB0 cB].
    rewrite HB0//HB//orbT//.
  Qed.

  Section has_cut. 

    Fixpoint cut_followed_by_det (sP :sigT) (sV:sigV) (s: seq A) :=
      match s with
      | [::] => false
      | Cut :: xs => all (det_atom sP sV) xs || cut_followed_by_det sP sV xs
      | Call _ :: xs => cut_followed_by_det sP sV xs
      end.

    Definition all_cut_followed_by_det_aux sP sV rules :=
      all (fun x => (det_term sP sV x.(head) == false) || cut_followed_by_det sP sV x.(premises)) rules.

    Definition all_cut_followed_by_det sP sV := 
      forall pr, all_cut_followed_by_det_aux sP sV (rules pr).

    Lemma all_det_nfa_big_and {p sP sV l}: all (det_atom sP sV) l -> no_free_alt sP sV (big_and p l).
    Proof.
      elim: l => //= a l IH/andP[] H1 H2.
      by rewrite H1 orbT IH//.
    Qed.

    Lemma cut_followed_by_det_has_cut {sP sV p l}:
       cut_followed_by_det sP sV l -> has_cut (big_and p l).
    Proof. by elim: l => //= -[]//= _ l H/H->. Qed.

    Lemma cut_followed_by_det_nfa_and {sV sP p bo} :
      cut_followed_by_det sP sV bo -> no_free_alt sP sV (big_and p bo).
    Proof.
      elim: bo => //=.
      move=> [|t] /= l IH.
        by move=>/orP[/all_det_nfa_big_and|/IH]->; rewrite orbT.
      by move=> H; rewrite IH//!andbT andbb (cut_followed_by_det_has_cut H).
    Qed.

    Lemma is_det_no_free_alt {sP sV t s1} {p:program}:
      all_cut_followed_by_det_aux sP sV p.(rules) -> det_term sP sV t -> 
        no_free_alt sP sV (big_or p s1 t).
    Proof.
      rewrite /big_or/F.
      case: p => rules modes sig1 /=.
      generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
      clear.
      elim: rules modes s1 t pr => //.
      move=> [] hd bo rules IH modes sig1/= t p /andP[H1 H1'] H2.
      case H: H => /= [s2|]; last first.
        apply IH => //.
      clear IH.
      move: H.
      generalize (modes t) as m => {}modes.
      have X: t = hd by admit.
      subst.
      move=> _Ign. (* TODO *)
      rewrite H2 in H1.
      elim: rules H1' bo H1 => //=.
        move=> _ bo.
        apply cut_followed_by_det_nfa_and.
      move=> [] hd1 bo1/= l IH /andP [H3 H4] bo H1.
      case H: H => [s3|]//=; last first.
        by apply: IH.
      rewrite (cut_followed_by_det_has_cut H1).
      have ?: hd = hd1 by admit.
      subst.
      rewrite H2 in H3.
      by rewrite (cut_followed_by_det_nfa_and H1) IH// if_same.
    Admitted.

  Lemma expand_has_cut {A s}: 
    has_cut A -> has_cut (get_state (expand s A)) \/ is_cutbrothers (expand s A).
  Proof.
    elim: A s; try by move=> /=; auto.
    - by move=> p []//=; right.
    - move=> A HA s1 B HB s /=/andP[kA kB].
      case: ifP => dA.
        rewrite (is_ko_expand kB)/=kA kB; auto.
      rewrite (is_ko_expand kA)/=kA kB; auto.
    - move=> A HA B0 _ B HB s /=/orP[].
        move=> /(HA s); case: expand => [s1|s1||s1] C/= []//; auto => cC.
        - by rewrite cC /=; left.
        - by rewrite cC /=; left.
        left; rewrite get_state_And /=.
        by case: ifP; rewrite ?cC // has_cut_cutl.
      case/andP=> cB0 cB.
      case: expand => [s1|s1||s1] C/=; rewrite ?cB ?cB0 ?orbT; auto.
      move: (HB s1 cB).
      by case: expand => [s2|s2||s2] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
  Qed.

  Lemma no_free_alt_cutl {sP sV A}: no_free_alt sP sV (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      rewrite fun_if/=HA HB cutr2 eqxx no_alt_cut if_same.
      case: ifP => //dA.
      rewrite has_cut_dead//no_alt_dead//.
    move=> A HA B0 HB0 B HB /=.
    rewrite HA HB HB0 !orbT//.
      (* rewrite HB/=success_cut sA orbT//. *)
    (* rewrite success_cut sA/=. *)
  Qed.

  Lemma expand_no_free_alt {sP sV s1 A r} : 
    (* valid_state A -> *)
    all_cut_followed_by_det sP sV -> no_free_alt sP sV A -> 
      expand s1 A = r ->
        no_free_alt sP sV (get_state r).
  Proof.
    move=> H + <-; clear r.
    elim: A s1 => //.
    - move=> p []// t s1 /=.
      apply: is_det_no_free_alt.
      by have:= H p.
    - move=> A HA s B HB s1 /=/andP[fA].
      case: ifP => //= cA.
        move=> nnB.
        case: ifP => //= dA.
          have:= HB s1 nnB.
          case: expand => //= [_|_||_] C nnC; rewrite fA nnC cA//.
        have:= HA s1 fA.
        have := @expand_has_cut _ s1 cA.
        case X: expand => //= -[]// + ->; rewrite ?nnB ?no_alt_cut //=; try by case: has_cut.
        by rewrite cutr2 eqxx if_same.
      move/eqP->.
      case: ifP => [dA|].
        rewrite get_state_Or/=cA no_alt_dead//=is_ko_expand//=?is_ko_cutr//cutr2//.
      have:= HA s1 fA => + dA.
      case Y: expand => /=->; rewrite !cutr2 eqxx no_alt_cut if_same//.
    - move=> A HA B0 HB0 B HB s /=.
      move=>/orP[].
        move=>kA; rewrite is_ko_expand///=kA//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => //= [|||s1 C]; try rewrite cB0 cB/= fB0 fB !orbT//.
        rewrite get_state_And.
        rewrite /= (HB s1) //.
        have := @expand_has_cut _ s1 cB.
        case H1: (is_cutbrothers (expand s1 B)).
          move=>_/=; rewrite has_cut_cutl// no_free_alt_cutl no_free_alt_cutl !orbT//.
        move=> []//H2; rewrite H2 fB0 cB0 orbT//.
      have:= HA s fA.
      case X: expand => //= [|||s1 C] H1; try rewrite H1 orbT fB fB0 orbT//.
      have:= HB s1 fB; case Y: expand => //= H2; try rewrite fB0 H2 H1 orbT !orbT//.
      rewrite !no_free_alt_cutl H2 !orbT//.
  Qed.

  Goal forall sP sV s, no_free_alt sP sV (Or OK s OK) == false.
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

  Lemma expand_next_alt {sP sV s1 A s2 B} : 
    all_cut_followed_by_det sP sV -> no_free_alt sP sV A ->
      expand s1 A = Success s2 B -> forall s3, next_alt s3 B = None.
  Proof.
    move=> H.
    elim: A s1 B s2 => //.
    - by move=> /= s1 A s2 _ [_ <-]//.
    - move=> p []//.
    - move=> A HA s B HB s1 C s2.
      move=> /=/andP[fA].
      case: (ifP  (is_dead _)) => dA.
        rewrite has_cut_dead// => fB.
        have:= HB s1 _ _ fB.
        case X: expand => ///(_ _ _ erefl) H1 [??]; subst => /= s3.
        rewrite dA H1//.
      have:= HA s1 _ _ fA.
      case X: expand => // [s4 A'] /(_ _ _ erefl) H1 + [_<-] s3/=.
      rewrite (expand_not_dead dA X) H1.
      rewrite success_has_cut ?(expand_solved_success X)//.
      move=>/eqP->.
      rewrite is_ko_next_alt?if_same//is_ko_cutr//.
    - move=> A HA B0 _ B HB s1 C s2 /=.
      move=>/orP[].
        move=> kA; rewrite is_ko_expand//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => // [s3 D].
        have:= HB s3 _ _ fB.
        have sbF:= has_cut_success cB.
        case Y: expand => ///(_ _ _ erefl) H1 [??] s4;subst.
        have []:= expand_solved_success Y; congruence.
      have:= HA s1 _ _ fA.
      case X: expand => //[s3 D]/(_ _ _ erefl) H1.
      have:= HB s3 _ _ fB.
      case Y: expand => ///(_ _ _ erefl) H2 [??];subst => /= s4.
      by rewrite H1 H2; rewrite !if_same.
  Qed.

  Lemma expandedb_next_alt_done {sP sV s A s1 B b}: 
    all_cut_followed_by_det sP sV -> 
      no_free_alt sP sV A -> expandedb s A (Done s1 B) b ->
        forall s0, next_alt s0 B = None.
  Proof.
    remember (Done _ _) as d eqn:Hd => Hz + H.
    elim: H s1 B Hd => //; clear -Hz.
    - {
      move=> s s' A B HA s1 C [_ <-] fA; clear s1 C.
      apply: expand_next_alt Hz fA HA.
    } 
    - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA).
    - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA).
  Qed.

  Lemma has_cut_next_alt {s A s' B}: 
    has_cut A -> next_alt s A = Some (s', B) -> has_cut B.
  Proof.
    elim: A s B s' => //.
    - move=>/=p[]//[]?//?? _ [_<-]//.
    - move=> A HA s1 B HB s C s' /=.
      move=>/andP[kA kB].
      by rewrite !is_ko_next_alt//; rewrite !if_same//.
    - move=> A HA B0 HB0 B HB s C s' /=.
      case: ifP => //= dA /orP[].
        move=> cA.
        have:= HA s _ _ cA.
        case: next_alt => // [[s2 D]|].
          move=>/(_ _ _ erefl) cD.
          case: ifP => //= fA.
            case: ifP => //= fB0 [??]; subst.
            by rewrite /= cD.
          case: next_alt => //[[s3 E]|].
            by move=>[??]; subst; rewrite/=cA.
          by case: ifP => fB //=[??]; subst; rewrite /= cD.
        move=> _; case: ifP => //= fA.
        case: next_alt => //= [[s2 D]][??]; subst => /=.
        by rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= fA.
        by case: next_alt => //= [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
      have:= HB s _ _ cB.
      case: next_alt => //= [[s1 D]|].
        by move=> /(_ _ _ erefl) cD [_ <-]/=; rewrite cB0 cD orbT.
      by move=> _; case: next_alt => // [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
  Qed.

  Lemma no_free_alt_next_alt {sP sV s1 A s2 B}:
    no_free_alt sP sV A -> next_alt s1 A = Some (s2, B) -> no_free_alt sP sV B.
  Proof.
    elim: A s1 B s2 => //.
    - move=> []//??? _ [_<-]//.
    - move=>/=??[]//??? _ [_<-]//.
    - move=> A HA s B HB s1 C s2 /=.
      move=>/andP[fA].
      case: (ifP (is_dead _)) => dA.
        rewrite has_cut_dead//.
        move=> fB.
        have:= HB (Some s) _ _ fB.
        case X: next_alt => //[[s3 D]] /(_ _ _ erefl) fD[_ <-]/=.
        rewrite no_alt_dead// has_cut_dead// fD.
      case: ifP => cA.
        move=> fB.
        have:= (HA s1 _ _ fA).
        case X: next_alt => //[[s3 D]|].
          have cD:= has_cut_next_alt cA X.
          by move=> /(_ _ _ erefl) fD[_<-]/=; rewrite fD cD fB.
        move=> _.
        case: ifP => dB//.
        have idA := @is_dead_dead A.
        (* case: ifP => // Fb. *)
          case Y: next_alt => //[[s3 D]].
          move=>[_ <-]/=.
          rewrite no_alt_dead// has_cut_dead//.
          apply: HB fB Y.
        (* move=>[_<-]/=; rewrite no_alt_dead//has_cut_dead// fB. *)
      move=>/eqP->; rewrite (is_ko_next_alt is_ko_cutr) if_same.
      have:= HA s1 _ _ fA.
      case: next_alt => // [[s3 D]]/(_ _ _ erefl) fD [_ <-]/=.
      by rewrite fD cutr2 eqxx no_alt_cut if_same.
    - move=> A HA B0 HB0 B HB s1 C s2 /=.
      case: (ifP (is_dead _)) => dA//.
      move=>/orP[].
        move=>kA.
        by rewrite is_ko_failed// is_ko_next_alt//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case: ifP => // fA.
          case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
          by rewrite cB0 fB0 orbT.
        have:= HB s1 _ _ fB.
        case X: next_alt => // [[s3 D]|].
          by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite cB0 (has_cut_next_alt cB X) fD fB0 orbT.
        move=> _; case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
        by rewrite cB0 fB0 orbT.
      case: ifP => // _.
        have:= HA s1 _ _ fA.
        case X: next_alt => // [[s3 D]].
        move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
        by rewrite fD orbT fB0 orbT.
      have:= HB s1 _ _ fB.
      case: next_alt => // [[s3 D]|].
        by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite fA fD fB0 !orbT.
      move=> _.
      have:= HA s1 _ _ fA.
      case X: next_alt => // [[s3 D]].
      move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
      by rewrite fD orbT fB0 orbT.
  Qed.


  Lemma expand_next_alt_failed {sP sV A B C s s'}:
    all_cut_followed_by_det sP sV ->
      no_free_alt sP sV A -> expand s A = Failure B ->
        forall sN, next_alt sN B = Some (s', C) -> no_free_alt sP sV C.
  Proof.
    move=> Hz.
    elim: A B C s s' => //.
    - move=> /=????? []<-//.
    - move=> /=????? []<-//.
    - move=> ? []//.
    - move=> A HA s1 B HB C D s s' /=++sN.
      move=>/andP[fA].
      case: (ifP (is_dead _)) => dA.
        rewrite has_cut_dead// => fB.
        have:= HB _ _ s _ fB.
        case: expand => // E /(_ _ _ _ erefl (Some s1)) + [<-]/=.
        rewrite dA.
        case: next_alt => //[[s2 F]] /(_ _ _ erefl) + [_<-]/=.
        by move=> /= ->; rewrite has_cut_dead// no_alt_dead.
      case: ifP => //.
        have := HA _ _ s _ fA _ sN.
        case X: expand => // [E] /(_ _ _ _ erefl) + cA + [?]; subst.
        rewrite /= (expand_not_dead dA X).
        have:= @expand_has_cut _ s cA; rewrite X/= => -[]// cE.
        case Y: next_alt => //[[s2 F]|].
          move=> /(_ _ _ erefl) fF fB [_ <-] /=.
          have cF:= has_cut_next_alt cE Y.
          by rewrite fF cF fB.
        move=>_ fB.
        case: ifP => // dB.
        have dDe := @is_dead_dead E.
        (* case:ifP => //FB. *)
          case nB : next_alt => //= [[s2 F]] [_<-]/=.
          rewrite no_alt_dead// has_cut_dead// (no_free_alt_next_alt fB nB)//.
        (* move=>[_<-]/=. *)
        (* rewrite no_alt_dead// has_cut_dead// fB. *)
      move=> cA /eqP->.
      have:= HA _ _ s _ fA _ sN.
      case X: expand => // [E] /(_ _ _ _ erefl) + [<-]/=.
      have kcB := @is_ko_cutr B.
      rewrite /= (expand_not_dead dA X) (is_ko_next_alt kcB).
      rewrite if_same.
      case Y: next_alt => //[[s2 F]].
      move=> /(_ _ _ erefl) fF [_ <-] /=.
      by rewrite fF no_alt_cut cutr2 eqxx if_same.
    - move=> A HA B0 _ B HB C D s s' /= ++sN.
      move=> /orP[].
        move=> kA; rewrite is_ko_expand// => -[<-]/=.
        rewrite is_ko_failed// is_ko_next_alt// if_same//.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => //[E|s1 E].
          move=> [<-]/=.
          case: ifP => // dS.
          case: ifP => // fS.
            case nE: next_alt => [[s3 F]|]//.
            by case: ifP => //FB0 [_<-]/=; rewrite cB0 fB0 orbT.
          case Y: next_alt => //[[s3 F]|].
            by move=>[_ <-]/=; rewrite cB0 (has_cut_next_alt cB Y) fB0 (no_free_alt_next_alt fB Y) orbT.
          by case: next_alt => // [[s3 F]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
        have:= HB _ _ s1 _ fB _ sN.
        case Z: expand => // [F] /(_ _ _ _ erefl) + [<-]/=.
        case: ifP => //dE; case:ifP=>FE.
          move=> _.
          by case: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
        case Y: next_alt => //[[s3 G]|].
          move=>/(_ _ _ erefl) nG.
          (* have [? ->]:= next_alt_some Y s. *)
          have := @expand_has_cut _ s1 cB.
          rewrite Z/==>-[]//cF.
          by move=>[_ <-]/=; rewrite cB0 nG fB0 (has_cut_next_alt cF Y) orbT.
        have [??]:= expand_solved_same X; subst => _.
        (* move=>_; rewrite (next_alt_none Y). *)
        case W: next_alt => //[[s3 G]]; case: ifP => // _[_<-]/=.
        by rewrite cB0 fB0 orbT.
      have:= HA _ _ s _ fA _ sN.
      case X: expand => //[E|s1 E].
        move=> /(_ _ _ _ erefl) + [<-]/=.
        case: ifP => // dS.
        case: ifP => //fE.
          case: next_alt => //[[s4 G]] /(_ _ _ erefl) fG.
          by case: ifP => // _[_<-]/=; rewrite fB0 fG orbT orbT.
        case Y: (next_alt sN B) => //[[s4 G]|].
          by move=> _ [_<-]/=; rewrite (no_free_alt_next_alt fB Y) fB0 (expand_no_free_alt Hz fA X) orbT orbT.
        case: next_alt => //[[s3 G]] /(_ _ _ erefl)fG; case:ifP=>//_[_<-]/=.
        by rewrite fG fB0 orbT orbT.
      move=> _.
      have:= HB _ _ s1 _ fB _ sN.
      case Z: expand => // [F] /(_ _ _ _ erefl) {}HB [<-]/=.
      have /= fE := expand_no_free_alt Hz fA X.
      case: ifP => //dE; case:ifP=>FE.
        case W: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=.
        by rewrite fB0 (no_free_alt_next_alt fE W) orbT orbT.
      move: HB.
      case W: next_alt => //[[s3 G]|].
        (* have [? XX]:= next_alt_some W s1. *)
        move=> /(_ _ _ erefl) fG [_<-]/=; rewrite fG fB0 fE orbT orbT//.
      case T: next_alt => //[[s3 G]] => _; case:ifP => //[fB01][_<-]/=.
      by rewrite fB0 (no_free_alt_next_alt fE T) orbT orbT.
    Qed.

  Lemma expandedb_next_alt_failed {sP sV s A B C s' b1}: 
    all_cut_followed_by_det sP sV ->
      no_free_alt sP sV A ->
        expandedb s A (Failed B) b1 -> 
          forall sN, next_alt sN B = Some (s', C) -> no_free_alt sP sV C.
  Proof.
    remember (Failed _) as f eqn:Hf => Hz + H.
    elim: H B C s' Hf => //; clear -Hz.
    - move=> s A B HA ? C s' [<-] fA nB.
      apply: expand_next_alt_failed Hz fA HA nB.
    - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA) _ nB.
    - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA) _ nB.
  Qed.

  Definition is_det A := forall s s' B,
    run s A s' B -> forall s2, next_alt s2 B = None.

  Lemma runb_next_alt {sP sV A}: 
    all_cut_followed_by_det sP sV -> 
      no_free_alt sP sV A -> is_det A.
  Proof.
    rewrite/is_det.
    move=> H1 H2 s s' B []b H3.
    elim: H3 H2; clear -H1 => //.
    - move=> s s' A B C b HA -> fA s2.
      have H := expandedb_next_alt_done H1 fA HA _.
      have sB := expanded_Done_success HA.
      have//:= next_alt_clean_success sB (H s2).
    - move=> s s' r A B C D b1 b2 b3 HA HB HC IH ? fA s2; subst.
      apply: IH.
      apply: expandedb_next_alt_failed H1 fA HA _ HB.
  Qed.

  Lemma main {sP sV p t}:
    all_cut_followed_by_det sP sV -> det_term sP sV t -> 
      is_det (Goal p (Call t)).
  Proof.
    move=> H1 fA HA.
    apply: runb_next_alt H1 _ HA.
    apply: fA.
  Qed.
  End has_cut.

  Print Assumptions  main.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.
    
    Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

    Lemma cut_in_prem_tail_cut sP sV: AllTailCut -> all_cut_followed_by_det sP sV.
    Proof.
      rewrite /AllTailCut /all_cut_followed_by_det.
      rewrite /tail_cut /all_cut_followed_by_det_aux.
      move=> + pr => /(_ pr).
      remember (rules pr) as RS.
      apply: sub_all => r; clear.
      case X: det_term => //=.
      case: r X => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sP sV p t:
      AllTailCut -> det_term sP sV t -> is_det (Goal p (Call t)).
    Proof.
      move=> /(cut_in_prem_tail_cut sP sV).
      apply main.
    Qed.
  End tail_cut.

  Print Assumptions tail_cut_is_det.

End check.

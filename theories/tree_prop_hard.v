From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop.
From det Require Import zify_ssreflect.

Section s.
  Variable u : Unif.
  Variable p : program.


  Lemma run_or0 {s1 A s B s2 r b}:
    run u p s1 (Or A s B) s2 r b -> b = false.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s B Ho; clear => //.
    - move=> s1 s2 r A B n + _ _ C s D ?; subst => /=.
      by case: ifP; case: step => [[]]//.
    - move=> s1 s2 r A B n + HB IH C s D ?; subst => /=.
      case: ifP => dC.
        case X: step => [[]D']//=[?]; subst; by apply: IH.
      case Y: step=> [[]C']//[?]; subst; by apply: IH.
    - move=> s1 s2 A B r n _ + H IH C s3 D ?; subst => /=.
      case: ifP => //= dA.
        case: next_alt => //= ? [/esym]; apply IH.
      case: next_alt => //=.
        move=>? [/esym]; apply IH.
      case: next_alt => //= ? [/esym]; apply IH.
  Qed.

  Lemma next_alt_run {A B C s s2 b1}:
    next_alt false A = B ->
      run u p s (build_na A B) s2 C b1 ->
        run u p s A s2 C b1.
  Proof.
    move=> <-{B}.
    case fA: (failed A).
      case X: next_alt => [A'|]/= H.
        by apply: run_fail fA X H.
      have [->[->->]]:= run_dead2 H.
      apply: run_dead fA X.
    rewrite next_alt_not_failed//.
  Qed.

  Definition get_dead A B := if is_dead A && ~~(is_dead B) then A else dead A.

  Lemma run_ko_left1 {s1 s2 A B A' B' sx}:
    is_ko A -> run u p s1 (Or A s2 B) sx (Or A' s2 B') false ->
      Texists b, run u p s2 B sx B' b /\ 
        (A' = get_dead A B').
  Proof.
    rewrite/get_dead.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember (Or A' _ _) as o2 eqn:Ho2 => + H.
    elim: H A B A' B' s2 Ho1 Ho2; clear.
    + move=> s _ A _ + <-<- A1 B1 A2 B2 s2 ? + kA'; subst => /=.
      rewrite (is_ko_success kA') (is_ko_next_alt _ kA').
      case: ifP =>// dA1 sB1.
      case X: next_alt => //=[B1'|] [??]; subst.
        repeat eexists.
          apply: run_done sB1 erefl _.
          by rewrite X.
        rewrite (next_alt_dead X)//.
      rewrite is_dead_dead.
      repeat eexists.
      apply: run_done sB1 erefl _.
      rewrite X => //.
    - move=> s1 s2 r A B n + HB IH A1 A2 B1 B2 s4 ?? kA1; subst => /=.
      by case: ifP => dC; case X: step => [[]]//.
    - move=> s1 s2 r A B n + HB IH A1 A2 B1 B2 s4 ?? kA1; subst => /=.
      rewrite (is_ko_step _ _ _ kA1)//.
      case: ifP => dC//.
      case X: step => [[]D']//[?]; subst;
      have {IH} [b[H1 ?]] := IH _ _ _ _ _ erefl erefl kA1; subst; rewrite dC/=;
      repeat eexists.
        apply:run_step X H1.
      apply:run_cut X H1.
    - move=> s1 s2 A B r n ++ rB IH A1 A2 B1 B2 s3 ?? kA1; subst => /=.
      rewrite (is_ko_next_alt _ kA1).
      case: ifP => /=dA H1.
        case X: next_alt => [A2'|]//=.
          move=> [?]; subst.
          have [b[H3 H4]] := IH _ _ _ _ _ erefl erefl kA1; subst.
          rewrite dA/=; repeat eexists.
          apply: run_fail H1 X H3.
        case X: next_alt => //[A2'][?]; subst.
        have [b[H3]]:= IH _ _ _ _ _ erefl erefl (is_dead_is_ko is_dead_dead).
        rewrite is_dead_dead dead2 if_same => ?; subst.
        repeat eexists.
        apply: next_alt_run X H3.
    - move=> _ A + + B1 C1 B2 C2 s ?/= + kB1; subst => /=++[??]; subst.
      rewrite (is_ko_next_alt _ kB1).
      rewrite is_dead_dead /= andbF.
      case: ifP => dB1 F.
        case X: next_alt => [C1'|]// _.
        repeat eexists; apply: run_dead F X.
      case X: next_alt => // _.
      repeat eexists.
      case fC1: (failed C1).
        apply: run_dead fC1 X.
      by rewrite next_alt_not_failed in X.
  Qed.

  Lemma run_ko_left2 {s2 X B B' r b1} sIgn:
    is_ko X -> run u p s2 B r B' b1 ->
    run u p sIgn (Or X s2 B) r (Or (get_dead X B') s2 B') false.
  Proof.
    rewrite/get_dead.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s _ A _ sA <-<- sIgn X kX; subst => /=.
      case dX: (is_dead X) => /=.
        apply: run_done.
          by rewrite/= sA dX.
          by rewrite /= dX//.
        rewrite/=dX //.
        case Y: next_alt => //=[A'|].
          rewrite (next_alt_dead Y)//.
        by rewrite is_dead_dead//.
      apply: run_fail => /=.
        by rewrite dX is_ko_failed.
        by rewrite/= dX is_ko_next_alt// next_alt_not_failed// success_failed//.
      apply: run_done.
        rewrite /= is_dead_dead//.
        rewrite/= is_dead_dead//.
      rewrite /=is_dead_dead// ?is_dead_dead//=; case: next_alt => //=.
      rewrite dead2//.
    + move=> s1 s2 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X) => /=.
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step IH.
        by rewrite /= dX HA//.
      have {}IH:= IH sIgn (dead X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead dead2 if_same in IH.
      have fA := step_not_failed HA notF.
      apply: run_fail.
        rewrite/=dX is_ko_failed//.
        by rewrite /= dX is_ko_next_alt// next_alt_not_failed//=failed_dead.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    (* TODO: the following case is same as previous... *)
    + move=> s1 s2 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X) => /=.
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step IH.
        by rewrite /= dX HA//.
      have {}IH:= IH sIgn (dead X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead dead2 if_same in IH.
      have fA := step_not_failed HA notF.
      apply: run_fail.
        rewrite/=dX is_ko_failed//.
        by rewrite /= dX is_ko_next_alt// next_alt_not_failed//=failed_dead.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    + move=> s1 s2 A B r n fA nB rC IH sIgn X kX; subst.
      case dX: (is_dead X).
        have {}IH:= IH sIgn _ kX.
        rewrite dX/= in IH; subst.
        apply: run_fail IH; rewrite /=dX//nB//.
      have {}IH:= IH sIgn (dead X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead/=dead2 if_same in IH; subst.
      by apply: run_fail IH; rewrite/= dX ?is_ko_failed// is_ko_next_alt//nB.
    + move=> s1 B fB nB sIgn X kX.
      rewrite is_dead_dead andbF.
      apply: run_dead; rewrite/=.
        by rewrite fB is_ko_failed//if_same.
      by rewrite nB/= is_ko_next_alt//if_same.
  Qed.

  Lemma run_or_ko_right1 {s2 X B B' SOL b1} sIgn:
    is_ko X -> run u p s2 B SOL B' b1 ->
    run u p s2 (Or B sIgn X) SOL (Or B' sIgn (if is_dead B' then dead X else if b1 == false then X else cutr X)) false.
  Proof.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s _ A _ sA <-<- sIgn X kX; subst => /=.
      apply: run_done => /=; rewrite?sA ?(success_is_dead sA)//.
      rewrite (is_ko_next_alt _ kX).
      case W: next_alt => //=[A'|].
        rewrite (next_alt_dead W)//.
      rewrite is_dead_dead//.
    + move=> s1 s2 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_step in HA.
      have:= IH sIgn (cutr X) is_ko_cutr.
      rewrite cutr2 if_same dead_cutr//.
    + move=> s1 s2 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_step in HA.
      apply: IH => //.
    + move=> s1 s2 A B r n fA nA rB IH sIgn X kX.
      apply/run_fail/IH/kX => /=.
        by rewrite fA is_ko_failed//if_same.
      rewrite (is_ko_next_alt _ kX)/=nA; case: ifP => dA//.
      by rewrite is_dead_next_alt in nA.
    + move=> s1 A fA nA sIgn X kX.
      rewrite is_dead_dead.
      apply: run_dead => /=.
        by rewrite fA is_ko_failed// if_same.
      by rewrite is_ko_next_alt//=nA if_same.
  Qed.

  Lemma run_or_ko_right2 {s2 X X' A A' SOL sIgn}:
    is_ko X -> run u p s2 (Or A sIgn X) SOL (Or A' sIgn X') false ->
      Texists b1, run u p s2 A SOL A' b1 /\ X' = if is_dead A' then dead X else if b1 == false then X else cutr X.
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember (Or A' _ _) as o2 eqn:Ho2 => + H.
    elim: H A X A' X' Ho1 Ho2; clear.
    + move=> s  _ A _ + <-<- A1 B1 A2 B2 ? + kB'; subst => /=.
      rewrite (is_ko_success kB') (is_ko_next_alt _ kB').
      case: ifP =>// dA1 sB1.
      rewrite (is_ko_next_alt _ kB')/=.
      case X: next_alt => //=[B1'|][??]; subst.
        repeat eexists.
          apply: run_done sB1 erefl _.
          by rewrite X.
        by rewrite (next_alt_dead X)//.
      repeat eexists.
      apply: run_done sB1 erefl _.
        rewrite X//.
      rewrite is_dead_dead//.
    - move=> s1 s2 r A B n + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      by case: ifP => dC; case X: step => [[]]//.
    - move=> s1 s2 r A B n + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_step _ _ _ kA1)//=.
      case: ifP => dC//.
      case X: step => [[]D']//[?]; subst;
      have := IH _ _ _ _ erefl erefl.
        move=> /(_ kA1) [b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_step X IH.
      move=> /(_ is_ko_cutr)[b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_cut X IH.
      rewrite cutr2 if_same dead_cutr.
      by rewrite (run_or0 HB)//.
    - move=> s1 s2 A B r n ++ rB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_next_alt _ kA1). 
      case: ifP => //=dA H1.
      case X: next_alt => [A2'|]//=[?]; subst.
      have [b[{}IH ?]] := IH _ _ _ _ erefl erefl kA1; subst.
      repeat eexists; apply: run_fail H1 X IH.
    - move=> s1 ? ++ A X A' X' ? + kX; subst => /= ++[??]; subst.
      rewrite is_ko_failed//.
      case: ifP => dA H; rewrite (is_ko_next_alt _ kX).
        rewrite //is_dead_dead; repeat eexists.
        apply: run_dead (is_dead_failed dA) (is_dead_next_alt _ dA).
      case W: next_alt => //= _.
      repeat eexists.
      apply: run_dead H W.
      rewrite is_dead_dead//.
  Qed.

  Definition build_or_state cn A' X :=
    if cn == false then 
      if is_dead A' then 
        if next_alt false X is Some X' then X'
        else dead X
      else X
    else if is_dead A' then dead X else cutr X.

  Lemma run_none_dead_res {s A B cn} :
    run u p s A None B cn -> dead B = B.
  Proof.
    move=> H.
    remember None as n eqn:Hn.
    by elim: H Hn; clear => // _ B fB; rewrite dead2.
  Qed.

  Lemma run_or_correct_left {s1 A A' s2 b}:
    run u p s1 A s2 A' b ->
        if s2 is None then
          if b == false then (
            forall sX X s3 X' n1, run u p sX X s3 X' n1 ->
            if is_dead A then 
              (run u p s1 (Or A sX X) s3 (Or (get_dead A X') sX X') false)%type2
            else
            (run u p s1 (Or A sX X) s3 (Or A' sX X') false))%type2
          else
            (
              forall sX X,
                run u p s1 (Or A sX X) None (Or A' sX (dead X)) false
            )
        else forall sX X, run u p s1 (Or A sX X) s2 (Or A' sX (build_or_state b A' X)) false
          .
  Proof.
    rewrite/build_or_state.
    move=> H; elim: H; clear => //.
    + move=> s _ A _ sA <-<- sX X; subst => /=.
      apply: run_done; rewrite /=?(success_is_dead sA)//.
      case W: next_alt => //=[B'|].
        by rewrite (next_alt_dead W)//=.
      rewrite is_dead_dead.
      by case X: next_alt => //.
    + move=> s1 s2 r A B n HA HB.
      case: s2 HB => //= [s2|] HB/=.
        move=> + sX X.
        move=> /(_ sX (cutr X)); rewrite next_alt_cutr cutr2 if_same dead_cutr.
        apply: run_step => /=.
        rewrite HA.
        case: ifP => //dA.
        by rewrite is_dead_step in HA.
      case:eqP => H; subst.
        move=> IH sX X.
        apply: run_step.
          rewrite/= HA; case: ifP => // dA.
          by rewrite is_dead_step in HA.
        have:= run_or_ko_right1 sX (@is_ko_cutr X) HB.
        rewrite /= -(run_none_dead_res HB) is_dead_dead dead_cutr//.
      move=> IH sX X.
      apply: run_step.
        rewrite/= HA; case: ifP => // dA.
        by rewrite is_dead_step in HA.
      have:= run_or_ko_right1 sX (@is_ko_cutr X) HB.
      rewrite cutr2 if_same dead_cutr.
      rewrite /= -(run_none_dead_res HB) is_dead_dead//.
    + move=> s1 s3 r A B n HA _.
      case: s3 => //[s3|].
        move=> + sX X.
        move=> /(_ sX X).
        apply: run_step => /=.
        rewrite HA.
        case: ifP => //dA.
        by rewrite is_dead_step in HA.
      case:eqP => H; subst.
        move=> IH.
        move=> sX X s3 X' n1 H.
        rewrite/get_dead/=.
        case: ifP => dA.
          by rewrite is_dead_step in HA.
        apply: run_step.
          rewrite/= HA dA//.
        by have:= IH _ _ _ _ _ H; rewrite (step_not_dead dA HA).
      move=> IH sX X.
      apply: run_step.
        rewrite/= HA; case: ifP => // dA.
        by rewrite is_dead_step in HA.
      by apply: IH.
    + move=> s1 s2 A B r n fA nA _.
      case: s2 => //[s2|] IH; auto.
        move=> sX X.
        apply: run_fail; rewrite /=?(next_alt_dead nA)//.
        rewrite nA//.
      move: IH.
      case:eqP => //Hn; subst.
        rewrite  !(next_alt_dead nA)//.
        move=> IH.
        move=> sX X s3 X' n1 H.
        apply: run_fail => /=.
          rewrite  !(next_alt_dead nA)//.
        rewrite !(next_alt_dead nA) nA//.
        apply: IH H.
      move=> IH sX X.
      apply: run_fail => /=.
        rewrite  !(next_alt_dead nA)//.
        rewrite  !(next_alt_dead nA) nA//.
      apply: IH.
    + move=> s1 B fB nB/=sX X s3 X' n1 H.
      rewrite /get_dead.
      case: ifP => dB.
        rewrite dB/=.
        have:= run_ko_left2 s1 (is_dead_is_ko dB) H.
        rewrite/get_dead dB/=//.
      inversion H; subst; clear H.
      - apply: run_fail => /=.
          rewrite dB//.
          rewrite dB nB //=next_alt_not_failed//success_failed//.
        apply: run_done; rewrite /= is_dead_dead//.
        rewrite //?is_dead_dead//.
        case W: next_alt => //=.
        rewrite dead2//.
      - apply: run_fail => /=.
          rewrite dB//.
          rewrite dB nB next_alt_not_failed//=.
          by rewrite (step_not_failed H0).
        apply: run_step => //=.
          rewrite H0 is_dead_dead//.
        have:= run_ko_left2 s1 (is_dead_is_ko (@is_dead_dead B)) X0 .
        by rewrite /get_dead is_dead_dead dead2 if_same.
      - apply: run_fail => /=.
          rewrite dB//.
          rewrite dB nB next_alt_not_failed//=.
          by rewrite (step_not_failed H0).
        apply: run_step => //=.
          rewrite H0 is_dead_dead//.
        have:= run_ko_left2 s1 (is_dead_is_ko (@is_dead_dead B)) X0 .
        by rewrite /get_dead is_dead_dead dead2 if_same.
      - apply: run_fail => /=.
          rewrite dB//.
          rewrite dB nB H1//.
        have:= run_ko_left2 s1 (is_dead_is_ko (@is_dead_dead B)) X0.
        by rewrite /get_dead is_dead_dead dead2 if_same.
      - rewrite -/(dead (Or B sX X)).
        by apply: run_dead; rewrite /=dB// nB H1.
  Qed.

  Lemma run_or_complete {s1 s2 A B s3 A' B'}:
    run u p s1 (Or A s2 B) s3 (Or A' s2 B') false ->
      (Texists n1,
        if s3 is Some s3 then
          ((run u p s1 A (Some s3) A' n1 /\ B' = build_or_state n1 A' B)%type2
          +
          (if is_dead A then 
              A' = get_dead A B' /\
              run u p s1 A None (dead A') false /\ run u p s2 B (Some s3) B' n1
           else (A' = dead A') /\ run u p s1 A None A' false
              /\ run u p s2 B (Some s3) B' n1)%type2)%type
        else
          run u p s1 A None A' n1 /\ (if n1 == false then Texists n2, 
            run u p s2 B None B' n2 else B' = dead B) /\ A' = dead A' 
              /\ B' = dead B'
          ).
  Proof.
    rewrite/build_or_state.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember false as z eqn:Hz.
    remember (Or A' _ _) as o2 eqn:Ho2 => H.
    elim: H s2 A B A' B' Ho1 Ho2 Hz => //=; clear.
    + move=> s1 _ A _ + <-<- s3 A1 B1 A2 B2 ? + _; subst => /=.
      case: ifP => [dA1 sB1|dA sA1].
        case nB1: next_alt => [B1'|]//=[??]; subst.
          rewrite next_alt_not_failed//?success_failed//=if_same dA1.
          eexists; right; repeat split; auto.
            rewrite/get_dead dA1 (next_alt_dead nB1)//=.
            apply: run_dead (is_dead_failed dA1) (is_dead_next_alt _ dA1).
          apply: run_done => //.
          by rewrite nB1//.
        eexists; right; rewrite dead2; repeat split; auto.
          rewrite/get_dead dA1 is_dead_dead//.
          apply: run_dead (is_dead_failed dA1) (is_dead_next_alt _ dA1).
        apply: run_done => //.
        rewrite nB1//.
      case nA1 : next_alt => [A1'|]//=.
        move=>[??]; subst.
        rewrite (next_alt_dead nA1).
        eexists;left; split.
          apply: run_done => //=.
          rewrite nA1//.
        move=> //.
      case nB1: next_alt => //[B1'|][??]; subst; eexists; rewrite is_dead_dead dead2; left.
        split.
          apply: run_done => //=.
          rewrite nA1//.
        move=> //.
      split.
        apply: run_done => //.
        rewrite nA1//.
      move=> //.
    + move=> s1 s3 r A B n + HB IH s4 A1 A2 B1 B2 ???; subst => //=.
      case: ifP => dA1.
        case X: step => [[]B'']//[?]; subst; have {IH}[n1+] := IH _ _ _ _ _ erefl erefl erefl.
          case: s3 HB => [s3|] HB//.
            move=> [].
              move=>[H1 ?]; subst.
              by have [] := run_dead1 dA1 H1.
            rewrite dA1 => -[?[H1 H2]]; subst.
            have [_[H3 _]] := run_dead1 dA1 H1.
            eexists; right; repeat split; auto.
            apply: run_step X H2.
          move=> [H1[+[H3 H4]]]; subst.
          case:eqP => H5; subst.
            move=> [n2 H5].
            repeat eexists; eauto => /=.
            repeat eexists.
            apply: run_step X H5.
          move=> ?; subst; rewrite dead2.
          repeat eexists; eauto.
          case: eqP => //.
          by have [_[??]] := run_dead1 dA1 H1; subst.
        case: s3 HB => [s3|] HB//.
          move=> [].
            move=> [H1 ?]; subst.
            eexists; left; split.
              apply: H1.
            by have []:= run_dead1 dA1 H1.
          rewrite dA1 => -[?[H1 H2]]; subst.
          eexists; right; repeat split; auto.
          apply: run_cut X H2.
        move=> [H1[H2[H3 H4]]]; subst.
        repeat eexists; eauto; move:H2; case:eqP => H; subst.
          move=> [n2 H].
          eexists; apply: run_cut X H.
        move=> ?; subst.
        by have [_[??]] := run_dead1 dA1 H1; subst.
      case X: step => [[]D']//[?]; subst; have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
        case: s3 HB => [s3|] HB//.
          move=> [].
            move=> [H1?]; subst.
            eexists; left; split.
              apply: run_step X H1.
            by move=> //.
          rewrite (step_not_dead dA1 X) => -[Hz [H1 H2]].
          eexists; right; repeat split; eauto.
          apply: run_step X H1.
        move=> [H1[H2[H3 H4]]]; subst.
        repeat eexists; eauto.
        apply: run_step X H1.
      case: s3 HB => [s3|] HB//.
        move=> [].
          move=> [H1 ?]; subst.
          eexists; left; split.
            apply: run_cut X H1.
          by rewrite next_alt_cutr/= cutr2 if_same dead_cutr.
        rewrite (step_not_dead dA1 X) => -[Hz [H1 H2]].
        by have [] := run_consistent H2 (is_ko_run _ _ _ is_ko_cutr).
      move=> [H1[H2[H3 H4]]]; subst.
      move: H2; case:eqP => H; subst.
        move=>[n2]/(run_consistent (is_ko_run _ _ _ is_ko_cutr)) [?[??]]; subst.
        rewrite dead2 dead_cutr.
        repeat eexists; eauto.
          apply: run_cut X H1.
        by [].
      move=> ?; subst.
      rewrite dead2 dead_cutr; eexists; repeat split; auto.
        apply: run_cut X H1.
      move=> //=.
    + move=> s1 r A B C n ++ rB IH s2 A1 B1 A2 B2 ???; subst.
      move=> /=; case: ifP => [dA fB|dA fA].
        case X: next_alt => //[B1'][?]; subst.
        have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
        case: r rB => //[s3|] rB.
          move=> [].
            move=> [H1 ?]; subst.
            by have [] := run_dead1 dA H1.
          rewrite dA => -[?[H1 H2]]; subst.
          eexists; right; repeat split; auto.
          apply: run_fail fB X H2.
        move=> [H1 [H2[H3 H4]]]; subst.
        case: n1 H1 H2 => //=[|n1] H1; last first.
          move: H1.
          move=> [n2 H]; repeat eexists; eauto.
          move=> /=; eexists; apply: run_fail fB X H.
        by have [_[??]] := run_dead1 dA H1; subst.
      case nA1 : next_alt => [A1'|]//.
        move=> [?]; subst.
        have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
        case: r rB => //[s3|] rB.
          move=> [].
            move=> [H1 ?]; subst.
            eexists; left; split; eauto.
            apply: run_fail fA nA1 H1.
          rewrite (next_alt_dead nA1)/=.
          move=> [Hx [H1 H2]].
          eexists; right; repeat split; eauto.
          apply: run_fail fA nA1 H1.
        move=> [H1 [H2[H3 H4]]]; subst.
        case: n1 H1 H2 => //= H1; last first.
          move=> [n2 H]; repeat eexists; eauto.
            apply: run_fail fA nA1 H1.
          by eexists; eauto.
        move=> ?; subst; repeat eexists => //.
          apply: run_fail fA nA1 H1.
        by [].
      case nB1: next_alt => [B1'|]//=[?]; subst.
      have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
      case: r rB => //[s3|] rB.
        move=> [].
          move=>[H1 ?]; subst.
          by have [] := run_dead2 H1.
        rewrite is_dead_dead.
        move=> [?[H1 H2]]; subst.
        eexists; right; repeat split; eauto.
          rewrite/get_dead is_dead_dead/= dead2 if_same dead2//.
          rewrite/get_dead dead2 if_same.
          rewrite/get_dead dead2 if_same dead2 in H1.
          apply: next_alt_run nA1 H1.
        apply: next_alt_run nB1 H2.
      move=> [H1 [H2[H3 H4]]]; subst.
      case: n1 H1 H2 => //= H1; last first.
        have [_[? _]]:= run_dead2 H1; subst.
        move=> [n2 H]; repeat eexists; eauto.
          apply: run_dead fA nA1.
        by eexists; apply: next_alt_run; eauto.
      move=> ?; subst; repeat eexists => //.
        have [_[? _]]:= run_dead2 H1; subst.
        apply: run_dead fA nA1.
      by have [?[]]:= run_dead2 H1.
    + move=> s1 B ++ s2 A1 B1 A2 B2 ? + _; subst => /=.
      case:ifP => [dA1 fB1|dA1 fA1].
        case nB1: next_alt => // _ [<-{A2}<-{B2}].
        repeat eexists; rewrite?dead2//.
          apply: run_dead (is_dead_failed dA1) _.
          by rewrite is_dead_next_alt.
        eexists; apply: run_dead fB1 nB1.
      case nA1: next_alt => [A1'|]//=.
      case nB1: next_alt => // _ [<-<-{A2 B2}].
      repeat eexists; rewrite ?dead2//.
        apply: run_dead fA1 nA1.
      eexists.
      case X: (failed B1).
        apply: run_dead X nB1.
      by rewrite next_alt_not_failed in nB1.
  Qed.

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> run u p sIgn1 (Or A s B) s2 D b2 ->
      run u p sIgn2 (Or A s B) s2 D false.
  Proof.
    move=> H1 H2.
    have:= run_same_structure H2.
    case: D H2 => //= A' s' B' + /eqP?; subst.
    move=> /[dup] /run_or0-> /(run_ko_left1 H1) [b'][H2 -> {A'}].
    apply: run_ko_left2 H1 H2.
  Qed.

  Lemma failed_cutl_run A:
    failed (cutl A) -> forall s, run u p s (cutl A) None (dead A) false.
  Proof.
    Search failed cutl.
    elim: A => //=; try by move=> *; apply: run_dead => //.
    - move=> A HA s B HB + s1; case: ifP => dA/=; rewrite ?is_dead_cutl dA => F.
        have {}HB := HB F s.
        have := run_ko_left2 s1 (is_dead_is_ko dA) HB; eauto.
        rewrite/get_dead is_dead_dead andbF//.
      have {}HA := HA F s1.
      have /= := run_or_ko_right1 s (@is_ko_cutr B) HA.
      by rewrite is_dead_dead dead_cutr.
    - move=> A HA B0 B HB.
      case:ifP => //= sA.
        rewrite failed_success_cut success_cut sA/=.
        move=> fB s.
        have {}HB := HB fB (get_substS s A).
        inversion HB; clear HB; subst => //.
        - by rewrite failed_step// in H.
        - by rewrite next_alt_cutl_failed// in H0.
        - admit.
         (* rewrite dead_cutl -/(dead (And A B0 B)) -/(cutl (And A B0 B)) -dead_cutl. *)
          (* replace (And _ _ _) with (cutl (And A B0 B)); last by rewrite /=sA.
          rewrite -/(dead (And A B0 B)).
          suffices : dead (And A B0 B) = dead (cutl (And A B0 B)).
            move=> ->.
            apply: run_dead; rewrite/= sA/= success_cut sA ?fB?orbT// H3 next_alt_cutl/=.
            by destruct B0.
          move=> /=; rewrite sA/= .
          move: sA fB H; clear => /=.
          elim: 
          rewrite !next_alt_cutl/= failed_success_cut success_cut sA/= H3//. *)
      move=> _ s.
      have:= (HA _ s).
      rewrite failed_success_cut success_cut sA/=.
      move=> /(_ isT) {}HA; inversion HA; clear HA; subst.
      - rewrite failed_step//failed_success_cut success_cut sA// in H.
      - rewrite next_alt_cutl_failed// in H0.
      (* - rewrite dead_cutl -/(dead (And A B0 B)) -/(cutl (And A B0 B)) -dead_cutl.
        replace (And _ _ _) with (cutl (And A B0 B)); last first.
          rewrite/= sA//=.
        apply: run_dead; rewrite/= sA/= failed_cutr//.
        by rewrite next_alt_cutr. *)
      admit.
  Abort.

  Lemma run_and_correct_successL {s0 sn A B0 B A' B0' B' b}:
    success A -> next_alt true A = None ->
    run u p s0 (And A B0 B) sn (And A' B0' B') b ->
    (run u p (get_substS s0 A) B sn B' b /\ 
      (B0' = B0) /\
      (A' = if is_dead B' then dead A else if b == false then A else cutl A)
    )%type2.
  Proof.
    (* remember (And A _ _) as a eqn:Ha.
    remember (And A' _ _) as a' eqn:Ha' => ++H.
    elim: H A B0 B Ha A' B0' B' Ha'; clear => //=.
    - move=> s1 _ A _ + <-<- A1 B01 B1 ? A2 B02 B2; subst => /=/andP[sA1 sB1].
      rewrite success_failed//sA1.
      case nB1: next_alt => [B1'|]//=.
        destruct B01.
        move=> [???] _ nA2; subst.
        rewrite (next_alt_dead nB1); repeat split.
        apply: run_done sB1 erefl _.
        by rewrite nB1//.
      destruct B01.
      case nA1: next_alt => //=-[???] _ _; subst.
      rewrite success_is_dead//=.
      repeat split.
      (* rewrite is_dead_dead; repeat split. *)
      apply: run_done => //.
      rewrite nB1//=.
    - move=> s1 s3 r A B n + _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= + sA1 nA1.
      rewrite succes_step//=.
      case eA1: step => //[B1'][?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl.
      rewrite next_alt_cutl success_cut => /(_ sA1 erefl).
      rewrite ges_subst_cutl// cutl2 if_same dead_cutl.
      move=> [rB1'[??]]; subst.
      rewrite cutr2 dead_cutr !if_same.
      repeat split.
      apply: run_cut eA1 rB1'.
    - move=> s1 s3 r A B n + _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= + sA1 nA1.
      rewrite succes_step//=.
      case eA1: step => //[B1'][?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl.
      move => /(_ sA1 nA1).
      move=> [rB1' [??]]; subst.
      by repeat eexists; eauto; apply: run_step eA1 rB1'.
    - move=> s1 s2 A A' r n ++ _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= ++ sA1 nA1.
      rewrite success_failed//= sA1/= nA1.
      case X: next_alt => //[B1'] fB1 [?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl sA1 nA1.
      move=> [rB1' [??]]; subst.
      repeat split.
      by apply: run_fail; eauto.
    - move=> s1 B + + A1 B01 B1 ? A2 B02 B2 + sA1 nA1; subst => /=.
      rewrite success_failed// sA1/= nA1 => ++[???]; subst.
      case X: next_alt => // fB1 _.
      rewrite is_dead_dead; repeat split.
      apply: run_dead fB1 X. *)
  Abort.

  Lemma run_big_and_total {r s}:
      Texists r0 B n, run u p s ((big_and r)) r0 B n.
  Proof.
    elim: r s => //=.
    - move=> s; repeat eexists; apply: run_done => //.
    - move=> x xs IH s.
      admit.
  Admitted.

  Lemma run_big_or_total {sr r rs c s}:
    F u p c s = (sr, r) :: rs -> 
      Texists r0 B n, run u p s (TA (call c)) r0 B n.
  Proof.
    elim: rs sr r c s => //=.
    - move=> sr r c s H.
      have [r0[B [n H1]]] := @run_big_and_total (premises r) sr.
      repeat eexists.
      apply: run_step; rewrite /=/big_or?H//.
      apply: run_fail => //=.
        rewrite next_alt_big_and//.
      by apply: run_ko_left2; eauto.
    - move=> [sx r] rs IH sr r' c s H.
  Abort.

  Lemma run_is_total {s A}:
    Texists r B n, run u p s A r B n.
  Proof.
    elim: A s.
    - repeat eexists; apply: run_dead => //.
    - repeat eexists; apply: run_done => //.
    - repeat eexists; apply: run_dead => //.
    - move=> c s.
      (* case F: (F u p c s) => [|[sr r] rs].
        repeat eexists.
        apply: run_step => //.
        rewrite/big_or F; apply: run_dead => //.
      repeat eexists.
      apply: run_step => //=.
      rewrite/big_or; rewrite F.
      apply: run_fail => //=.
      admit. *)
    (* - repeat eexists; apply: run_cut => //; apply: run_done => //. *)
    (* - admit. *)
    (* - admit. *)
  Abort.

  (*Lemma run_and_correct {s0 sn A B0 B A' B0' B' b}:
    run u s0 (And A B0 B) sn (And A' B0' B') b ->
    if sn is Some sn then true :> Type
    else (
      run u s0 A None A' b + 
      (Texists s0', run u s0 A (Some s0') )
    
    ).
(*     true
    (Texists sm r1 b1, run u s0 A sm r1 b1 /\
      Texists b2 r2, ((run u sm B sn r2 b2) + 
        (* TODO: it should not be Texsists sm, but I should provide the right substitution *)
        (* The problem is given by a state like (A \/ B) /\ C
           A succeeds, C fails, the substitution on which we should run C0
           is the one obtained by running B (i.e. next_alt A).
        *)
        (Texists sm, run u sm B0 sn r2 b2))). *)
  Proof.
    remember (And _ _ _) as a eqn:Ha => H.
    elim: H A B0 B Ha; clear.
    - move=> s1 s2 r A B /step_solved_same [[??]+] ? C D E ?; subst => /=.
      move=> /andP[sC sE].
      repeat eexists.
        apply: run_done (succes_step _ _ sC) erefl.
      rewrite sC; left; apply: run_done erefl.
      apply: succes_step sE.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: step => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_cut X IH.
      case Y: step => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= step_solved_same _ X; subst.
      have sC' := sC.
        rewrite -success_cut in sC'.
      have {IH} [?[??]] := run_consistent _ _ IH (run_success1 _ _ sC'); subst.
      rewrite ges_subst_cutl in H2.
      case: H2 => H2.
        by repeat eexists; left; apply: run_cut Y H2.
      move: H2 => [sm H2].
      case sD: (success (cutl D)).
        have [?[??]] := run_consistent _ _ H2 (run_success1 _ _ sD); subst.
        repeat eexists; right.
        rewrite success_cut in sD.
        rewrite ges_subst_cutl.
        eexists; apply: run_success1 sD.
      have:= @failed_success_cut D.
      rewrite sD/= => H1.
      by have:= failed_cutl_run _ H1 _ _ _ _ H2.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: step => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_step X IH.
      case Y: step => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= step_solved_same _ X; subst.
      have {IH} [?[??]] := run_consistent _ _ IH (run_success1 _ _ sC); subst.
      case: H2 => H2.
        repeat eexists; left; apply: run_step Y H2.
      by repeat eexists; eauto.
    - move=> s1 s2 A B C r n /step_failed_same [? +] + rC IH D E F ?; subst.
      move=> /= /orPT[fD|/andP[sD fF]].
        rewrite fD; case: ifP => //dD.
        case W: next_alt => //=[D'].
        case X: next_alt => //=[E'][?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split.
          apply: run_fail (failed_step _ fD) W IH.
        case: H2 => H2; repeat eexists; eauto.
        right; eexists; apply: next_alt_run X H2.
      rewrite success_failed// success_is_dead//sD.
      case W: next_alt => //=[F'|].
        move=>[?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split; eauto.
        case: H2 => H2; repeat eexists; eauto.
        left; apply: next_alt_run W H2.
      case X: next_alt => //=[D'].
      case Y: next_alt => //=[E'][?]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done erefl.
        apply: succes_step sD.
      case: H2 => H2; repeat eexists.
        right; eexists; apply: next_alt_run Y _.
        eauto.
      repeat eexists; right; eauto.
  Qed. *)
End s.
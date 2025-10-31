From mathcomp Require Import all_ssreflect.
From det Require Import run run_prop.
From det Require Import zify_ssreflect.

Section s.
  Variable u : Unif.

  (* Lemma next_alt_exp_same {s A r}:
    expand u s A = r -> is_fail r = false -> is_solved r = false ->
      next_alt false A = Some A.
  Proof.
    move=> <-; elim: A s {r} => //=.
    - move=> A HA s B HB s1.
      case: ifP => dA.
        have:= HB s; case: expand => //=s' B'/(_ erefl)->//.
      have:= HA s1; case: expand => //= _ _ /(_ erefl)->//.
    - move=> A HA B0 _ B HB s; case: ifP => dA.
        rewrite is_dead_expand//.
      have:= HA s; case X: expand => //=[s' A'|s' A'|s' A'] /(_ erefl).
        move=> /(_ erefl)->; rewrite (expand_not_failed _ X notF) (expand_not_solved_not_success _ X notF)//.
        move=> /(_ erefl)->; rewrite (expand_not_failed _ X notF) (expand_not_solved_not_success _ X notF)//.
      have [[??]sA] := expand_solved_same _ X; subst.
      rewrite sA success_failed//.
      have:= HB (get_substS s A').
      case Y: expand => //=[s'' B'|s'' B'] /(_ erefl erefl) ->//.
  Qed. *)


  Lemma runb_success1 {A} s: 
    success A -> runb u s A (Some (get_substS s A)) (build_na A (next_alt true A)) 0.
  Proof.
    move=> sA.
    apply: run_done.
    apply: succes_is_solved sA.
    move=> //.
  Qed.

  Lemma runb_success {A s1 s2 r n}: 
    success A -> runb u s1 A s2 r n -> (s2 = Some (get_substS s1 A) /\ r = build_na A (next_alt true A) /\ n = 0)%type2.
  Proof.
    move=> sA H; have:= succes_is_solved u s1 sA.
    inversion H; clear H; try congruence; subst.
    - by rewrite H0 => -[??]; subst.
    - by rewrite failed_success in sA.
    - by rewrite failed_success in sA.
  Qed.

  Lemma run_consistent {s A s1 B s2 C n1 n2}:
    runb u s A s1 B n1 -> runb u s A s2 C n2 -> ((s2 = s1) /\ (C = B) /\ (n2 = n1))%type2.
  Proof.
    move=> H; elim: H s2 C n2; clear.
    + move=> s1 s2 r A B HA ? s3 C n2 H; subst.
      have [[??]sA]:= expand_solved_same _ HA; subst.
      by apply: runb_success sA H.
    + move=> s1 s2 s3 r n1 A B HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - move: H0; rewrite HA => -[??]; subst; by rewrite !(IH _ _ _ H1)//.
      - by rewrite failed_expand in HA.
      - by rewrite failed_expand in HA.
    + move=> s1 s2 s3 r n1 A B HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - move: H0; rewrite HA => -[??]; subst; by rewrite !(IH _ _ _ H1)//.
      - by rewrite failed_expand in HA.
      - by rewrite failed_expand in HA.
    + move=> s1 s2 A B r n1 fA nB rB IH s3 C n2 H.
      inversion H; clear H; try congruence; subst; try by rewrite failed_expand in H0.
      move: H1; rewrite nB => -[?]; subst.
      by apply: IH.
    + move=> s1 A fA nA s2 C n2 H.
      inversion H; subst; try congruence; try rewrite //failed_expand// in H0.
  Qed.

  Lemma is_ko_runb {s A}: is_ko A -> runb u s A None (dead1 A) 0.
  Proof.
    elim: A s => //=.
    - by move=> s _; apply: run_dead => //=.
    - move=> s _; apply: run_dead => //=.
    - move=> A HA s B HB s2 /andP[kA kB].
      have {}HA := HA s2 kA.
      have {}HB := HB s2 kB.
      apply: run_dead; rewrite/=.
        by rewrite !is_ko_failed//if_same.
      by rewrite !is_ko_next_alt// !if_same.
    - move=> A HA B0 HB0 B HB s kA.
      have {HB}HA := HA s kA.
      apply: run_dead => /=.
        by rewrite is_ko_failed.
      by rewrite (is_ko_next_alt _ kA)// is_ko_failed//=if_same.
  Qed.

  Lemma runb_or0 {s1 A s B s2 r b}:
    runb u s1 (Or A s B) s2 r b -> b = 0.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s B Ho; clear => //.
    - move=> s1 s2 s3 r A B n + _ _ C s D ?; subst => /=.
      by case: ifP; case: expand => //.
    - move=> s1 s2 s3 r A B n + HB IH C s D ?; subst => /=.
      case: ifP => dC.
        case X: expand => //[s' D'|s' D'][??]; subst; by apply: IH.
      case Y: expand=> //[s1' C'|s1' C'][??]; subst; by apply: IH.
    - move=> s1 s2 A B r n _ + H IH C s3 D ?; subst => /=.
      case: ifP => //= _.
        case: next_alt => //= ? [/esym]; apply IH.
      case: next_alt => //=.
        move=>? [/esym]; apply IH.
      case: ifP => // _.
      case: next_alt => //= ? [/esym]; apply IH.
  Qed.

  Lemma next_alt_not_failed A:
    (failed A) = false -> next_alt false A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA fB.
        rewrite HB//=.
      rewrite HA//.
    - move=> A HA B0 _ B HB.
      case: ifP => dA.
        rewrite is_dead_failed//.
      case: ifP => //=fA.
      case: ifP => //=sA fB.
      rewrite HB//.
  Qed.

  Lemma next_alt_runb {A B C s s2 b1}:
    next_alt false A = B ->
      runb u s (build_na A B) s2 C b1 ->
        runb u s A s2 C b1.
  Proof.
    move=> <-{B}.
    case fA: (failed A).
      case X: next_alt => [A'|]/= H.
        apply: run_fail fA X H.
      have [->[->->]]:= run_dead2 _ H.
      apply: run_dead fA X.
    rewrite next_alt_not_failed//.
  Qed.

  Definition get_dead A B := if is_dead A && ~~(is_dead B) then A else dead1 A.

  Lemma run_ko_left1 {s1 s2 A B A' B' sx}:
    is_ko A -> runb u s1 (Or A s2 B) sx (Or A' s2 B') 0 ->
      Texists b, runb u s2 B sx B' b /\ 
        (A' = get_dead A B').
  Proof.
    rewrite/get_dead.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember (Or A' _ _) as o2 eqn:Ho2 => + H.
    elim: H A B A' B' s2 Ho1 Ho2; clear.
    + move=> s s' A B _ + <-  A1 B1 A2 B2 s2 ? + kA'; subst.
      move=> /expand_solved_same [[??]+]; subst => /=.
      rewrite (is_ko_success kA') (is_ko_next_alt _ kA').
      case: ifP =>// dA1 sB1.
      case X: next_alt => //=[B1'|] [??]; subst.
        repeat eexists.
          apply: run_done.
            apply: succes_is_solved sB1.
          by rewrite X.
        rewrite (next_alt_dead X)//.
      repeat eexists.
      apply: run_done.
        apply: succes_is_solved sB1.
        rewrite X => //.
      rewrite is_dead_dead//.
    - move=> s1 s2 s3 r A B n + HB IH A1 A2 B1 B2 s4 ?? kA1; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 s3 r A B n + HB IH A1 A2 B1 B2 s4 ?? kA1; subst => /=.
      rewrite (is_ko_expand _ kA1)//.
      case: ifP => dC//.
      case X: expand => //[s4' D'|s4' D'][??]; subst;
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
        case: ifP => // dA2.
        case X: next_alt => //[A2'][?]; subst.
        have [b[H3]]:= IH _ _ _ _ _ erefl erefl (is_dead_is_ko is_dead_dead).
        rewrite is_dead_dead dead2 if_same => ?; subst.
        repeat eexists.
        apply: next_alt_runb X H3.
    - move=> _ A + + B1 C1 B2 C2 s ?/= + kB1; subst => /=++[??]; subst.
      rewrite (is_ko_next_alt _ kB1).
      rewrite is_dead_dead /= andbF.
      case: ifP => dB1 F.
        case X: next_alt => [C1'|]// _.
        repeat eexists; apply: run_dead F X.
      case: ifP => dC1.
        repeat eexists; apply: run_dead.
          apply: is_dead_failed dC1.
        rewrite is_dead_next_alt//.
      case X: next_alt => // _.
      repeat eexists.
      case fC1: (failed C1).
        apply: run_dead fC1 X.
      by rewrite next_alt_not_failed in X.
  Qed.

  Lemma run_ko_left2 {s2 X B B' r b1} sIgn:
    is_ko X -> runb u s2 B r B' b1 ->
    runb u sIgn (Or X s2 B) r (Or (get_dead X B') s2 B') 0.
  Proof.
    rewrite/get_dead.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s s' r A B /expand_solved_same [[??]sB] ? sIgn X kX; subst => /=.
      case dX: (is_dead X) => /=.
        apply: run_done.
          by rewrite/= (succes_is_solved _ _ sB) is_ko_expand// dX.
        rewrite/=dX; case Y: next_alt => //=[A'|].
          by rewrite (next_alt_dead Y)//.
        by rewrite is_dead_dead//.
      apply: run_fail => /=.
        by rewrite dX is_ko_failed.
        by rewrite/= dX is_ko_next_alt// success_is_dead// next_alt_not_failed// success_failed//.
      apply: run_done.
        rewrite/= (succes_is_solved _ _ sB) is_dead_dead//.
      by rewrite /=is_dead_dead//; case: next_alt => //=; rewrite dead2//.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X) => /=.
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step IH.
        by rewrite /= dX HA//.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead dead2 if_same in IH.
      have fA := expand_not_failed _ HA notF.
      apply: run_fail.
        rewrite/=dX is_ko_failed//.
        by rewrite /= dX is_ko_next_alt// next_alt_not_failed//=failed_dead.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    (* TODO: the following case is same as previous... *)
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X) => /=.
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step IH.
        by rewrite /= dX HA//.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead dead2 if_same in IH.
      have fA := expand_not_failed _ HA notF.
      apply: run_fail.
        rewrite/=dX is_ko_failed//.
        by rewrite /= dX is_ko_next_alt// next_alt_not_failed//=failed_dead.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    + move=> s1 s2 A B r n fA nB rC IH sIgn X kX; subst.
      case dX: (is_dead X).
        have {}IH:= IH sIgn _ kX.
        rewrite dX/= in IH; subst.
        by apply: run_fail IH; rewrite /=dX//nB//.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead/=dead2 if_same in IH; subst.
      apply: run_fail IH; rewrite/= dX ?is_ko_failed// is_ko_next_alt//nB.
      rewrite (next_alt_dead nB)//.
    + move=> s1 B fB nB sIgn X kX.
      rewrite is_dead_dead andbF.
      apply: run_dead; rewrite/=.
        by rewrite fB is_ko_failed//if_same.
      by rewrite nB is_ko_next_alt// !if_same.
  Qed.

  Lemma run_or_ko_right1 {s2 X B B' SOL b1} sIgn:
    is_ko X -> runb u s2 B SOL B' b1 ->
    runb u s2 (Or B sIgn X) SOL (Or B' sIgn (if is_dead B' then dead1 X else if b1 == 0 then X else cutr X)) 0.
  Proof.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s s' r A B /expand_solved_same [[??]sB] ? sIgn X kX; subst => /=.
      apply: run_done.
        by rewrite/= success_is_dead// succes_is_solved//.
      rewrite/= success_is_dead// (is_ko_next_alt _ kX)// if_same//.
      case W: next_alt => //=[A'|].
        rewrite (next_alt_dead W)//.
      rewrite is_dead_dead//.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      have:= IH sIgn (cutr X) is_ko_cutr.
      rewrite cutr2 if_same dead_cutr//.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      apply: IH => //.
    + move=> s1 s2 A B r n fA nA rB IH sIgn X kX.
      apply: run_fail => /=.
        by rewrite fA is_ko_failed//if_same.
      rewrite (is_ko_next_alt _ kX) nA (next_alt_dead nA)//.
      apply: IH kX.
    + move=> s1 A fA nA sIgn X kX.
      rewrite is_dead_dead.
      apply: run_dead => /=.
        by rewrite fA is_ko_failed// if_same.
      by rewrite is_ko_next_alt//nA !if_same.
  Qed.

  Lemma run_or_ko_right2 {s2 X X' A A' SOL sIgn}:
    is_ko X -> runb u s2 (Or A sIgn X) SOL (Or A' sIgn X') 0 ->
      Texists b1, runb u s2 A SOL A' b1 /\ X' = if is_dead A' then dead1 X else if b1 == 0 then X else cutr X.
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember (Or A' _ _) as o2 eqn:Ho2 => + H.
    elim: H A X A' X' Ho1 Ho2; clear.
    + move=> s s' A B _ + <-  A1 B1 A2 B2 ? + kB'; subst.
      move=> /expand_solved_same [[??]+]; subst => /=.
      rewrite (is_ko_success kB') (is_ko_next_alt _ kB').
      case: ifP =>// dA1 sB1.
      rewrite (is_ko_next_alt _ kB') if_same.
      case X: next_alt => //=[B1'|][??]; subst.
        repeat eexists.
          apply: run_done.
            apply: succes_is_solved sB1.
          by rewrite X.
        by rewrite (next_alt_dead X)//.
      repeat eexists.
      apply: run_done.
        apply: succes_is_solved sB1.
        rewrite X => //.
      rewrite is_dead_dead//.
    - move=> s1 s2 s3 r A B n + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 s3 r A B n + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_expand _ kA1)//=.
      case: ifP => dC//.
      case X: expand => //[s4' D'|s4' D'][??]; subst;
      have := IH _ _ _ _ erefl erefl.
        move=> /(_ kA1) [b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_step X IH.
      move=> /(_ is_ko_cutr)[b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_cut X IH.
      rewrite cutr2 if_same dead_cutr.
      by rewrite (runb_or0 HB)//.
    - move=> s1 s2 A B r n ++ rB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_next_alt _ kA1) if_same.
      case: ifP => //=dA H1.
      case X: next_alt => [A2'|]//=[?]; subst.
      have [b[{}IH ?]] := IH _ _ _ _ erefl erefl kA1; subst.
      repeat eexists; apply: run_fail H1 X IH.
    - move=> s1 ? ++ A X A' X' ? + kX; subst => /= ++[??]; subst.
      rewrite is_ko_failed// is_ko_next_alt//= if_same is_dead_dead.
      case: ifP => //=H1.
        move=> _ _; repeat eexists.
        apply: run_dead.
          rewrite is_dead_failed//.
        rewrite is_dead_next_alt//.
      move=> fA; case W: next_alt => //= _.
      repeat eexists.
      apply: run_dead fA W.
  Qed.

  Definition build_or_state cn A' X :=
    if cn == 0 then 
      if is_dead A' then 
        if next_alt false X is Some X' then X'
        else dead1 X
      else X
    else if is_dead A' then dead1 X else cutr X.

  (* Lemma build_or_state_inj {cn A A1} A2:
    build_or_state cn A A1 ->
      build_or_state cn A A2 -> A1 = A2.
  Proof.
    rewrite/build_or_state.
    case: eqP => [?|???]; subst => //.
    case: r => [???|]; subst => //.
    case: next_alt => [?|??]; subst => //.
    (* TODO: solve this issue by removing the existential and
       add the state in option None in runb *)
    move=> [A1 [dA1 ?]] [A2 [dA2 ?]]; subst.
    repeat f_equal.
  Admitted. *)

  Lemma run_or_correct_left {s1 A A' s2 b}:
    runb u s1 A s2 A' b -> forall sX X,
        if s2 is None then A' = dead1 A'
          (* forall X', runb u s1 (Or A sX X)  <-> runb  *)
        else runb u s1 (Or A sX X) s2 (Or A' sX (build_or_state b A' X)) 0
          .
  Proof.
    rewrite/build_or_state.
    move=> H; elim: H; clear => //.
    + move=> s s' A B r /[dup] /(expand_solved_same) [[??]sA] eA nB sX X; subst => /=.
      apply: run_done => //=.
        by rewrite eA success_is_dead//=.
      rewrite /= success_is_dead//=.
      case W: next_alt => //=[B'|].
        rewrite (next_alt_dead W)//=.
      rewrite is_dead_dead.
      case: ifP => dX.
        rewrite is_dead_next_alt//.
      case X: next_alt => //.
    + move=> s1 s2 s3 r A B n HA _ + sX X/=.
      move=> /(_ sX (cutr X)); rewrite next_alt_cutr dead_cutr cutr2 if_same.
      case: s3 => //s3.
      apply: run_step => /=.
      rewrite HA.
      case: ifP => //dA.
      by rewrite is_dead_expand in HA.
    + move=> s1 s2 s3 r A B n HA _ + sX X/=.
      move=> /(_ sX X).
      case: s3 => //s3.
      apply: run_step => /=.
      rewrite HA.
      case: ifP => //dA.
      by rewrite is_dead_expand in HA.
    + move=> s1 s2 A B r n fA nA _ IH sX X.
      case: s2 IH => //[s2|] IH; auto.
      apply: run_fail; rewrite /=?(next_alt_dead nA)//.
      rewrite nA//.
    + by move=>*; rewrite dead2.
  Qed.

  Lemma run_or_complete {s1 s2 A B s3 A' B'}:
  (* TODO: be more precise on altAB *)
    runb u s1 (Or A s2 B) s3 (Or A' s2 B') 0 ->
      (Texists n1, (
        if s3 is None then
          runb u s1 A None A' n1 /\ (if n1 == 0 then Texists n2, runb u s2 B None B' n2 else B' = dead1 B) /\ A' = dead1 A' /\ B' = dead1 B'
        else
          True)).
        (* (runb u s1 A s3 r' n /\ build_or_state n s2 B r' r)%type2
         + 
        (runb u s2 B s3 r' n))%type). *)
  Proof.
    (* rewrite/build_or_state. *)
    remember (Or A _ _) as o1 eqn:Ho1.
    remember 0 as z eqn:Hz.
    remember (Or A' _ _) as o2 eqn:Ho2 => H.
    elim: H s2 A B A' B' Ho1 Ho2 Hz => //=; clear.
    + move=> s1 s2 s3 r A B n + HB IH s4 A1 A2 B1 B2 ???; subst => //=.
      case: ifP => dA1.
        case X: expand => //[s4' B''|s4' B''][??]; subst; have {IH}[n1+] := IH _ _ _ _ _ erefl erefl erefl.
          case: s3 HB => [s3|] HB//.
          move=> [H1[+[H3 H4]]]; subst.
          case:eqP => H5; subst.
            move=> [n2 H5].
            repeat eexists; eauto => /=.
            repeat eexists.
            apply: run_step X H5.
          move=> ?; subst; rewrite dead2.
          repeat eexists; eauto.
          case: eqP => //.
          by have [_[??]] := run_dead1 _ dA1 H1; subst.
        case: s3 HB => [s3|] HB//.
        move=> [H1[H2[H3 H4]]]; subst.
        repeat eexists; eauto; move:H2; case:eqP => H; subst.
          move=> [n2 H].
          eexists; apply: run_cut X H.
        move=> ?; subst.
        by have [_[??]] := run_dead1 _ dA1 H1; subst.
      case X: expand => //[s4' D'|s4' D'][??]; subst; have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
        case: s3 HB => [s3|] HB//.
        move=> [H1[H2[H3 H4]]]; subst.
        repeat eexists; eauto.
        apply: run_step X H1.
      case: s3 HB => [s3|] HB//.
      move=> [H1[H2[H3 H4]]]; subst.
      move: H2; case:eqP => H; subst.
        move=>[n2]/(run_consistent (is_ko_runb is_ko_cutr)) [?[??]]; subst.
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
        case: r {rB} => //.
        move=> [H1 [H2[H3 H4]]]; subst.
        case: n1 H1 H2 => //=[|n1] H1.
          move=> [n2 H]; repeat eexists; eauto.
          move=> /=; eexists; apply: run_fail fB X H.
        by have [_[??]] := run_dead1 _ dA H1; subst.
      case nA1 : next_alt => [A1'|]//.
        move=> [?]; subst.
        have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
        case: r {rB} => //.
        move=> [H1 [H2[H3 H4]]]; subst.
        case: n1 H1 H2 => //=[|n1] H1.
          move=> [n2 H]; repeat eexists; eauto.
            apply: run_fail fA nA1 H1.
          by eexists; eauto.
        move=> ?; subst; repeat eexists => //.
          apply: run_fail fA nA1 H1.
        by [].
      case:ifP => //dB1.
      case nB1: next_alt => [nB1'|]//=[?]; subst.
      have {IH}[n1] := IH _ _ _ _ _ erefl erefl erefl.
      case: r {rB} => //.
      move=> [H1 [H2[H3 H4]]]; subst.
      case: n1 H1 H2 => //=[|n1] H1.
        have [_[? _]]:= run_dead2 _ H1; subst.
        move=> [n2 H]; repeat eexists; eauto.
          apply: run_dead fA nA1.
        by eexists; apply: next_alt_runb; eauto.
      move=> ?; subst; repeat eexists => //.
        have [_[? _]]:= run_dead2 _ H1; subst.
        apply: run_dead fA nA1.
      by have [?[]]:= run_dead2 _ H1.
    + move=> s1 B ++ s2 A1 B1 A2 B2 ? + _; subst => /=.
      case:ifP => [dA1 fB1|dA1 fA1].
        case nB1: next_alt => // _ [<-{A2}<-{B2}].
        repeat eexists; rewrite?dead2//.
          apply: run_dead (is_dead_failed dA1) _.
          by rewrite is_dead_next_alt.
        eexists; apply: run_dead fB1 nB1.
      case nA1: next_alt => [A1'|]//=.
      case:ifP => [dB1 _|dB1].
        move=> [<-<-{A2 B2}].
        repeat eexists; rewrite ?dead2//.
          apply: run_dead fA1 nA1.
        by eexists; apply: run_dead (is_dead_failed dB1) (is_dead_next_alt _ _).
      case nB1: next_alt => // _ [<-<-{A2 B2}].
      repeat eexists; rewrite ?dead2//.
        apply: run_dead fA1 nA1.
      eexists.
      case X: (failed B1).
        apply: run_dead X nB1.
      by rewrite next_alt_not_failed in nB1.
  Qed.

  (* Lemma run_or_correct_dead {s1 s2 A B}:
    dead_run u s1 A -> dead_run u s2 B -> dead_run u s1 (Or A s2 B).
  Proof.
    move=> HA HB C n.
    have [n[r'[]]] := run_or_complete H.
      by move=> []/HA.
    apply: HB.
  Qed. *)

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> runb u sIgn1 (Or A s B) s2 D b2 ->
      runb u sIgn2 (Or A s B) s2 D 0.
  Proof.
    move=> H1 H2.
    have:= runb_same_structure _ H2.
    case: D H2 => //= A' s' B' + /eqP?; subst.
    move=> /[dup] /runb_or0-> /(run_ko_left1 H1) [b'][H2 -> {A'}].
    apply: run_ko_left2 H1 H2.
  Qed.

  (* Lemma failed_cutl_runb A:
    failed (cutl A) -> forall s, dead_run u s (cutl A).
  Proof.
    elim: A => //=.
    - move=> _ s1 s2 B n; inversion 1; subst => //; inversion H0; subst => //.
    - move=> _ s1 s2 B n; inversion 1; subst => //; inversion H0; subst => //.
    - move=> _ s1 s2 B n; inversion 1; subst => //; inversion H0; subst => //.
    - move=> _ _ _ s1 s2 B n; inversion 1; subst => //; inversion H0; subst => //.
    - move=> _ s1 s2 B n; inversion 1; subst => //; inversion H0; subst => //.
    - move=> A HA s B HB; case: ifP => dA/=; rewrite ?is_dead_cutl dA => F.
        move=> s1 s2 r n H.
        have [b[r' [H1 H2]]] := run_ko_left1 (is_dead_is_ko dA) H; eauto.
        apply: HB F _ _ _ _ _.
        by eauto.
      move=> s1 s2 r n H.
      have [b[r' [H1 H2]]] := run_or_ko_right2 is_ko_cutr H; eauto; subst.
      apply: HA F _ _ _ _ _.
      by eauto.
    - move=> A HA B0 HB0 B HB.
      case F: failed => //=.
        move=> _ s1 s2 r n H.
        inversion H; subst; move: H0 => /=; rewrite failed_expand => //-[?]; subst.
        by move: H1 => /=; rewrite F next_alt_cutl_failed// if_same.
      move=> /andP[sA fB] s1 s2 r n H.
      inversion H; subst; move: H0 => /=; rewrite succes_is_solved//= failed_expand//=.
      move=>[?]; subst; move: H1; rewrite /= sA success_failed//=.
      rewrite (next_alt_cutl_failed fB) next_alt_cutl_success//?if_same//.
      rewrite -success_cut//.
  Qed. *)

  (* Lemma run_and_correct {s0 sn A B0 B r b}:
    runb u s0 (And A B0 B) sn r b ->
    (Texists sm r1 b1, runb u s0 A sm r1 b1 /\
      Texists b2 r2, ((runb u sm B sn r2 b2) + 
        (* TODO: it should not be Texsists sm, but I should provide the right substitution *)
        (* The problem is given by a state like (A \/ B) /\ C
           A succeeds, C fails, the substitution on which we should run C0
           is the one obtained by running B (i.e. next_alt A).
        *)
        (Texists sm, runb u sm B0 sn r2 b2))).
  Proof.
    remember (And _ _ _) as a eqn:Ha => H.
    elim: H A B0 B Ha; clear.
    - move=> s1 s2 r A B /expand_solved_same [[??]+] ? C D E ?; subst => /=.
      move=> /andP[sC sE].
      repeat eexists.
        apply: run_done (succes_is_solved _ _ sC) erefl.
      rewrite sC; left; apply: run_done erefl.
      apply: succes_is_solved sE.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: expand => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_cut X IH.
      case Y: expand => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= expand_solved_same _ X; subst.
      have sC' := sC.
        rewrite -success_cut in sC'.
      have {IH} [?[??]] := run_consistent _ IH (runb_success1 _ _ sC'); subst.
      rewrite ges_subst_cutl in H2.
      case: H2 => H2.
        by repeat eexists; left; apply: run_cut Y H2.
      move: H2 => [sm H2].
      case sD: (success (cutl D)).
        have [?[??]] := run_consistent _ H2 (runb_success1 _ _ sD); subst.
        repeat eexists; right.
        rewrite success_cut in sD.
        rewrite ges_subst_cutl.
        eexists; apply: runb_success1 sD.
      have:= @failed_success_cut D.
      rewrite sD/= => H1.
      by have:= failed_cutl_runb _ H1 _ _ _ _ H2.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: expand => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_step X IH.
      case Y: expand => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= expand_solved_same _ X; subst.
      have {IH} [?[??]] := run_consistent _ IH (runb_success1 _ _ sC); subst.
      case: H2 => H2.
        repeat eexists; left; apply: run_step Y H2.
      by repeat eexists; eauto.
    - move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D E F ?; subst.
      move=> /= /orPT[fD|/andP[sD fF]].
        rewrite fD; case: ifP => //dD.
        case W: next_alt => //=[D'].
        case X: next_alt => //=[E'][?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split.
          apply: run_fail (failed_expand _ fD) W IH.
        case: H2 => H2; repeat eexists; eauto.
        right; eexists; apply: next_alt_runb X H2.
      rewrite success_failed// success_is_dead//sD.
      case W: next_alt => //=[F'|].
        move=>[?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split; eauto.
        case: H2 => H2; repeat eexists; eauto.
        left; apply: next_alt_runb W H2.
      case X: next_alt => //=[D'].
      case Y: next_alt => //=[E'][?]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done erefl.
        apply: succes_is_solved sD.
      case: H2 => H2; repeat eexists.
        right; eexists; apply: next_alt_runb Y _.
        eauto.
      repeat eexists; right; eauto.
  Qed. *)
End s.
From mathcomp Require Import all_ssreflect.
From det Require Import run run_prop.
From det Require Import zify_ssreflect.

Section s.
  Variable u : Unif.

  Lemma next_alt_exp_same {s A r}:
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
    - move=> s1 s2 A B C r n /expand_failed_same [? _] + _ IH D s3 E ?; subst => /=.
      case: ifP => //dD.
        by case: next_alt => //? [?]; subst; apply: IH.
      case: next_alt => //. 
        by move=> ?[?]; subst; apply: IH.
      case: ifP => // _.
      case: next_alt => //. 
      by move=> ?[?]; subst; apply: IH.
  Qed.

  Lemma next_alt_runb {A B C s s2 b1}:
    next_alt false A = Some B ->
      runb u s B s2 C b1 ->
        runb u s A s2 C b1.
  Proof.
    case fA: (failed A).
      repeat eexists; apply: run_fail; eauto.
      by apply: failed_expand.
    by rewrite next_alt_not_failed// => -[->].  
  Qed.

  Lemma run_ko_left1 {s1 s2 A B b sx r}:
    is_ko A -> runb u s1 (Or A s2 B) sx r b ->
      Texists b r', runb u s2 B sx r' b /\ 
        (omap (fun x => Or (if is_dead A then A else dead1 A) s2 x) r' = r).
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1 => + H.
    elim: H A B s2 Ho1; clear.
    + move=> s s' r A B H ->  A' B' s2 ? kA'; subst.
      have [[??]sA]:= expand_solved_same _ H; subst.
      move: sA => /=.
      case: ifP => [dA sB|dA sA]; last first.
        by rewrite is_ko_success in sA.
      repeat eexists; auto.
      apply: run_done (succes_is_solved _ _ sB) erefl.
    - move=> s1 s2 s3 r A B n + HB IH C D s4 ? kC; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 s3 r A B n + HB IH C D s4 ? kC; subst => /=.
      case: ifP => dC.
        case X: expand => //[s4' D'|s4' D'][??]; subst; 
        have {IH} [b[r'[H1 H2]]]:= IH _ _ _ erefl kC; subst; rewrite dC in HB; subst;
        rewrite dC; repeat eexists.
          apply:run_step X H1.
        apply:run_cut X H1.
      by rewrite is_ko_expand.
    - move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D E s3 ? kD; subst.
      rewrite /=(is_ko_next_alt _ kD).
      case: ifP => [dD fE|dD fD].
        case X: next_alt => //[E'][?]; subst.
        have [b[r'[{}IH H]]] := IH _ _ _ erefl kD; subst; rewrite dD/= in rC; subst.
        rewrite dD; repeat eexists.
        apply: run_fail; eauto.
        by apply: failed_expand.
      case: ifP => //dE.
      case W: next_alt => //[E'][?]; subst.
      have [b[r'[{}IH H]]] := IH _ _ _ erefl (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead/= in H; subst.
      have {W IH} := next_alt_runb W IH.
      repeat eexists; eauto.
  Qed.

  Lemma run_ko_left2 {s2 X B r SOL b1} sIgn:
    is_ko X -> runb u s2 B SOL r b1 ->
    runb u sIgn (Or X s2 B) SOL (omap (fun x => Or (if is_dead X then X else dead1 X) s2 x) r) 0.
  Proof.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s s' r A B /expand_solved_same [[??]sB] ? sIgn X kX; subst => /=.
      case dX: (is_dead X).
        repeat eexists.
          apply: run_done.
            rewrite/= (succes_is_solved _ _ sB) is_ko_expand// .
          rewrite dX => //.
        by move=> /=; rewrite dX/=; case: next_alt; auto.
      repeat eexists.
      apply: run_fail => /=.
        by rewrite dX is_ko_expand//.
        by rewrite/= dX is_ko_next_alt// success_is_dead// next_alt_not_failed// success_failed//.
      apply: run_done.
        rewrite/= (succes_is_solved _ _ sB) is_dead_dead//.
      rewrite /=is_dead_dead//.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X).
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step.
          rewrite /= dX HA//.
        by eassumption.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead in IH.
      repeat eexists.
      apply: run_fail.
        rewrite/=dX is_ko_expand//.
        move=>/=; rewrite dX is_ko_next_alt//.
        have fA := expand_not_failed _ HA notF.
        rewrite next_alt_not_failed//failed_dead//.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    (* TODO: the following case is same as previous... *)
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      case dX: (is_dead X).
        have {}IH := IH sIgn _ kX.
        rewrite dX in IH.
        apply: run_step.
          rewrite /= dX HA//.
        by eassumption.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead in IH.
      repeat eexists.
      apply: run_fail.
        rewrite/=dX is_ko_expand//.
        move=>/=; rewrite dX is_ko_next_alt//.
        have fA := expand_not_failed _ HA notF.
        rewrite next_alt_not_failed//failed_dead//.
      apply: run_step IH.
      rewrite /=is_dead_dead HA//.
    + move=> s1 s2 A B C r n /expand_failed_same [? fB] nB rC IH sIgn X kX; subst.
      case dX: (is_dead X).
        have {}IH:= IH sIgn _ kX.
        rewrite dX in IH; subst.
        repeat eexists.
        apply: run_fail IH.
          rewrite/= dX failed_expand//.
        rewrite/= dX nB//.
      have {}IH:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead in IH; subst.
      repeat eexists; repeat eexists.
      apply: run_fail IH.
        rewrite/=dX is_ko_expand//.
      move=>/=; rewrite dX is_ko_next_alt//(next_alt_dead nB) nB//.
  Qed.

  Lemma run_or_ko_right1 {s2 X B B' SOL b1} sIgn:
    is_ko X -> runb u s2 B SOL B' b1 ->
    runb u s2 (Or B sIgn X) SOL (omap (fun x => Or x sIgn (if b1 == 0 then X else cutr X)) B') 0.
  Proof.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s s' r A B /expand_solved_same [[??]sB] ? sIgn X kX; subst => /=.
      apply: run_done.
        rewrite/= success_is_dead// succes_is_solved//.
      rewrite/= success_is_dead// (is_ko_next_alt _ kX)// if_same//.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      have:= IH sIgn (cutr X) is_ko_cutr.
      by rewrite cutr2 if_same.
    + move=> s1 s2 s3 r A B n HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      by apply: IH.
    + move=> s1 s2 A B C r n /expand_failed_same [? fB] nB rC IH sIgn X kX; subst.
      apply: run_fail.
        rewrite/= (failed_expand _ fB)//; rewrite (next_alt_dead nB)//.
        move=>/=; rewrite (next_alt_dead nB) nB//.
      by apply: IH.
  Qed.

  Lemma run_or_ko_right2 {s2 X B SOL r sIgn b}:
    is_ko X -> runb u s2 (Or B sIgn X) SOL r b ->
      Texists b1 r', runb u s2 B SOL r' b1 /\ omap (fun x => Or x sIgn (if b1 == 0 then X else cutr X)) r' = r.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => +HB.
    elim: HB B sIgn X Ho; clear.
    + move=> s s' r A B /expand_solved_same [[??]+] ? C sIgn X ? kX; subst => /=.
      rewrite is_ko_success//.
      case: ifP => //dC sC.
      rewrite (is_ko_next_alt _ kX) if_same.
      repeat eexists.
      apply: run_done (succes_is_solved _ _ sC) erefl.
      by auto.
    + move=> s1 s2 s3 r A B n + HB IH C sIgn X ? kX; subst => /=.
      case: ifP; case: expand => //.
    + move=> s1 s2 s3 r A B n + HB IH C sIgn X ? kX; subst => /=.
      rewrite (is_ko_expand _ kX); case: ifP => //dC.
      case W: expand => //[s1' C'|s1' C'][??]; subst.
        have [b1[r' [{}IH H]]] := IH _ _ _ erefl kX; subst.
        repeat eexists; apply: run_step W IH.
      have [b1[r' [{}IH H]]] := IH _ _ _ erefl is_ko_cutr; subst.
      repeat eexists.
        apply: run_cut W IH.
      by rewrite cutr2 if_same.
    + move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D sIgn X ? kX; subst => /=.
      rewrite (is_ko_next_alt _ kX) if_same.
      case: ifP => //[dD fD].
      case W: next_alt => //[D'][?]; subst.
      have [b1[r' [{}IH H]]] := IH _ _ _ erefl kX; subst.
      repeat eexists.
      apply: next_alt_runb W IH.
  Qed.

  Lemma run_or_correct_left {s1 A s2 b r} sX X:
    runb u s1 A s2 r b ->
      Texists r', 
        runb u s1 (Or A sX X) s2 r' 0 /\
          if b == 0 then
            if r is Some A' 
              then (r' = (Some (Or A' sX X))) :> Type
            else if next_alt false X is Some X' 
              then Texists A'', is_dead A'' /\ (r' = Some (Or A'' sX X'))
            else r' = None
          else r' = omap (fun x => Or x sX (cutr X)) r
           .
  Proof.
    move=> H; elim: H X; clear.
    + move=> s s' r A B /[dup] /(expand_solved_same) [[??]sA] H ? X; subst.
      repeat eexists.
        apply: run_done erefl; rewrite /= H success_is_dead//.
      rewrite//= success_is_dead//.
      case W: next_alt => //=.
      case Z: next_alt => //=[C'|].
        rewrite (next_alt_dead Z); repeat eexists; rewrite is_dead_dead//.
      rewrite if_same//.
    + move=> s1 s2 s3 r A B n HA HB IH X/=.
      case: n HB IH => //=.
        move=> + /(_ (cutr X)) [r'[{}H1]].
        case: r => [B'|].
          move=> HB?; subst.
          repeat eexists => //.
          apply: run_step.
            by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
          by [].
        rewrite (is_ko_next_alt _ is_ko_cutr) => H2 ?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move=> n + /(_ (cutr X)) [r'[{}H1]].
      rewrite cutr2.
      case: r => [B'|].
      move=> HB?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move => H2 ?; subst.
      repeat eexists => //.
      apply: run_step.
        by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      by [].
    + move=> s1 s2 s3 r A B n HA HB IH X/=.
      case: n HB IH => //=.
        move=> + /(_ X) [r'[{}H1]].
        case: r => [B'|].
          move=> HB?; subst.
          repeat eexists => //.
          apply: run_step.
            by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
          by [].
        case Y: next_alt => [X'|].
          move=> HB [A'' [dA'' ?]]; subst.
          repeat eexists; eauto.
          apply: run_step; eauto; rewrite/= HA.
          by case: ifP => // dA; rewrite is_dead_expand in HA.
        move=> rB ?; subst.
        repeat eexists => //.
        apply: run_step.
          by move=> /=; rewrite HA; case: ifP => //dA;rewrite is_dead_expand in HA.
        by [].
      move=> n + /(_ (X)) [r'[{}H1]].
      case: r => [B'|].
      move=> HB?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move => H2 ?; subst.
      repeat eexists => //.
      apply: run_step.
        by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      by [].
    + move=> s1 s2 A B C r n HA HB HC + X.
      move=> /(_ X)[r' [H1 H2]].
      repeat eexists; try eassumption.
      apply: run_fail H1.
        move=> /=; rewrite HA; case: ifP => //dA.
        move: HA; rewrite is_dead_expand// =>-[?]; subst.
        by rewrite is_dead_next_alt in HB.
      by rewrite/= HB (next_alt_dead HB).
  Qed.

  Lemma run_or_complete {s1 s2 A B s3 r b}:
  (* TODO: be more precise on altAB *)
    runb u s1 (Or A s2 B) s3 r b ->
      (Texists n r', (
        (runb u s1 A s3 r' n /\ 
          (
            if n == 0 then
              if r' is Some A' 
                then (r = (Some (Or A' s2 B))) :> Type
              else if next_alt false B is Some B' 
                then Texists A'', is_dead A'' /\ (r = Some (Or A'' s2 B'))
              else r = None
            else r = omap (fun x => Or x s2 (cutr B)) r'
          )
        )%type2
         + 
        (runb u s2 B s3 r' n))%type).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1 => H.
    elim: H s2 A B HO1 => //=; clear.
    + move=> s1 s2 r A B /expand_solved_same [[??] +] ? s3 C D ?; subst => /=.
      case:ifP => [dC sD|dC sC]; repeat eexists.
        right; apply: run_done erefl.
        by apply: succes_is_solved sD.
      left; repeat eexists.
        apply: run_done erefl.
        by apply: succes_is_solved.
      case X: next_alt => //=.
      case Y: next_alt => //[D'|]; rewrite?if_same//.
      repeat eexists; last first.
        rewrite (next_alt_dead Y)//.
      by rewrite is_dead_dead.
    + move=> s1 s2 s3 r A B n + HB IH s4 C D ?; subst => /=.
      by case: ifP; case: expand => //.
    + move=> s1 s2 s3 r A B n + HB IH s4 C D ?; subst => /=.
      case: ifP => dC.
        case X: expand => //[s4' D'|s4' D'][??]; subst.
          have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
            by have:= is_dead_runb _ dC IH.
          repeat eexists; right.
          apply: run_step X IH.
        have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
          by have:= is_dead_runb _ dC IH.
        repeat eexists; right.
        apply: run_cut X IH.
      case X: expand => //[s4' D'|s4' D'][??]; subst.
        have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
          repeat eexists; left; split; eauto.
          apply: run_step X IH.
        by repeat eexists; eauto.
      have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
        repeat eexists; left; split; eauto.
          apply: run_cut X IH.
        move: H1.
        move=> /=; rewrite cutr2 next_alt_cutr.
        case: eqP => //=?; subst.
        case: b1 IH => //=.
      by have:= is_ko_runb _ is_ko_cutr IH.
    + move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH s3 D E ?; subst => /=.
      case: ifP => [dD fE|dD fD].
        case X: next_alt => //[E'][?]; subst.
        have := IH _ _ _ erefl=> -[aB[b1 [[{}IH H1]|{}IH]]].
          by have:= is_dead_runb _ dD IH.
        repeat eexists; right.
        apply: run_fail; eauto.
        by apply: failed_expand.
      case X: next_alt => //[D'|].
        move=>[?]; subst.
        have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
          repeat eexists; left; split; eauto.
          apply: run_fail; eauto.
          by apply: failed_expand.
        by repeat eexists; right; eauto.
      case: ifP => // dE; case W: next_alt => //[E'][?]; subst.
      have := IH _ _ _ erefl => -[aB[b1 [[{}IH H1]|{}IH]]].
        by have:= is_dead_runb _ is_dead_dead IH.
      repeat eexists; right.
      apply: next_alt_runb W IH.
  Qed.

  Lemma run_or_correct_dead {s1 s2 A B}:
    dead_run u s1 A -> dead_run u s2 B -> dead_run u s1 (Or A s2 B).
  Proof.
    move=> HA HB sX C b H.
    have [n[r'[]]] := run_or_complete H.
      by move=> []/HA.
    apply: HB.
  Qed.

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> runb u sIgn1 (Or A s B) s2 D b2 ->
      runb u sIgn2 (Or A s B) s2 D 0.
  Proof.
    move=> H1 H2.
    have [b1[r1 [H3 H4]]]:= run_ko_left1 H1 H2.
    by have H5 := run_ko_left2 sIgn2 H1 H3; subst.
  Qed.

  Lemma failed_cutl_runb A:
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
  Qed.

  Lemma run_and_correct {s0 sn A B0 B r b}:
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
  Qed.
End s.
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
        by have:= HB s; case: expand => //= _ s' B'/(_ erefl)->//.
      have:= HA s1; case: expand => //= _ _ _ /(_ erefl)->//.
    - move=> A HA B0 _ B HB s; case: ifP => dA.
        by rewrite is_dead_expand//.
      have:= HA s; case X: expand => //= [b s' A'|s' A'] /(_ erefl).
        move=> /(_ erefl)->; rewrite (expand_not_failed _ X notF) (expand_not_solved_not_success _ X notF)//.
      have [[??]sA] := expand_solved_same _ X; subst.
      rewrite sA success_failed//.
      have:= HB (get_substS s A').
      case Y: expand => //= [b s'' B'] /(_ erefl erefl) ->//.
  Qed.

  Lemma runb_or0 {s1 A s B s2 r b}:
    runb u s1 (Or A s B) s2 r b -> b = 0.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s B Ho; clear => //.
    - move=> s1 s2 s3 r A B n b1 nn + _ IH ? C s D ?; subst => /=.
      case: ifP => //=dC.
        case X: expand => // [b' s' D']/=[???]; subst; by apply: IH.
      by case Y: expand=> //[b' s1' C'][???]; subst; apply: IH.
    - move=> s1 s2 A B C r n /expand_failed_same [? _] + _ IH D s3 E ?; subst => /=.
      case: ifP => //dD.
        by case: next_alt => //? [?]; subst; apply: IH.
      case: next_alt => //. 
        by move=> ?[?]; subst; apply: IH.
      case: ifP => // _.
      case: next_alt => //. 
      by move=> ?[?]; subst; apply: IH.
  Qed.

  (* Lemma next_alt_exp_Failed {s1 A B C b1}:
    expandedb u s1 A (Failed B) b1 ->
      next_alt false B = Some C ->
        if A == B then true
        else next_alt false A == Some A.
  Proof.
    remember (Failed _) as f eqn:Hf => H.
    elim: H B C Hf; clear => //.
    - move=> s A B HA C D [<-] H.
      rewrite  (expand_failed_same _ HA) eqxx//.
    - move=> s1 s2 r A1 A2 b HA1 HA2 IH B C ? HB; subst.
      have {IH} := IH _ _ erefl HB.
      case: eqP => H; subst;
      rewrite (next_alt_exp_same HA1 erefl erefl) eqxx if_same//.
    - move=> s1 s2 r A1 A2 b HA1 HA2 IH B C ? HB; subst.
      have {IH} := IH _ _ erefl HB.
      case: eqP => H; subst;
      rewrite (next_alt_exp_same HA1 erefl erefl) eqxx if_same//.
  Qed. *)

  (* Lemma expandedb_exists s A:
    Texists r b, expandedb u s A r b.
  Proof.
    elim: A s => //=.
    - move=> s; do 2 eexists; apply: expanded_fail => //.
    - move=> s; do 2 eexists; apply: expanded_done => //.
    - move=> s; do 2 eexists; apply: expanded_step => //.
      apply: expanded_done => //.
    - move=> s; do 2 eexists; apply: expanded_fail => //.
    - move=> p c s.
      case X : (F u p c s) => [|[s' x] xs].
        do 2 eexists.
        apply: expanded_step => //=.
        apply: expanded_fail.
        rewrite/big_or X//.
      do 2 eexists.
      apply: expanded_step => //=.
      apply: expanded_fail.
      rewrite/big_or X//.
    - move=> s; do 2 eexists.
      apply: expanded_cut => //.
      apply: expanded_done => //.
    - move=> A HA s B HB s1.
      have [r[b {}HA]]:= HA s1.
      have [r1 [b1 {}HB]] := HB s.
      case: r HA => [s1' A'|A'] HA.
        have H1 := expanded_or_correct_left _ _ HA s B.
        do 2 eexists; eassumption.
      case dA: (is_dead A).
        case: r1 HB => [s' B'|B'] H1.
          have := expanded_or_correct_right _ s1 dA H1.
          do 2 eexists; eassumption.
        have := expanded_or_correct_right_fail _ dA H1 s1.
        do 2 eexists; eassumption.
      have  := expanded_or_correct_left_fail _ _ dA HA s B.
      do 2 eexists; eassumption.
    - move=> A HA B0 _ B HB s.
      have [r[bA {}HA]] := HA s.
      case: r HA => [s' A'|A'] HA.
        have [r[bB {}HB]]:= HB s'.
        case: r HB => [s'' B'|B'] HB.
          have := expanded_and_correct_done _ B0 HA HB.
          do 2 eexists; eassumption.
        have := run_and_fail_both _ B0 HA HB.
        do 2 eexists; eassumption.
      have [b]:= expanded_and_fail_left _ HA B0 B.
      do 2 eexists; eassumption.
  Qed. *)

  (* Lemma run_dead_left1 {s1 s2 A B b sx r}:
    is_dead A -> runb u s1 (Or A s2 B) sx r b ->
      (Texists b r', runb u s2 B sx r' b /\ omap (fun x => Or A s2 x) r' = r).
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1 => + H.
    elim: H A B s2 Ho1; clear.
    + move=> s s' r A B H ->  A' B' s2 ? dA'; subst.
      have [[??]sA]:= expand_solved_same _ H; subst.
      move: sA => /=.
      rewrite dA' => sB.
      repeat eexists.
      apply: run_done (succes_is_solved _ _ sB) erefl.
    - move=> s1 s2 s3 r A B n + HB IH C D s4 ? kC; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 s3 r A B n + HB IH C D s4 ? dC; subst => /=.
      rewrite dC.
      case X: expand => //[s4' D'|s4' D'][??]; subst; 
      have {IH} [b[r'[H1 H2]]]:= IH _ _ _ erefl dC; subst;
      repeat eexists.
        apply:run_step X H1.
      apply:run_cut X H1.
    - move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D E s3 ? dD; subst.
      move=> /=.
      rewrite dD => fE.
      case X: next_alt => //[E'][?]; subst.
      have [b[r'[{}IH ?]]] := IH _ _ _ erefl dD; subst.
      repeat eexists; apply: run_fail; eauto.
      by apply: failed_expand.
  Qed.

  Lemma run_dead_left2 sIgn {s2 A B b sx r}:
    is_dead A -> runb u s2 B sx r b ->
      Texists r', runb u sIgn (Or A s2 B) sx r' 0 /\ 
        ((omap (fun x => Or A s2 x) r = r') + (omap (fun x => Or A s2 x) r = r')).
  Proof.
    move=> + H; elim: H sIgn A; clear => //.
    + move=> s1 s2 r A B /expand_solved_same [[??]sB] ? s3 C dA; subst.
      repeat eexists.
        apply: run_done; rewrite//= dA succes_is_solved//.
      rewrite dA; auto.
    + move=> s1 s2 s3 r A B n HA HB IH s4 C dC.
      have [r'[H1 H2]] := IH s4 _ dC.
      repeat eexists.
        apply: run_step H1; rewrite/= dC HA//.
      auto.
    + move=> s1 s2 s3 r A B n HA HB IH s4 C dC.
      have [r'[H1 H2]] := IH s4 _ dC.
      repeat eexists.
        apply: run_step H1; rewrite/= dC HA//.
      auto.
    + move=> s1 s2 A B C r n /expand_failed_same [? fB] nB rC IH s3 D dD; subst.
      have {IH} [r'[H1 H2]] := IH s3 _ dD.
      repeat eexists.
        apply: run_fail H1 => /=.
          rewrite dD failed_expand//.
        rewrite/=dD nB//.
      auto.
  Qed. *)

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
    - move=> s1 s2 s3 r A B n b1 nn + HB IH ? C D s4 ? kC; subst => /=.
      case: ifP => dC.
        case X: expand => //[b' s4' D'][???]; subst.
        have {IH} [b[r'[H1 H2]]] := IH _ _ _ erefl kC; subst.
        repeat eexists.
          apply: run_step X H1 erefl.
        by rewrite dC.
      rewrite is_ko_expand //.
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
    Texists r', runb u sIgn (Or X s2 B) SOL r' 0 /\ 
      (omap (fun x => Or (if is_dead X then X else dead1 X) s2 x) r = r').
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
    + move=> s1 s2 s3 r A B n b1 nn HA HB IH ? sIgn X kX; subst.
      case dX: (is_dead X).
        have [r'[{}IH H]]:= IH sIgn _ kX.
        rewrite dX in H; subst.
        repeat eexists.
        apply: run_step IH _.
          rewrite /= dX HA//.
        by [].
      have [r'[{}IH H]]:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead in H; subst.
      repeat eexists.
      apply: run_fail.
        rewrite/=dX is_ko_expand//.
        move=>/=; rewrite dX is_ko_next_alt//.
        have fA := expand_not_failed _ HA notF.
        rewrite next_alt_not_failed//failed_dead//.
      apply: run_step IH _.
        rewrite /=is_dead_dead HA//.
      by [].
    + move=> s1 s2 A B C r n /expand_failed_same [? fB] nB rC IH sIgn X kX; subst.
      case dX: (is_dead X).
        have [r'[{}IH H]]:= IH sIgn _ kX.
        rewrite dX in H; subst.
        repeat eexists.
        apply: run_fail IH.
          rewrite/= dX failed_expand//.
        rewrite/= dX nB//.
      have [r'[{}IH H]]:= IH sIgn (dead1 X) (is_dead_is_ko is_dead_dead).
      rewrite is_dead_dead in H; subst.
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
    + move=> s1 s2 s3 r A B n b1 nn HA HB IH ? sIgn X kX; subst.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      have kK : is_ko (if b1 then cutr X else X) .
        by case: ifP ; rewrite // is_ko_cutr//.
      have := IH sIgn (if b1 then cutr X else X) kK.
      case: b1 {HA kK}; eauto.
      rewrite cutr2 if_same//.
      by[].
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
    + move=> s1 s2 s3 r A B n b1 nn + HB IH ? C sIgn X ? kX; subst => /=.
      rewrite is_ko_expand => //.
      case: ifP => //.
      case Y: expand => //[b1' s' X'] dC [???]; subst.
      have k: is_ko (if b1' then cutr X else X).
        by case: ifP ; rewrite // is_ko_cutr//.
      have [b2[r'[{}IH ?]]] := IH _ _ _ erefl k; subst.
      repeat eexists.
        apply: run_step Y IH erefl.
      case: b1' {k HB Y} => //.
      rewrite cutr2 if_same//.
    + move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D sIgn X ? kX; subst => /=.
      rewrite (is_ko_next_alt _ kX) if_same.
      case: ifP => //[dD fD].
      case W: next_alt => //[D'][?]; subst.
      have [b1[r' [{}IH H]]] := IH _ _ _ erefl kX; subst.
      repeat eexists.
      apply: next_alt_runb W IH.
  Qed.

  Lemma run_or_complete {s1 s2 A B SOL altAB b}:
  (* TODO: be more precise on altAB *)
    runb u s1 (Or A s2 B) SOL altAB b ->
      (Texists altA b1, runb u s1 A SOL altA b1) + 
        (Texists altB b1, runb u s2 B SOL altB b1).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1 => H.
    elim: H s2 A B HO1 => //=; clear.
    + move=> s1 s2 r A B /expand_solved_same [[??] +] ? s3 C D ?; subst => /=.
      case:ifP => [dC sD|dC sC].
        right; repeat eexists; apply: run_done erefl.
        apply: succes_is_solved sD.
      left; repeat eexists; apply: run_done erefl.
      apply: succes_is_solved sC.
    + move=> s1 s2 s3 r A B n b1 nn + HB IH ? s4 C D ?; subst => /=.
      case: ifP => dC.
        case X: expand => //[b1' s4' D'][???]; subst.
        have:= IH _ _ _ erefl => -[]; auto => -[r'[b2 {}IH]].
        right; repeat eexists; apply: run_step X IH erefl.
      case X: expand => //[b1' s4' D'][???]; subst.
      have [] := IH _ _ _ erefl.
        move=> [r' [b2 {}IH]]; left.
        repeat eexists.
        apply: run_step X IH erefl.
      case: b1' X {IH} HB => //= X HB; auto.
      move=> [r' [b2 {}IH]].
      by have:= is_ko_runb _ (is_ko_cutr) IH.
    + move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH s3 D E ?; subst => /=.
      case: ifP => [dD fE|dD fD].
        case X: next_alt => //[E'][?]; subst.
        have := IH _ _ _ erefl => -[] [al [b1 {}IH]].
          by have:= is_dead_runb _ dD IH.
        right; repeat eexists; apply: run_fail; eauto.
        by apply: failed_expand.
      case X: next_alt => //[D'|].
        move=>[?]; subst.
        have := IH _ _ _ erefl => -[] [al [b1 {}IH]].
          left; repeat eexists; apply: run_fail; eauto.
          by apply: failed_expand.
        by right; repeat eexists; eauto.
      case: ifP => // dE; case W: next_alt => //[E'][?]; subst.
      have := IH _ _ _ erefl => -[] [al [b1 {}IH]].
        by have:= is_dead_runb _ is_dead_dead IH.
      right; repeat eexists.
      apply: next_alt_runb W IH.
  Qed.

  Lemma run_or_correct_dead {s1 s2 A B}:
    dead_run u s1 A -> dead_run u s2 B -> dead_run u s1 (Or A s2 B).
  Proof.
    move=> HA HB sX C b H.
    have [] := run_or_complete H.
      move=> [x[b1]]; apply: HA.
    move=> [x[b1]]; apply: HB.
  Qed.

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> runb u sIgn1 (Or A s B) s2 D b2 ->
      runb u sIgn2 (Or A s B) s2 D 0.
  Proof.
    move=> H1 H2.
    have [b1[r1 [H3 H4]]]:= run_ko_left1 H1 H2.
    by have [r'[H5 H6]] := run_ko_left2 sIgn2 H1 H3; subst.
  Qed.

  (* Fixpoint has_bt A B :=
    match A, B with
    | Or A _ B, Or A' _ B' =>
        if is_dead A' then 
          if is_dead A then has_bt B B'
          else true (*I'm creating a new dead state = call to backtrack*)
        else false
    | _, _ => false
    end.

  Lemma has_bt_id {A} : has_bt A A = false.
  Proof.
    elim: A => //=.
    move=> A HA _ B HB; case: ifP => dA//; rewrite dA//.
  Qed.

  Lemma expand_has_bt {s A r}:
    expand u s A = r -> has_bt A (get_state r) = false.
  Proof.
    move=> <-; clear r.
    elim: A s => //=.
    move=> A HA s B HB s1; case: ifP => dA.
      move: (HB s); case X: expand => /= ->; rewrite if_same//.
    move: (HA s1); case X: expand => /=; rewrite (expand_not_dead _ dA X)//.
  Qed.

  Lemma has_bt_trans {A B C}:
    same_structure A B -> same_structure B C ->
    has_bt A B = false -> has_bt B C = false -> has_bt A C = false.
  Proof.
    elim: A B C => //= A HA s B HB C D; destruct C, D => //= /and3P[_ Hx Hy] /and3P[_ H1 H2].
    case: ifP => dC1; last first.
      move=> _; case: ifP => dD1//.
    case: ifP => //dA bB.
    case: ifP => // dD1 bC.
    apply: HB Hy H2 bB bC.
  Qed. *)

  Lemma run_and_correct {s0 sn A B0 B r b}:
    runb u s0 (And A B0 B) sn r b ->
    (Texists sm r1 b1, runb u s0 A sm r1 b1).
  Proof.
    remember (And _ _ _) as a eqn:Ha => H.
    elim: H A B0 B Ha; clear.
    - move=> s1 s2 r A B /expand_solved_same [[??]+] ? C D E ?; subst => /=.
      move=> /andP[sC sE].
      repeat eexists; apply: run_done (succes_is_solved _ _ sC) erefl.
    - move=> s1 s2 s3 r A B n b1 nn + rB IH ? C D E ?; subst => /=.
      case X: expand => //[b s1' C'|s1' C'].
        move=> [???]; subst.
        have [sm[r1[b1' {}IH]]]:= IH _ _ _ erefl.
        repeat eexists; apply: run_step X IH erefl.
      case Y: expand => //=[s1'' E'][??]; subst.
      repeat eexists; apply: run_done X erefl.
    - move=> s1 s2 A B C r n /expand_failed_same [? +] + rC IH D E F ?; subst.
      move=> /= /orPT[fD|/andP[sD fF]].
        rewrite fD; case: ifP => //dD.
        case W: next_alt => //=[D'].
        case X: next_alt => //=[E'][?]; subst.
        have [sm[r1[b1 {}IH]]]:= IH _ _ _ erefl.
        repeat eexists; apply: run_fail (failed_expand _ fD) W IH.
      rewrite success_is_dead// success_failed//sD.
      case W: next_alt => //=[F'|].
        move=>[?]; subst.
        have [sm[r1[b1 {}IH]]]:= IH _ _ _ erefl.
        by repeat eexists; eauto.
      case X: next_alt => //=[D'].
      case Y: next_alt => //=[E'][?]; subst.
      repeat eexists.
      apply: run_done erefl.
      apply: succes_is_solved sD.
  Qed.

  (* Lemma run_and_correct {s0 sn A B B0 A' B0' B' b}:
    runb u s0 (And A B0 B) sn (And A' B0' B') b -> Texists A'' b1 b2 sm,
    (* TODO: be more precise on B0: it is cut if B' has a cut *)
    ( runb u s0 A sm (clean_success A'') b1 /\
      (if has_bt A A'' then runb u sm B0 sn (clean_success B' ) b2
      else runb u sm B sn (clean_success B' ) b2) /\
      A' = (if b2 == 0 then A'' else cutl A'')).
  Proof.
    remember (And _ _ _) as O1 eqn:HO1.
    remember (And A' _ _) as O2 eqn:HO2.
    move=> H.
    elim: H A B B0 A' B0' B' HO1 HO2 => //=; clear.
    + move=> s st s' alt C b H ? A B B0 A' B0' B' ? H1; subst.
      have := expandedb_same_structure _ H.
      case: alt H H1 => //= Ax B0x Bx H + _.
      have [s''[b1[b2[A''[H1[H2 [?]]]]]]]:= expanded_and_complete H; subst.
      case: eqP => H3 ?; subst.
        have sA'' := expanded_Done_success _ H1.
        rewrite sA'' => -[???]; subst.
        repeat eexists.
        - apply: run_done H1 erefl.
        - rewrite (expandedb_has_bt H1)//clean_success2//; apply: run_done H2 erefl.
        - move=> //.
      have := expanded_Done_success _ H1.
      rewrite -success_cut => sA''.
      rewrite sA'' => -[???]; subst.
      repeat eexists.
      - apply: run_done H1 erefl.
      - rewrite  (expandedb_has_bt H1)//clean_success2//; apply: run_done H2 erefl.
      - case: eqP => //.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? Ax B0x Bx A' B' C' ??; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= E' F' G' H1 + _.
      case: ifP => dD'//.
      have {H1} [[H1 [??]]|[s'[b5[b6[A'''[H1[H5 [H [Hx Hy]]]]]]]]] := expandes_and_fail H1; subst.
        (* we are in the case (E /\ G) with E failing for expandedb *)
        rewrite (expandedb_failed _ H1).
        case X: next_alt => //=[E2][?]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H5]]]]]]; subst.
        rewrite if_same.
        repeat eexists.
        apply: run_backtrack H1 X rE2 erefl.
        case: ifP => bt//.
        admit. (*should be OK: has_bt Ax A'' should be true *)
      have sA''' := expanded_Done_success _ H1.
      case: b6 H5 Hx Hy => /= [|n] H5 Hx Hy; subst.
        rewrite success_failed sA'''//.
        case W: next_alt => [G''|][?]; subst.
          have {IH} := IH _ _ _ _ _ _ erefl erefl.
          move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
          have [[? H ]?] := run_consistent _ rE2 (runb_success _ _ sA'''); subst.
          case: ifP => hbt H2.
            repeat eexists.
            apply: run_done H1 H.
            case: ifP => hbt1.
              admit.
            admit. (*should be OK: has_bt Ax A'' should be true *)
          repeat eexists.
          apply: run_done H1 H.
          case: ifP; last first => Hz.
            apply: run_backtrack H5 W _ erefl.
            admit. (*should be ok: need lemma: next_alt, the input subst for run is ignorable*)
          admit. (*should be ok: has_bt A''' A' is true*)
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
        rewrite if_same => H.
        repeat eexists.
        apply: run_done H1 _.
          admit. (*?what*)
        admit.
      rewrite -success_cut in sA'''.
      rewrite success_failed//sA'''.
      case W: next_alt => [G''|][?]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
        have [[? H ]?] := run_consistent _ rE2 (runb_success _ _ sA'''); subst.
        (* have:= clean_success_cutl _ sA'''. *)
        (* rewrite cutl2 -H => Hw. *)
        admit.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
      have /= := is_ko_runb _ _ rE2.
      rewrite success_cut in sA'''.
      (* move=> /(_ (clean_success_cutl _ sA'''))//. *)
  Admitted. *)

  (* Lemma run_and_correct_success_left {s0 sn A B B0 C b}:
    success A ->
    runb u s0 (And A B0 B) sn C b -> Texists A' B0' B' b1 b2, C = And A' B0' B' /\
    (   (runb u (get_substS s0 A) B sn (clean_success B' ) b2 /\ 
         A' = clean_success (if b2 == 0 then A else cutl A))%type2 +
    
        Texists sm A'', (runb u s0 (clean_success A) sm (clean_success A'') b1 /\ 
         runb u sm B0 sn (clean_success B') b2 /\
         A' = clean_success (if b2 == 0 then A'' else cutl A''))%type2
    )%type.
  Proof.
    remember (And _ _ _) as O1 eqn:HO1.
    move=> + H.
    elim: H A B B0 HO1 => //=; clear.
    + move=> s st s' alt C b H ? A B B0 ? sA; subst.
      have /= := expandedb_same_structure _ H.
      case: alt H => // A' B0' B' H _.
      move=> /=.
      have [s''[b1[b2[A''[H1[H2 [?]]]]]]]:= expanded_and_complete H; subst.
      have:= expanded_success1 u s sA.
      move=> /(expanded_consistent _ H1) [][]???; subst.
      case: eqP => H3 ?; subst.
        rewrite sA.
        repeat eexists; left; split; (try apply: run_done H2 _);rewrite?clean_success2//.
      rewrite success_cut sA.
      repeat eexists; left; repeat split.
        apply: run_done H2 _; rewrite clean_success2//.
      case: eqP => //.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? E G F ? sE; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= E' F' G' H1 + _.
      case: ifP => dD'//.
      have Hz := expanded_success1 u s sE.
      have {H1} [[H1 [??]]|[s'[b5[b6[A'''[H1[H5 [H [Hx Hy]]]]]]]]] := expandes_and_fail H1; subst.
        by have [] := expanded_consistent _ H1 Hz.
      have {H1}[[]???] := expanded_consistent _ Hz H1; subst A'''; subst.
      case: b6 H5 Hx Hy => //= [|n] H5 ??; subst.
        rewrite success_failed sE//.
        case X: next_alt => //[G''|][?]; subst.
          have {IH} [A'[B0'[B'[b1[b3[? [[H1 H2]|[sm[A'' [H4 [H6 H7]]]]]]]]]]] := IH _ _ _ erefl sE; subst.
            repeat eexists; left; split => //.
            apply: run_backtrack H5 X H1 erefl.
          by repeat eexists; right; repeat eexists; try eassumption.
        admit.
      rewrite -success_cut in sE.
      rewrite success_failed//sE.
      case X: next_alt => [G''|][?]; subst.
        have {IH} [A'[B0'[B'[b1[b3[? [[H1 H2]|[sm[A'' [H4 [H6 H7]]]]]]]]]]] := IH _ _ _ erefl sE; subst.
          repeat eexists.
          left; repeat split.
          rewrite ges_subst_cutl in H1.
          apply: run_backtrack H5 X H1 erefl.
          by rewrite cutl2 if_same.
        rewrite success_cut in sE.
        by have:= is_ko_runb _ (clean_success_cutl _ sE) H4.
      have /= := is_ko_runb _ _ H3.
      rewrite success_cut in sE.
      by move=> /(_ (clean_success_cutl _ sE)).
  Admitted. *)

End s.
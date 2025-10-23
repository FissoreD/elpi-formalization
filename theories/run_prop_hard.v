From mathcomp Require Import all_ssreflect.
From det Require Import run run_prop.
From det Require Import zify_ssreflect.

Section s.
  Variable u : Unif.

  Lemma expandedb_exists s A:
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
  Qed.


  Lemma next_alt_runb {A B C s s2 b1}:
    next_alt false A = Some B ->
      runb u s B s2 C b1 ->
        Texists b, runb u s A s2 C b.
  Proof.
    have [r[b H]]:= expandedb_exists s A.
    elim: H B C s2 b1; clear.
    - move=> s s' A A' HA B C s2 b1 nA HB.
      have [[??]sA]:= expand_solved_same _ HA; subst.
      have:= next_alt_not_failed _ (success_failed _ sA).
      rewrite nA => -[]?; subst.
      eexists; eassumption.
    - move=> s A B HA B0 C s2 b1 nA HB.
      have [? fA]:= (expand_failed_same _ HA); subst => //.
      eexists; apply: run_backtrack nA HB erefl.
      apply: expanded_fail HA.
    - move=> s s' r A B b HA HB IH B0 C s2 b1 nA H.
      have fA:= expand_not_failed _ HA notF.
      have:= next_alt_not_failed _ fA.
      rewrite nA => -[?]; subst.
      eexists; eassumption.
    - move=> s s' r A B b HA HB IH B0 C s2 b1 nA H.
      have fA:= expand_not_failed _ HA notF.
      have:= next_alt_not_failed _ fA.
      rewrite nA => -[?]; subst.
      eexists; eassumption.
  Qed.


  Definition same_or left s1 s2 := 
    match s1, s2 with
    | None, None => True
    | Some (Or A _ B), Some A' => if left then A = A' else B = A'
    | _, _ => False
    end.

  Lemma run_dead_left1 {s1 s2 A B b sx r}:
    is_ko A -> runb u s1 (Or A s2 B) sx r b ->
      (Texists b r', runb u s2 B sx r' b /\ same_or false r r').
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1 => + H.
    elim: H A B s2 Ho1; clear.
    - move=> s1 s2 A1 A2 _ b HA1 <- B1 C1 s3 ? /[subst] dE.
      have:= expandedb_same_structure _ HA1.
      case: A2 HA1 => // B1' s3' C1' /= HA1 /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done _ HA1.
      move=> []; last first.
        move=> [dB1[?[b1 H]]]; subst.
        rewrite dB1.
        repeat eexists.
        apply: run_done H erefl.
        case: next_alt => //.
      move=> [dB1[b1[H1?]]]; subst.
      by have [] := expanded_consistent _ H1 (is_ko_expanded u s1 dE).
    - move=> s1 s2 ? X C D b1 b2 b3 HA HB HC IH ? A B s3 ? dE; subst.
      have:= expandedb_same_structure _ HA.
      case: X HA HB => //= A' s3' B' H1 + /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_fail _ H1.
      move=> [].
        move=> [dA[b3 [H2 H3]]].
        rewrite (expanded_not_dead _ dA H2).
        have [[??]] := expanded_consistent _ H2 (is_ko_expanded u s1 dE); subst.
        simpl in H3; subst.
        rewrite is_ko_next_alt//.
        case: ifP => //dB'.
        case X: next_alt => //=[B''][?]; subst.
        have [b[r' [H4 H5]]]:= IH _ _ _ erefl (is_dead_is_ko is_dead_dead).
        have [? H6]:= next_alt_runb X H4.
        repeat eexists; eauto.
      move=> [dA[?[b3 H2]]]; subst.
      rewrite dA.
      case X: next_alt => //[E''][?]; subst.
      have {IH} [bx [r' [H3 H4]]] := IH _ _ _ erefl dE; subst.
      repeat eexists; eauto.
      apply: run_backtrack erefl; eassumption.
  Qed.

  Lemma run_dead_left2 {s2 X B B' SOL b1} sIgn:
    is_dead X -> runb u s2 B SOL B' b1 ->
    runb u sIgn (Or X s2 B) SOL (omap (fun x => Or X s2 x) B') 0.
  Proof.
    move=> dA HB; elim: HB sIgn; clear -dA.
    - move=> s1 s2 A B C b H1 H2 sIgn; subst.
      have H := expanded_or_correct_right _ sIgn dA H1.
      apply: run_done H _ => /=; rewrite dA//.
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? sIgn; subst.
      have H := expanded_or_correct_right_fail _ dA HA sIgn.
      have {}IH := IH sIgn.
      apply: run_backtrack H _ IH erefl => /=.
      have fE := expandedb_failed _ HA.
      rewrite dA HB//.
  Qed.

  Lemma run_or_ko_right1 {s2 X B B' SOL b1} sIgn:
    is_ko X -> runb u s2 B SOL B' b1 ->
    runb u s2 (Or B sIgn X) SOL (omap (fun x => Or x sIgn (if b1 == 0 then X else cutr X)) B') 0.
  Proof.
    move=> +HB; elim: HB sIgn X; clear.
    - move=> s1 s2 A B C b H1 H2 sIgn X kX; subst.
      have H2 := expanded_or_correct_left _ _ H1 sIgn X.
      apply: run_done H2 _.
      have sB:= expanded_Done_success _ H1.
      rewrite/= success_is_dead//.
      case W: next_alt => //.
      case: ifP => //= dB.
      case: ifP; rewrite is_ko_next_alt//is_ko_cutr//.
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? sIgn X kX; subst.
      case dA': (is_dead A).
        have [[??]] := expanded_consistent _ HA (is_dead_expanded u s1 dA'); subst.
        by rewrite (is_dead_next_alt _ dA') in HB.
      case: b1 HA => [|n] HA.
        apply: run_backtrack.
          apply: expanded_or_correct_left_fail dA' HA _ _.
          move=> /=; rewrite (expanded_not_dead _ dA' HA) HB//.
          apply: IH kX.
          by [].
      move=> /=.
      apply: run_backtrack.
      apply: expanded_or_correct_left_fail dA' HA _ _.
      move=> /=; rewrite (expanded_not_dead _ dA' HA) HB//.
      have:= IH sIgn (cutr X).
      rewrite cutr2 if_same is_ko_cutr; eauto.
      by [].
  Qed.

  Lemma run_or_ko_right2 {s2 X B SOL r sIgn b}:
    is_ko X -> runb u s2 (Or B sIgn X) SOL r b ->
      Texists b1 r', runb u s2 B SOL r' b1 /\ same_or true r r'.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => +HB.
    elim: HB B sIgn X Ho; clear.
    - move=> s1 s2 A B C b H1 H2 D sIgn X Ho kX; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 => //= D' sIgn' X' H1 /and3P[/eqP? _ _]; subst.
      have {H1} [[dD[b1[H2?]]]|[dD[?[b1 H2]]]] := expanded_or_complete_done _ H1; subst.
        repeat eexists.
          apply: run_done H2 erefl.
        rewrite (expanded_not_dead _ dD H2).
        case: next_alt => //.
        case: ifP => //=.
        case: ifP; rewrite is_ko_next_alt//is_ko_cutr//.
      by have [] := expanded_consistent _ H2 (is_ko_expanded _ _ kX).
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? E sIgn X Ho kX; subst.
      have:= expandedb_same_structure _ HA.
      case: B HA HB => //= D' sIgn' X' HA + /and3P[/eqP? _ _]; subst.
      have {HA} [[dE[b3[H1 H2]]]|[dE[?[b3 H1]]]] := expanded_or_complete_fail _ HA; subst.
        rewrite (expanded_not_dead _ dE H1).
        have kX' : is_ko X'.
          move: H2; case: ifP => _ ?; subst => //; rewrite is_ko_cutr//.
        case Y: next_alt => //[D''|].
          move=>[?]; subst.
          have [b4[r'[H3 H4]]]:= IH _ _ _ erefl kX'.
          repeat eexists; eauto.
          apply: run_backtrack H1 Y H3 erefl.
        case: ifP => //dX'.
        rewrite is_ko_next_alt//.
      rewrite dE.
      have [[]??] := expanded_consistent _ H1 (is_ko_expanded _ _ kX); subst.
      rewrite is_ko_next_alt//.
  Qed.

  Lemma run_or_complete {s1 s2 A B SOL altAB b}:
  (* TODO: be more precise on altAB *)
    runb u s1 (Or A s2 B) SOL altAB b ->
      (Texists altA b1, runb u s1 A SOL altA b1) + 
        (Texists altB b1, runb u s2 B SOL altB b1).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1.
    move=> H.
    elim: H s2 A B HO1 => //=; clear.
    + move=> s st s' alt C b H ? s2 D E ?; subst.
      have /= := expandedb_same_structure _ H.
      case: alt H => //= D' s2' E' H /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done _ H.
      move=> [][dD].
        move=> [b'[H1?]]; subst.
        left; repeat eexists.
        by apply: run_done H1 erefl.
      move=> [?[H1]] H2; subst.
      right; do 2 eexists.
      by apply: run_done H2 erefl.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? s4 E F ?; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= D' s2' E' H1 + /and3P[/eqP? _ _]; subst.
      case: ifP => dD'.
        case X: next_alt => //=[E2][?]; subst.
        have [[x [b {}IH]]|[x [b{}IH]]] := IH _ _ _ erefl.
          by have:= is_dead_runb _ dD' IH.
        have [[dE [b3[H4 H5]]]|[dE[?[b3 H4]]]] := expanded_or_complete_fail _ H1; subst.
          have /= := expanded_not_dead _ dE H4; congruence.
        right; do 2 eexists.
        apply: run_backtrack H4 X IH erefl.
      case W: next_alt => [D''|].
        move=>[?]; subst.
        have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
          have {H1} [[dE [b4 [H1 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail _ H1; subst.
            left; repeat eexists; apply: run_backtrack H1 W H erefl.
          congruence.
        have [[dE [b4 [H2 H4]]]|[dE[?[b4 H2]]]] := expanded_or_complete_fail _ H1; subst; try congruence.
        right; case: b4 H2 H4 => /= [|n] H2 H4; subst.
        - repeat eexists; eassumption.
        - by have:= is_ko_runb _ is_ko_cutr H.
      case: ifP => //dE.
      have [[dE' [b4 [H2 H4]]]|[dE'[?[b4 H2]]]] := expanded_or_complete_fail _ H1; try congruence.
      case X: next_alt => //[E''][?]; subst.
      have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
        by have:= runb_dead _ H.
      case: b4 H2 H4 => [|n] /= H2 ?; subst => /=; try by rewrite next_alt_cutr in X.
      have [b4[r [H4 H5]]]:= run_dead_left1 (is_dead_is_ko is_dead_dead) H3; subst.
      have {H2} [[_ ?]?]:= run_consistent _ H H4; subst.
      right; eexists; apply: next_alt_runb X H.
  Qed.

  Lemma run_or_correct_dead {s1 s2 A B}:
    dead_run u s1 A -> dead_run u s2 B -> dead_run u s1 (Or A s2 B).
  Proof.
    move=> HA HB sX C b H.
    have [] := run_or_complete H.
      move=> [x[b1]]; apply: HA.
    move=> [x[b1]]; apply: HB.
  Qed.

  Lemma expandedb_or_is_ko_left_ign_subst {A s B D b2 sIgn1} sIgn2:
    is_ko A -> expandedb u sIgn1 (Or A s B) D b2 ->
      Texists b2, expandedb u sIgn2 (Or A s B) D b2.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => + H.
    elim: H s A B sIgn2 Ho => //=; clear.
    - move=> s s' A A' + s1 B B' sIgn2 ? kB; subst.
      move=> /=; rewrite (is_ko_expand _ kB).
      case: ifP => //dB.
      case X: expand => //[s1' B''][??]; subst.
      have [[??]sB''] := expand_solved_same _ X; subst.
      eexists; apply: expanded_done => /=.
      rewrite dB X//.
    - move=> s A A' + s1 B B' sIgn2 ? kB; subst => /=.
      rewrite (is_ko_expand _ kB).
      case: ifP => dB.
        case X: expand => //[B''][?]; subst.
        have ?:= (expand_failed_same _ X); subst.
        eexists; apply: expanded_fail => /=; rewrite dB X//.
      move=>[?]; subst.
      eexists; apply: expanded_fail => /=; rewrite dB (is_ko_expand)//.
    - move=> s1 s2 r A B b + HB IH s3 C D sIgn2 ? kC; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 r A B b + HB IH s3 C D sIgn2 ? kC; subst => /=.
      case: ifP => dC.
        case X: expand => //=[s3' D'|s3' D'][??]; subst;
        have [b2 {}IH] := IH _ _ _ sIgn2 erefl kC;
        eexists; apply: expanded_step IH; rewrite/=dC X//.
      rewrite is_ko_expand//.
  Qed.

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> runb u sIgn1 (Or A s B) s2 D b2 ->
      Texists b2, runb u sIgn2 (Or A s B) s2 D b2.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => + H.
    elim: H s A B sIgn2 Ho; clear.
    - move=> s s' A B C b H1 ? s2 D E sIgn2 ? H; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 => //= D' s2' E' H1 /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done _ H1.
      move=> [[dD [b1 [H2 ?]]]| [dD[?[b1 H2]]]]; subst.
        have:= is_ko_expanded u s H.
        move=> /(expanded_consistent _ H2) []//.
      rewrite dD.
      have H3 := expanded_or_correct_right _ sIgn2 dD H2.
      eexists.
      apply: run_done H3 _.
      move=> /=; rewrite dD//.
    - move=> s s1 A B C D b1 b2 b3 HA HB HC IH ? s2 E F sIgn2 ? kE; subst.
      have:= expandedb_same_structure _ HA.
      case: B HA HB => //= E' s2' F' HA + /and3P[/eqP? _ _]; subst.
      case: ifP => dE'.
        case X: next_alt => //[F''][?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE  [b4 [H2 H4]]]|[dE [?[b4 H2]]]] := expanded_or_complete_fail _ HA; subst.
          have:= is_ko_expanded u s kE.
          move=> /(expanded_consistent _ H2) [][??]; subst.
          congruence.
        move=> /(_ sIgn2 kE) [b3 IH].
        have H3 := expanded_or_correct_right_fail _ dE H2 sIgn2.
        eexists; apply: run_backtrack H3 _ IH erefl.
        move=> /=; rewrite dE X//.
      case X: next_alt => //[E''|].
        move=>[?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE [H1 [b3 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail _ HA; subst; [|congruence].
        have:= is_ko_expanded u s kE.
        move=> /(expanded_consistent _ b3) [][??]; subst.
        rewrite (is_ko_next_alt)// in X.
      case: ifP => //dF'.
      case W: next_alt => //[F''][?]; subst.
      have [b3{}IH] := IH _ _ _ sIgn2 erefl (is_dead_is_ko is_dead_dead).
      have [[dE [H [b4 H1]]]|[dE [?[b4 H1]]]] := expanded_or_complete_fail _ HA; subst; [|congruence].
      have:= is_ko_expanded u s kE.
      move=> /(expanded_consistent _ b4) [][??]; subst.
      simpl in H1; subst.
      have [b5 H2] := expandedb_or_is_ko_left_ign_subst sIgn2 kE HA.
      eexists.
      apply: run_backtrack H2 _ IH erefl; rewrite/= dE X dF' W//.
  Qed.

  Fixpoint has_bt A B :=
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
  Qed.

  Lemma expandedb_has_bt {s A r b}:
    expandedb u s A r b -> has_bt A (get_state_exp r) = false.
  Proof.
    elim; clear.
    - move=> s s' A A' /expand_solved_same [[??]sA]; subst; rewrite/=has_bt_id//.
    - move=> s A B /expand_failed_same [? fB]; subst; rewrite/=has_bt_id//.
    - move=> s s' r A B b HA HB H. apply: has_bt_trans (expand_has_bt HA) H.
      apply: expand_same_structure HA. apply: expandedb_same_structure HB.
    - move=> s s' r A B b HA HB H. apply: has_bt_trans (expand_has_bt HA) H.
      apply: expand_same_structure HA. apply: expandedb_same_structure HB.
  Qed.

  Lemma run_and_correct {s0 sn A B0 B r b}:
    runb u s0 (And A B0 B) sn r b ->
    (Texists sm r1 b1, runb u s0 A sm r1 b1).
  Proof.
    remember (And _ _ _) as a eqn:Ha => H.
    elim: H A B0 B Ha; clear.
    - move=> s1 s2 ? r C b HA _ A B0 B ?; subst.
      have /= := expandedb_same_structure _ HA.
      case: r HA => //= A' B0' B' + _.
      move=> /expanded_and_complete [s''[b1[b2[A''[HA [HB [? Hz]]]]]]]; subst.
      repeat eexists.
      apply: run_done HA erefl.
    - move=> s1 s2 ? Ign C r b1 b2 b3 HA HB HC IH ? A B0 B ?; subst.
      have /= := expandedb_same_structure _ HA.
      case: Ign HA HB => //= A' B0' B'.
      move=> /expandes_and_fail [[HA [??]]|[s'[b3[b4[A''[HA [HB[? [Hz Hw]]]]]]]]]; subst.
        have fA':= expandedb_failed _ HA.
        rewrite fA'.
        case: ifP => //dA.
        case X: next_alt => //[A''].
        case W: next_alt => //[B0''][?]; subst.
        have {IH} [sm[r1[b3 H]]] := IH _ _ _ erefl.
        move=> _.
        repeat eexists; apply: run_backtrack HA X H erefl.
      have sA'':= expanded_Done_success _ HA.
      case: ifP => //dA.
      case: b4 HB Hz Hw => //= [|n] HB Hz Hw; subst.
        rewrite success_failed sA''//.
        case X: next_alt => //[B''|].
          move=>[?] _ ; subst.
          have {IH}[sm[r1[b1 IH]]] := IH _ _ _ erefl.
          repeat eexists.
          apply: run_done HA erefl.
        case Y: next_alt => //=[A'''].
        case W: next_alt => //=[B0'][?] _; subst.
        have {IH}[sm[r1[b1 IH]]] := IH _ _ _ erefl.
        repeat eexists.
        apply: run_done HA erefl.
      have := sA''.
      rewrite -success_cut => SA''.
      rewrite success_failed SA''//.
      case X: next_alt => //[B''|].
        move=> [?] _; subst.
        have {IH}[sm[r1[b1 IH]]] := IH _ _ _ erefl.
        by repeat eexists; apply: run_done HA erefl.
      rewrite next_alt_cutl//.
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
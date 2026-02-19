From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop elpi elpi_equiv elpi_prop run_prop_hard.
From det Require Import valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Fixpoint a2t_ l :=
  match l with
  | nilA => Bot
  | consA (s1, x) t =>
    Or KO s1 (Or (gs2t_ x) empty (a2t_ t))
  end
with gs2t_ l :=
  match l with
  | nilG => Top
  | consG x xs => 
    let tl := gs2t_ xs in
    match (g2t_ x) with
    | (x, None) => And x tl tl 
    | (x, Some bt) => 
        let bt' := (Or Top empty bt) in
        let tl' := And bt' Top tl in
        And x tl' tl'
    end
  end
with g2t_ l :=
  match l with
  | cut ca => (CutS, Some (a2t_ ca))
  | call p t => (CallS p t, None)
  end.

Fixpoint of_goals l :=
  match l with
    | [::] => nilC
    | cut l :: xs => (cut l) ::: (of_goals xs)
    | (call _ _ as hd) :: xs => hd ::: (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => -nilCA
  | x :: xs => (empty, of_goals x) ::: (of_alt xs)
  end.

Section s.
  Variable p : program.
  Variable c1 : Callable.
  Variable c2 : Callable.
  Variable A B C D E F : Callable.
  Variable s : Sigma.
  Definition c := call p (c1).
  Definition q := call p (c2).

  Goal exists x, (a2t_ ((s, (c ::: (q:::nilC))) ::: nilC)) = x.
  Proof. move=> /=. Admitted.

  Goal exists x, a2t_ ((s, (c ::: nilC)) ::: ((s, (q ::: nilC)) ::: nilA)) = x.
  Proof. move=> /=. Admitted.

  Goal
  (* original is (((! \/ A) \/ B)) /\ (D) *)
  (* produced is ((bot \/ !D) \/ AC) \/ BC *)
    exists x, 
    let f x := (CallS p x) in
      a2t_ ((of_alt [:: 
        [::cut (of_alt [:: [:: call p B; call p C]]); call p D];
        [:: call p A; call p C]; 
        [:: call p B; call p C]])) = x.
  Proof.
    simpl of_alt.
    move=>/=.
    set X:= And _ _ Top.
    set Y:= And _ _ X.
    set Z:= Or _ _ KO.
    set W:= And _ _ Top.
    set T:= And _ _ W.
  Abort.

  Goal
  (* original (OK \/ A) /\_B OK *)
  (* produces is : (KO \/ Top) \/ AB *)
  let f x := (CallS p x) in
  a2t_ (of_alt [::[::]; [::call p A; call p B]]) = 
    Or KO empty
  (Or Top empty
     (Or KO empty
        (Or
           (And (CallS p A) (And (CallS p B) Top Top)
              (And (CallS p B) Top Top))
           empty KO))) .
  Proof.
    move=>/=.
    set X:= And _ _ Top.
    set Y:= And _ _ X.
    set Z:= Or _ _ KO.
    move=>//.
  Qed.
End s.

(* Fixpoint a2t_right_most_cat T1 T2 :=
  match T1 with
  | Or X s1 Y => Or X s1 (a2t_right_most_cat Y T2)
  | X => Or X empty T2
  end. *)


(* Lemma a2t_cat {L1 L2}:
  a2t_ (L1 ++ L2) = if L1 == nilC then (a2t_ L2) else a2t_right_most_cat (a2t_ L1) (a2t_ L2).
Proof.
  elim: L1 L2 => //[[s g]gs IH] L2.
  fConsA (s, g) gs.
  rewrite cat_cons/=.
  f_equal.
  case: gs.

  - fNilA; rewrite cat0s/=.
  - move=> /=. *)
  

Lemma step_a2t {u ign1 L}: 
  step u ign1 (a2t_ L) = Failed (a2t_ L).
Proof. case: L => //=-[]//. Qed.

Lemma expanded_a2t u ign1 L:
  expandedb u ign1 (a2t_ L) (Failed (a2t_ L)) false.
Proof. case: L => [|[s g]gs]/=; constructor => //. Qed.

Lemma run_a2t_ign {u s2 D b2 sIgn1 L} sIgn2:
  run u sIgn1 (a2t_ L) s2 D b2 ->
    Texists b2, run u sIgn2 (a2t_ L) s2 D b2.
Proof.
  case: L => //=.
    move=> /is_ko_run -/(_ isT)//.
  move=> [s g]gs.
  set X:= (Or _ empty _); generalize X; clear X => X H.
  apply: run_or_is_ko_left_ign_subst _ H => //.
Qed.

Lemma run_success_add_ca_deep {u s s1 B D bt bt1 res b}:
  success B ->
    run u s1 (a2t_ (state_to_list B s bt)) res D b ->
    Texists D0 b0,
      run u s1 (a2t_ (add_ca_deep bt1 (state_to_list B s bt))) res D0 b0 .
Proof.
  elim: B s s1 D bt bt1 res b => //=.
  - move=> s s1 D _ _ res b _.
    do 2 eexists; eassumption.
  - move=> A HA s0 B HB s s1 C bt bt1 res b.
    case: ifP => [dA sB|dA sA].
      rewrite state_to_list_dead//.

Admitted.

Lemma run_a2t_success {C} u s1 bt:
  success C ->
  Texists D b2, run u s1 (a2t_ (state_to_list C s1 bt)) (next_substS s1 C) D b2.
Proof.
  elim: C s1 bt => //=.
  - move=> s1 _; do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_fail => //.
    - move=> //=.
    - apply: StopT => //.
    - apply: expanded_step => //.
      apply: expanded_done => //.
  - move=> A HA s B HB s1 bt.
    case: ifP => [dA sB | dA sA].
    - rewrite state_to_list_dead//cat0s.
      have {HB HA} [D[b2]]:= HB s nilC sB; clear -sB.
      move=> /(run_a2t_ign s1) [b3 H].
      apply: run_success_add_ca_deep sB H.
    - rewrite add_ca_deep_cat.
      admit.
  - move=> A HA B0 _ B HB.
Admitted.

Lemma run_a2t_expandedb {u s A s' B b bt}:
  valid_state A ->
  expandedb u s A (Done s' B) b ->
    Texists C b2,
    run u s (a2t_ (state_to_list A s bt)) s' C b2.
Proof.
  remember (Done _ _) as d eqn:Hd => +H.
  elim: H s' B Hd; clear => //=.
  - move=> s1 s2 A B HA s3 C [??]vA; subst.
    have [[??] sC]:= step_success _ HA; subst.
    apply: run_a2t_success sC.
  - move=> s1 s2 r A B b HA HB IH s3 C ? vA; subst.
    have /=vB := valid_state_step _ vA HA.
    have {IH} := IH _ _ erefl vB.
    have [x[tl[H1 [H2 H3]]]]:= s2l_CutBrothers _ s1 bt vA HA.
    rewrite H1 H2/=.
    move=> [C1[b2 IH]].
    inversion IH; subst; clear IH.
      inversion H => //.
    inversion H; subst; clear H => //.
    move: H8 => //[?]; subst.
    move: H0 => /=; rewrite andbF; case: ifP => //dx.
    case X: prune => //[x'][?]; subst.
    have [H5 H6]:= step_cb_same_subst1 _ vA HA; subst.
    have:= run_dead_left1 _ _ H4 => /= /(_ isT) [b1[r' [Hx Hy]]].
    do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_fail => //.
    - rewrite //.
    - apply: run_dead_left2 is_dead_dead _.
      apply: run_or_correct_left.
      admit.
  - move=> s1 s2 r A B b HA HB IH s3 C ? vA; subst.
    have [D[b2 {}IH]]:= IH _ _ erefl (valid_state_step _ vA HA).
    admit.
Admitted.

Inductive equiv_run : state -> state -> Prop :=
  | equiv_run_fail u s A B : dead_run u s A -> dead_run u s B -> equiv_run A B
  | equiv_run_success u s1 s2 A B A' B' b1 b2 :
    run u s1 A s2 (Some A') b1 -> run u s1 B s2 (Some B') b2 -> equiv_run A' B' -> equiv_run A B.

Lemma xx u s1 s2 A B b1: 
  valid_state A ->
  run u s1 A s2 B b1 -> 
    Texists C b2, run u s1 (a2t_ (state_to_list A s1 nilC)) s2 C b2. (*/\ equiv_run B C*)
Proof.
  move=> +H; elim: H; clear.
  - move=> s s' A B C b HA HB vA.
    apply: run_a2t_expandedb vA HA.
  - move=> s1 s2 A B C r b1 b2 b3 HA HB HC IH ? vA; subst.
    have /= vB := valid_state_expanded _ vA HA.
    have vC := valid_state_prune vB HB.
    have [r'[bx {}IH]]:= IH vC.
    repeat eexists.
    apply: run_backtrack IH erefl.
Admitted.


Lemma zz u s1 s2 A B b1 bt: 
  valid_state A ->
  run u s1 A s2 B b1 -> 
    Texists C b2, run u s1 (a2t_ (state_to_list A s1 bt)) s2 C b2. (*/\ equiv_run B C*)
Proof.
  elim: A B s1 s2 b1 bt => //=.
  - by repeat eexists; eauto.
  - move=> B s1 s2 b1 bt _ H.
    inversion H; subst.
      inversion H0 => //; subst.
      case: H6 => ??; subst.
      repeat eexists.
      apply: run_backtrack erefl.
        apply: expanded_fail => //.
        move=> //.
      apply : StopT erefl.
      apply: expanded_step => //=.
      apply: expanded_done => //=.
    inversion H0 => //.
  - move=> B s1 s2 b1 bt _ H.
    inversion H; subst; last first.
      inversion H0 => //; subst.
      case: H3 => ??; subst.
      inversion H4 => //.
    inversion H0 => //; subst.
    case: H1 => ??; subst.
    inversion H2; subst => //.
    case: H7 => ??; subst.
    repeat eexists.
    apply: run_backtrack erefl.
      apply: expanded_fail => //.
      move=>//.
    apply: StopT => //.
    apply: expanded_step => //.
    apply: expanded_done => //.
  - move=> p c r s1 s2 b bt _ H.
    repeat eexists.
    apply: run_backtrack erefl.
      apply: expanded_fail => //.
      by [].
    apply: run_dead_left2 => //.
    apply: run_or_ko_right1 => //.
    admit. (*OK by applying an aux lemma on And*)
  - move=> B s1 s2 b1 _ H; repeat eexists.
    apply: run_backtrack.
      apply: expanded_fail => //.
      move=> //.
      apply: run_dead_left2 is_dead_dead _.
      apply: run_or_ko_right1 => //.
      (*OK by applying an aux lemma on And (the one used in admit before)*)
      admit.
    move=> //.
  - move=> A HA s B HB C s1 s2 b1 bt.
    case: ifP => [dA vB|dA/andP[vA bB]].
      move=>/(run_dead_left1 _ (is_dead_is_ko dA)) [b2 [r'[H1 H2]]].
      have {HA HB}[D[b3 H3]] := HB _ _ _ _ nilC vB H1.
      rewrite state_to_list_dead//.
      admit.
    rewrite add_ca_deep_cat.
    admit.
  - move=> A HA B0 _ B HB C s1 s2 b1 /and5P[_ vA _ ].
  (* OLD PROOF *)
  (* move=> +H; elim: H; clear.
  - move=> s s' A B C b HA HB vA.
    apply: run_a2t_expandedb vA HA.
  - move=> s1 s2 A B C r b1 b2 b3 HA HB HC IH ? vA; subst.
    have /= vB := valid_state_expanded _ vA HA.
    have vC := valid_state_prune vB HB.
    have [r'[bx {}IH]]:= IH vC.
    repeat eexists.
    apply: run_backtrack IH erefl. *)
Admitted.
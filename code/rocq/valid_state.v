From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Import Run.

  Fixpoint full_expanded (s : state) :=
    match s with
    | KO | OK => true
    | Top | Goal _ _ | Bot => false
    | And l _ r => full_expanded l && full_expanded r
    | Or l s r => full_expanded l && full_expanded r
    end.

  Fixpoint some_expanded (s : state) :=
    match s with
    | KO | OK => true
    | Top | Goal _ _ | Bot => false
    | And l _ r => some_expanded l || some_expanded r
    | Or l s r => some_expanded l
    end.

  Fixpoint base_and s :=
    match s with
    | And (Goal _ _) r r1 => (r == r1) && base_and r (* should also say something about the program *)
    | Top => true
    | _ => false
    end.

  Fixpoint base_or_aux s :=
    match s with
    | Or l _ r => base_and l && (base_or_aux r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and t
    end.

  Definition base_or s := (s == Bot) || (base_or_aux s).

  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Bot | Top => true
    | Or l _ r =>
      if full_expanded l then (valid_state r || failed r)
      else valid_state l && (base_or r || failed r)
    | And l r0 r => 
      valid_state l && if some_expanded r then valid_state r else (((r == r0) && base_and r))
    end.

  Inductive expandedP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
  | expandedP_done {s s' A B}  : F A -> F B -> expand s A = Solved s' B   -> expandedP s A (Done s' B)
  | expandedP_fail {s A B}     : F A -> F B -> expand s A = Failure B     -> expandedP s A (Failed B)
  | expandedP_cut {s s' A B}   : F A -> F B -> expand s A = CutBrothers B -> expandedP s B s' -> expandedP s A s'
  | expandedP_step {s s' A B}  : F A -> F B -> expand s A = Expanded B    -> expandedP s B s' -> expandedP s A s'.

  Inductive runP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
    | runP_done {s s' A B}            : F A -> F B -> expandedP F s A (Done s' B) -> runP s A (Done s' B)
    | runP_fail {s A B}               : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B = None -> runP s A (Failed B)
    | runP_backtrack {s s' s'' A B C} : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B = Some (s', C) ->  runP s' C s'' -> runP s A s''.

  Lemma full_expanded_cut A: full_expanded (cut A).
  Proof. 
    elim: A => //.
    + by move=> A HA s B HB //=; rewrite HA HB.
    + by move=> A HA B HB C HC => //=; rewrite HA HC.
  Qed.

  Lemma full_expanded_some_expanded {A} : full_expanded A -> some_expanded A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB //= /andP [] /HA.
    + by move=> A HA B HB C HC /= /andP [] HV _; rewrite (HA HV). 
  Qed.

  Lemma valid_cut_cut {B}: valid_state (cut B).
  Proof. 
    elim: B => //=. 
    + by move=> A HA _ B HB; rewrite full_expanded_cut HB.
    + move=> A HA B HB C HC; rewrite HA HC.
      by rewrite (full_expanded_some_expanded (full_expanded_cut C)).
  Qed.

  Lemma full_expanded_solved {s s' A B}: expand s A = Solved s' B -> full_expanded A -> full_expanded B.
  Proof.
    elim: A s s' B => //; clear.
    + by move=> s s' B; rewrite /expand => -[] /[subst2].
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [A' [HA']] /[subst1] //= /andP [].
      by move=> /(HA _ _ _ HA') -> ->.
    + move=> A HA A0 _ B HB s s' C /simpl_expand_and_solved [s2 [A' [B' [EA [EB]]]]] /[subst1] /= /andP [FA FB].
      by rewrite (HA _ _ _ EA FA) (HB _ _ _ EB FB).
  Qed.

  Lemma full_expanded_failure {s A B}: expand s A = Failure B -> full_expanded A -> full_expanded B.
  Proof.
    elim: A s B => //; clear.
    + by move=> s B; rewrite /expand => -[] /[subst2].
    + by move=> A HA s B HB s1 C /simpl_expand_or_fail [A' [HA']] /[subst1] //= /andP [] /(HA _ _ HA') -> ->.
    + move=> A HA A0 _ B HB s C /simpl_expand_and_fail [].
      + move=> [A' [EA]] /[subst1] /= /andP [FA FB].
        by rewrite (HA _ _ EA FA) FB.
      + move=> [s' [A' [B' [EA [EB]]]]] /[subst1] //= /andP [] FA FB.
        by rewrite (HB _ _ EB FB) (full_expanded_solved EA FA).    
  Qed.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA; rewrite (HVA HA) /=.
    by case some_expanded => //; rewrite HA eq_refl.
  Qed.

  Lemma base_or_aux_base_or {B}: base_or_aux B -> base_or B.
  Proof. case B => //. Qed.

  Lemma base_and_big_and {pr A}: base_and (big_and pr A).
  Proof. by elim: A => // a l /= ->; rewrite eq_refl. Qed.

  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof. by elim: l => // x xs /= ->; rewrite eq_refl base_and_big_and; case some_expanded. Qed.

  Lemma base_or_aux_big_and {pr l} : base_or_aux (big_and pr l).
  Proof. 
    by elim: l => //= _ ??; rewrite eq_refl base_and_big_and.
  Qed.

  Lemma base_or_big_and {pr l} : base_or (big_and pr l).
  Proof.
    case: l; rewrite /base_or // => ??.
    by rewrite base_or_aux_big_and.
  Qed.

  Lemma base_or_aux_big_or_aux {pr s l}: base_or_aux (big_or_aux pr s l).
  Proof. 
    elim: l s.
    + move=> s; apply base_or_aux_big_and.
    + by move=> [] s R l H r1 //=; rewrite H base_and_big_and.
  Qed.

  Lemma base_or_big_or_aux {pr s l}: base_or (big_or_aux pr s l).
  Proof.
    case: l => //=.
    + by rewrite base_or_big_and.
    + by move=> [] s' R l; rewrite /base_or/= base_and_big_and base_or_aux_big_or_aux.
  Qed.

  Lemma base_or_valid {A} : base_or A -> valid_state A.
  Proof.
    elim A => //; clear.
    + move=> A HA s B HB; rewrite /base_or => /orP [] //= /andP [] /base_and_valid ->.
      move=> H; move: (H) => /base_or_aux_base_or /HB ->; case full_expanded => //=.
      case: B H {HB} => //=.
      + by move=> ??? /andP [] H1 H2; rewrite /base_or /= H1 H2.
      + by move=> [] //= p a s1 s2 /andP [] H1 H2; rewrite /base_or/= H1 H2.
    + move=> A HA B HB C HC; rewrite /base_or => /orP []//=; case: A HA => //.
      move=> p a H /andP [] /eqP -> H1 ; move:(H1) ->; move: H1 => /base_and_valid ->; rewrite eq_refl.
      case: some_expanded => //.
  Qed.

  Lemma some_expanded_solved {s s' A A'}:
    expand s A = Solved s' A' -> some_expanded A'.
  Proof.
    elim: A s s' A' => //.
    + by move=> s s' A [] /[subst2].
    + by move=> s s' A [] /[subst2].
    + by move=> p [].
    + move=> A IHA s B IHB s1 s2 C.
      move=> /simpl_expand_or_solved [A' [HA]] /[subst1] /=.
      by have:= (IHA _ _ _ HA).
    + move=> A IHA B0 _ B IHB s1 s2 C /simpl_expand_and_solved [s' [A'[B'[HA[HB]]]]] /[subst1] /=.
      by rewrite (IHA _ _ _ HA).
  Qed.

  Lemma some_expanded_failure {s A A'}:
    expand s A = Failure A' -> some_expanded A'.
  Proof.
    elim: A s A' => //.
    + by move=> s A [] /[subst1].
    + by move=> s A [] /[subst1].
    + by move=> p [].
    + move=> A IHA s B IHB s1 C.
      move=> /simpl_expand_or_fail [A' [HA]] /[subst1] /=.
      by have:= (IHA _ _ HA).
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_fail [].
      + move=> [A' [HA]] /[subst1] /=.
        by rewrite (IHA _ _ HA).
      + move=> [s2 [A' [B' [EA [EB]]]]] /[subst1] /=.
        by rewrite (IHB _ _ EB) orbT.
  Qed.

  Lemma some_expanded_cb {s A A'}:
    expand s A = CutBrothers A' -> some_expanded A'.
  Proof.
    elim: A s A' => //.
    + by move=> p [] //= ?? -[] /[subst1].
    + move=> A IHA s B IHB s1 C.
      by move=> /simpl_expand_or_cut.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_cut [].
      + move=> [A' [HA]] /[subst1] /=.
        by rewrite (IHA _ _ HA).
      + move=> [s2 [A' [B' [EA [EB]]]]] /[subst1] /=.
        by rewrite (IHB _ _ EB) orbT.
  Qed.

  Lemma some_expanded_big_or {p s a}: some_expanded (big_or p s a).
  Proof.
    by elim: a s => //; rewrite /big_or; move=> *; case: F => // -[] //.
  Qed.


  Lemma some_expanded_expanded {s A A'}:
    expand s A = Expanded A' -> some_expanded A'.
  Proof.
    elim: A s A' => //.
    + move=> p [] // [] /= ???.
      + move=> [] /[subst1]; apply: some_expanded_big_or.
      + move=> [] /[subst1]; apply: some_expanded_big_or.
      + move=> ? [] /[subst1]; apply: some_expanded_big_or.
    + move=> A IHA s B IHB s1 C /= /simpl_expand_or_expanded [].
      + move=> [A' [HA]] /[subst1] /=; apply: IHA HA.
      + move=> [A' [HA]] /[subst1] /=; apply: some_expanded_cb HA.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_expanded [].
      + move=> [A' [HA]] /[subst1] /=.
        by rewrite (IHA _ _ HA).
      + move=> [s2 [A' [B' [EA [EB]]]]] /[subst1] /=.
        by rewrite (some_expanded_solved EA).
  Qed.

  Lemma valid_state_solved {s s' A A'}:
    expand s A = Solved s' A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s s' A' => //.
    + by move=> s s' A [] /[subst2].
    + move=> s s' A //= [] /[subst2] //=. 
    + by move=> pr [] => //= t s s' A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 s2 C.
      move=> /simpl_expand_or_solved [A' [HA]] /[subst1] /=.
      case F: full_expanded.
      + by move=> VA; rewrite (full_expanded_solved HA F).
      + move=> /andP [VA] /orP [] H.
        + by rewrite H (IHA _ _ _ HA VA) (base_or_valid H); case full_expanded.
        + rewrite H (IHA _ _ _ HA VA) 2!orbT; case full_expanded => //.
    + move=> A IHA B0 _ B IHB s1 s2 C /simpl_expand_and_solved [s' [A'[B'[HA[HB]]]]] /[subst1] /=.
      move=> /andP [] VA; rewrite (IHA _ _ _ HA VA); case X: some_expanded.
      + move=> VB; rewrite (IHB _ _ _ HB VB).
        by rewrite (some_expanded_solved HB).
      + move=> /andP [] /eqP <-.
        move=> H; have:=H => /base_and_valid /(IHB _ _ _ HB) ->.
        by rewrite (some_expanded_solved HB).
  Qed.

  Lemma valid_state_failure {s A A'}:
    expand s A = Failure A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> s A [] /[subst2].
    + move=> s A //= [] /[subst2] //=. 
    + by move=> pr [] => //= t s A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 C.
      move=> /simpl_expand_or_fail [A' [HA]] /[subst1] //=.
      case F: full_expanded.
      + by rewrite (full_expanded_failure HA F) => ->.
      + move=> /andP [] /(IHA _ _ HA) -> H.
        have: valid_state B || failed B.
        by move: H => /orP [] H; rewrite ?H ?orbT ?(base_or_valid H).
        by move: H => -> ->; case full_expanded.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_fail [].
      + move=> [A' [HA]] /[subst1] //= /andP [] VA VB.
        by rewrite (IHA _ _ HA VA).
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] VA.
        rewrite (valid_state_solved HA VA) => {HA VA}.
        rewrite (some_expanded_failure HB).
        case X: some_expanded.
        + by move=> /(IHB _ _ HB) ->.
        + by move=> /andP [] _ /base_and_valid /(IHB _ _ HB) ->.
  Qed.

  Lemma valid_state_cb {s A A'}:
    expand s A = CutBrothers A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> pr [] => //= t s [] /[subst1].
    + move=> A IHA s B IHB s1 C.
      by move=> /simpl_expand_or_cut.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_cut [].
      + by move=> [A' [HA]] /[subst1] //= /andP [] /(IHA _ _ HA) -> ->.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /(valid_state_solved HA) ->.
        rewrite (some_expanded_cb HB).
        case X: some_expanded.
        + by move=> /(IHB _ _ HB) ->.
        + by move=> /andP [] _ /base_and_valid /(IHB _ _ HB).
  Qed.

  Lemma full_expanded_big_and {pr l}:
    full_expanded (big_and pr l) = false.
  Proof. elim: l => //. Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    case: l => [|[]] //=; rewrite valid_state_big_and // full_expanded_big_and.
    move=> _ r l.
    by rewrite base_or_big_or_aux.
  Qed.

  Lemma valid_state_big_or {pr s t} : valid_state (big_or pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + by move=> ?; case: F => //= -[] //=???; rewrite valid_state_big_or_aux.
    + by move=> ?; case: F => //= -[] //=???; rewrite valid_state_big_or_aux.
    + by move=> ??; case F => //= -[] //=???; rewrite valid_state_big_or_aux.
  Qed. 

  Lemma full_expanded_cb {s1 A A'} : 
    expand s1 A = CutBrothers A' -> full_expanded A -> full_expanded A'.
  Proof.
    elim: A A' s1 => //.
    + move=> A HA s B HB A' ? /simpl_expand_or_cut [].
    + move=> A HA B0 HB0 C HC D s /simpl_expand_and_cut [].
      + by move=> [A2[H]] /[subst1] /= /andP [] /(HA _ _ H) -> ->.
      + by move=> [s1[A1[A2[H[H1]]]]] /[subst1] /= /andP [] /(full_expanded_solved H) -> /(HC _ _ H1) ->.
  Qed.

  Lemma full_expanded_expanded {s1 A A'} : 
    expand s1 A = Expanded A' -> full_expanded A -> full_expanded A'.
  Proof.
    elim: A A' s1 => //.
    + move=> A HA s B HB A' ? /simpl_expand_or_expanded [].
      + by move=> [A2 [H]] /[subst1] //= /andP [] /(HA _ _ H) -> ->.
      + move=> [A2 [H]] /[subst1] //= /andP [] /(full_expanded_cb H) ->.
        by rewrite full_expanded_cut.
    + move=> A HA B0 HB0 C HC D s /simpl_expand_and_expanded [].
      + by move=> [A2[H]] /[subst1] /= /andP [] /(HA _ _ H) -> ->.
      + by move=> [s1[A1[A2[H[H1]]]]] /[subst1] /= /andP [] /(full_expanded_solved H) -> /(HC _ _ H1) ->.
  Qed.

  Lemma failed_cut {B}: failed (cut B).
  Proof. elim: B => //=.
    + by move=> ? H ?? H1; rewrite H H1.
    + by move=> ? H ? H1 ? H2; rewrite H H2.
  Qed.

  Lemma valid_state_expanded {s A A'}:
    expand s A = Expanded A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> pr [] => //= t s ? [] /[subst1]; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 C.
      move=> /simpl_expand_or_expanded [].
      + move=> [A' [H]] /[subst1] /=.
        case F: full_expanded => //=.
        + by rewrite (full_expanded_expanded H).
        + move=> /andP [] VA H1; rewrite (IHA _ _ H VA).
          have HH: valid_state B || failed B.
            by move: H1 => /orP [] H1; rewrite ?H1 ?orbT // (base_or_valid H1).
          by rewrite HH H1; case full_expanded.
      + move=> [A' [H]] /[subst1] /=.
        case F: full_expanded => //=.
        + by rewrite (full_expanded_cb H F) valid_cut_cut.
        + by move=> /andP [] VA H1; rewrite (valid_state_cb H VA) valid_cut_cut failed_cut !orbT; case full_expanded.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_expanded [].
      + by move=> [A' [HA]] /[subst1] //= /andP [] /(IHA _ _ HA) -> ->.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /(valid_state_solved HA) ->.
        rewrite (some_expanded_expanded HB).
        case X: some_expanded.
        + by move=> /(IHB _ _ HB) ->.
        + by move=> /andP [] _ /base_and_valid /(IHB _ _ HB) H; rewrite H.
  Qed.

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> expandedP valid_state s A r.
  Proof.
    move=> + H; elim H; clear.
    + move=> s1 s2 A1 A2 EA VA.
      apply: expandedP_done => //.
      apply: valid_state_solved EA VA.
    + move=> s A B HA HB.
      apply: expandedP_fail => //.
      apply: valid_state_failure HA HB.
    + move=> s s' A B HA HB IH VA.
      have VB:= valid_state_cb HA VA.
      apply: expandedP_cut (VA) VB (HA) (IH VB).
    + move=> s s' A B HA HB IH VA.
      have VB:= valid_state_expanded HA VA.
      apply: expandedP_step (VA) VB (HA) (IH VB).
  Qed.

  Lemma valid_state_expanded_done {s1 s2 A B}:
    valid_state A ->  expanded s1 A (Done s2 B) -> valid_state B.
  Proof.
    remember (Done _ _) as D eqn:HD => + H.
    elim: H s2 B HD => //; clear.
    + move=> s1 s2 A B HA s3 C [] /[subst2].
      apply: valid_state_solved HA.
    + move=> s1 s2 A B HA HB + s3 C ? /(valid_state_cb HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
    + move=> s1 s2 A B HA HB + s3 C ? /(valid_state_expanded HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
  Qed.

  Lemma valid_state_expanded_failed {s1 A B}:
    valid_state A ->  expanded s1 A (Failed B) -> valid_state B.
  Proof.
    remember (Failed _) as D eqn:HD => + H.
    elim: H B HD => //; clear.
    + move=> s1 A B HA s3 [] /[subst1].
      apply: valid_state_failure HA.
    + move=> s1 s2 A B HA HB + C ? /(valid_state_cb HA) VB /[subst].
      by move=> /(_ _ erefl VB).
    + move=> s1 s2 A B HA HB + C ? /(valid_state_expanded HA) VB /[subst].
      by move=> /(_ _ erefl VB).
  Qed.
  
  (* Lemma full_expanded_next_alt_aux {b s1 s2 A B}:
    full_expanded A -> next_alt_aux b s1 A = Some (s2, B) -> full_expanded B.
  Proof.
    elim: A b s1 s2 B => //.
    + move=> A HA s B HB b s1 s2 C /= /andP [] FA FB.
      by case NA: next_alt_aux => [[ ] | ] [] /[subst2] /=; rewrite ?FB// (HA _ _ _ _ FA NA).
    + move=> A HA B0 HB0 B HB b s1 s2 C /=/andP [] FA FB.
      case NB: next_alt_aux => [[  ] | ].
      + by move=> [] /[subst2] /=; move: (HB _ _ _ _ FB NB) ->; rewrite FA.
      + case NA: next_alt_aux => // [[]] [] /[subst2] /=.
        rewrite (HA _ _ _ _ FA NA).
        case X: eq_op.
        move: X => /eqP ->; rewrite fulle. *)

  Lemma valid_state_next_alt {s s' b A B} : next_alt_aux b s A = Some (s', B) -> valid_state A -> valid_state B.
  Proof.
    elim: A b s s' B => //.
    + by move=> [] ??? // [] /[subst2].
    + by move=> [] ??? // [] /[subst2].
    + by move=> ? [|?] [] // ??? -[] /[subst2].
    + move=> A HA s B HB b s1 s2 C /=.
      case F: next_alt_aux => [[ ]| ] [] /[subst2].
  Admitted.


  Lemma runP_run {s A r}:
    valid_state A -> run s A r -> runP valid_state s A r.
  Proof.
    move=> + H; elim H; clear.
    + move=> s1 s2 A B EA VA.
      have:= expandedP_expanded VA EA => H.
      have ?:= valid_state_expanded_done VA EA.
      apply: runP_done => //.
    + move=> s A B HA HB VA.
      have:= expandedP_expanded VA HA => H.
      have VS := valid_state_expanded_failed VA HA.
      apply: runP_fail => //.
    + move=> s s' r A B C HA HB HC IH VA.
      have EA := expandedP_expanded VA HA.
      have VB := valid_state_expanded_failed VA HA.
      have NA := valid_state_next_alt HB VB.
      apply: runP_backtrack VA VB EA HB (IH NA).
  Qed.

End valid_state.
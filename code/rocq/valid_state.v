From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Import Run.
  

  Lemma failed_cut {A}: failed (cut A).
  Proof.
    elim: A => //=.
    (* + by move=> A HA _ B HB. ; rewrite HA HB. *)
    + by move=> A HA B HB C HC; rewrite HA.
  Qed.

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
    | And (Goal _ _) r r1 => (r == r1) && base_and r1 (* should also say something about the program *)
    | Top => true
    | _ => false
    end.

  Fixpoint base_or_aux s :=
    match s with
    | Or l _ r => base_and l && (base_or_aux r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and t
    end.

  Definition base_or s := (s == Bot) || (base_or_aux s).


  Fixpoint base_and_ko s :=
    match s with
    | And KO r r1 => (r == r1) && base_and_ko r1 (* should also say something about the program *)
    | KO => true
    | _ => false
    end.

  Fixpoint base_or_ko_aux s :=
    match s with
    | Or l _ r => base_and_ko l && (base_or_ko_aux r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and_ko t
    end.

  Definition base_or_ko s := (s == KO) || (base_or_ko_aux s).

  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Bot | Top => true
    | Or l _ r =>
      valid_state l && 
      (* if failed l then valid_state r
      else  *)
      (base_or r || base_or_ko r)
    | And l r0 r => 
      (base_and r0 || base_and_ko r0) &&
      valid_state l && if success l then valid_state r else ((r0 == r))
    end.

  Inductive expandedP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
  | expandedP_done {s s' A B}  : F A -> F B -> expand s A = Solved s' B   -> expandedP s A (Done s' B)
  | expandedP_fail {s A B}     : F A -> F B -> expand s A = Failure B     -> expandedP s A (Failed B)
  | expandedP_cut {s s' A B}   : F A -> F B -> expand s A = CutBrothers B -> expandedP s B s' -> expandedP s A s'
  | expandedP_step {s s' A B}  : F A -> F B -> expand s A = Expanded B    -> expandedP s B s' -> expandedP s A s'.

  Inductive runP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
    | runP_done {s s' A B}            : F A -> F B -> expandedP F s A (Done s' B) -> runP s A (Done s' B)
    | runP_fail {s A B}               : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B None -> runP s A (Failed B)
    | runP_backtrack {s s' s'' A B C} : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B (Some (s', C)) ->  runP s' C s'' -> runP s A s''.

  Lemma full_expanded_cut A: full_expanded (cut A).
  Proof. 
    elim: A => //.
    + by move=> A HA s B HB //=; rewrite HA HB.
    + by move=> A HA B HB C HC => //=; rewrite HA HC.
  Qed.

  Lemma full_expanded_some_expanded {A} : failed A -> some_expanded A.
  Proof.
    elim: A => //.
    (* + by move=> A HA s B HB //= /andP [] /HA. *)
    + move=> A HA B HB C HC /= /orP [].
      + by move=> /HA ->.
      + by move=> /andP [] _ /HC ->; rewrite orbT. 
  Qed.

  (* Lemma valid_cut_cut {B}: valid_state (cut B).
  Proof. 
    elim: B => //=. 
    + move=> A HA _ B HB; rewrite HA.
    + move=> A HA B HB C HC; rewrite HA HC.
      by rewrite (full_expanded_some_expanded (@failed_cut C)).
  Qed. *)

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
  Proof. 
    elim: l => // x xs /=.
    by rewrite base_and_big_and eq_refl.
  Qed.

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
    + move=> A HA s B HB; rewrite /base_or => /orP [] //= /andP [] /base_and_valid -> /base_or_aux_base_or.
      (* move=> H; move: (H) => /HB ->; rewrite H; case failed => //=. *)
      by move=> /[dup] H => ->.
    + move=> A HA B HB C HC; rewrite /base_or => /orP []//=; case: A HA => //.
      move=> p a H /andP [] /eqP -> H1 ; move:(H1) ->; move: H1 => /base_and_valid ->; rewrite eq_refl.
      case: some_expanded => //.
  Qed.

  Lemma some_expanded_solved {s s' A A'}:
    expand s A = Solved s' A' -> some_expanded A'.
  Proof.
    elim: A s s' A' => //.
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


  (* Lemma some_expanded_expanded {s A A'}:
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
  Qed. *)

  Lemma expand_solved_failed {s1 A s2 B}: expand s1 A = Solved s2 B -> failed A = false.
  Proof.
    elim: A s1 s2 B => //.
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [A' [HA']] /[subst1] /=.
      by rewrite (HA _ _ _ HA').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] /=.
      rewrite (HA _ _ _ HA').
      rewrite (HB _ _ _ HB') => /=.
      case: success => //.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: expand s1 A = Solved s2 B -> success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> ??? [] /[subst2].
    (* + by move=> ??? [] /[subst2]. *)
    + by move=> ? [].
    + move=> A HA s B HB s1 s2 C /= /simpl_expand_or_solved [A' [HA']] /[subst1] /= [].
      by rewrite (HA _ _ _ HA').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] //=.
      by rewrite (HA _ _ _ HA') (HB _ _ _ HB').
  Qed.

  Lemma expand_solved_success1 {s1 A s2 B}: expand s1 A = Solved s2 B -> success A.
  Proof.
    elim: A s1 s2 B => //.
    (* + by move=> ??? [] /[subst2]. *)
    + by move=> ? [].
    + move=> A HA s B HB s1 s2 C /= /simpl_expand_or_solved [A' [HA']] /[subst1] /= [].
      by rewrite (HA _ _ _ HA').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] //=.
      by rewrite (HA _ _ _ HA') (HB _ _ _ HB').
  Qed.

  Lemma expand_failure_success {s1 A A'}:  expand s1 A = Failure A' -> success A = false.
  Proof.
    elim: A s1 A' => //; clear.
    (* success (Or A s B) /\ expand s1 (Or A s B) = Failure (Or A' s B) *)
    (* failed A && success B *)
    + move=> A HA s B HB s1 C /simpl_expand_or_fail [A' [/[dup] HA' +]] ? /[subst].
      by move=> /HA /=.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [].
      + by move=> [A' [+]] ? /= => /HA ->.
      + by move=> [s1 [A' [B' [HA' [+]]]]] ? /= => /HB ->; case success.
  Qed.

  Lemma expand_cb_success {s1 A A'}:  expand s1 A = CutBrothers A' -> success A = false.
  Proof.
    elim: A s1 A' => //; clear.
    (* success (Or A s B) /\ expand s1 (Or A s B) = Failure (Or A' s B) *)
    (* failed A && success B *)
    + by move=> A HA s B HB s1 C /simpl_expand_or_cut.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_cut [].
      + by move=> [A' [+]] ? /= => /HA ->.
      + by move=> [s1 [A' [B' [HA' [+]]]]] ? /= => /HB ->; case success.
  Qed.

  Lemma expand_failure_left {s1 A B}:
    expand s1 A = Failure B -> failed A.
  Proof.
    elim: A s1 B; clear => //.
    + by move=> ? [] //.
    + move=> A HA s1 B HB s2 C /simpl_expand_or_fail [A' [HA']] /[subst1].
      apply: HA HA'.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [].
      + move=> [A'[HA']]  /[subst1] /=.
        by rewrite (HA _ _ HA').
      + move=> [s' [A' [B' [HA' [HB']]]]] /[subst1] /=.
        by rewrite (HB _ _ HB') (expand_solved_success1 HA') orbT.
  Qed.

  Lemma expand_failure_failed {s1 A B}: expand s1 A = Failure B -> failed B.
  Proof.
    move=> /[dup] + /expand_failure_left.
    elim: A s1 B => //.
    + by move=> ?? [] /[subst2].
    + move=> A HA s B HB s1 C /= /simpl_expand_or_fail [A' [HA']] /[subst1] /=.
      by move=> /(HA _ _ HA') ->.
    + move=> A HA ? _ B HB s1 C /simpl_expand_and_fail [].
      + move=> [A' [HA']] /[subst1] /=/orP [].
        + by move=> /(HA _ _ HA') ->.
        + move=> /andP [].
          by rewrite (expand_failure_success HA').
      + move=> [s2 [A' [B' [HA'[HB']]]]] ? /= /orP [].
        + by rewrite (expand_solved_failed HA').
        + move=> /andP [] SA; subst => /= FB.
          by rewrite (expand_solved_success HA') (HB _ _ HB' FB) orbT.
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof. 
    elim: B => // A HA B HB C HC /=.
    destruct A => // /andP [] /eqP -> /[dup] /HC -> ->.
    by rewrite eq_refl orbT.
  Qed.

  Lemma base_and_base_and_ko_valid {B}:
    base_and B || base_and_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_and_valid | move=> /base_and_ko_valid] => ->. Qed.

  Lemma base_or_ko_valid {B}: base_or_ko B -> valid_state B.
  Proof.
    rewrite /base_or_ko => /orP [].
    + by move=> /eqP ->.
    + elim: B => //.
      + move=> A HA s B HB /= /andP [] /base_and_ko_valid ->.
        rewrite /base_or_ko /base_or.
        case: B {HB} => //=.
        + by move=> C _ D ->; rewrite orbT.
        + move=> [] //.
      + by move=> [] // HA B0 HB0 B HB /= /andP [] /[dup] /eqP -> -> ->; rewrite orbT.
  Qed.

  Lemma base_or_base_or_ko_valid {B}:
    base_or B || base_or_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_or_valid | move=> /base_or_ko_valid] => ->. Qed.

  Lemma valid_state_solved {s s' A A'}:
    expand s A = Solved s' A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s s' A' => //.
    + by move=> s s' A [] /[subst2].
    + by move=> pr [] => //= t s s' A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 s2 C.
      by move=> /simpl_expand_or_solved [A' []] /[dup] H /IHA HP /[subst1] /= /andP [] /[dup] VA => {}/HP -> ->.
    + move=> A IHA B0 _ B IHB s1 s2 C /simpl_expand_and_solved [s' [A'[B'[HA[HB]]]]] /[subst1] /=.
      rewrite (expand_solved_success HA).
      move=> /andP [] /andP [] /[dup] BB0 -> /[dup] /(IHA _ _ _ HA) -> VA.
      case SA: success.
      + by move=> VB; rewrite (IHB _ _ _ HB VB).
      + by move=> /eqP H; rewrite H in BB0; move: BB0 => /base_and_base_and_ko_valid /(IHB _ _ _ HB) ->.
  Qed.

  Lemma valid_state_failure {s A A'}:
    expand s A = Failure A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> s A [] /[subst2].
    + by move=> pr [] => //= t s A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 C.
      move=> /simpl_expand_or_fail [A' [HA]] /[subst1] //= /andP [] VA.
      by rewrite (IHA _ _ HA VA) => ->.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_fail [].
      + move=> [A' [HA]] /[subst1] //= /andP [] /andP [] HB0 VA.
        rewrite (expand_failure_success HA)/=.
        move=> /eqP /[subst1].
        rewrite (IHA _ _ HA VA) HB0 eq_refl (base_and_base_and_ko_valid HB0).
        by case: success => //=.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /andP [] HB0 VA.
        rewrite (expand_solved_success HA).
        rewrite (valid_state_solved HA VA) => {HA VA}.
        case X: success => /=.
        + by move=> /(IHB _ _ HB) ->; rewrite HB0.
        + by move=> /eqP /[subst1]; rewrite HB0 (IHB _ _ HB (base_and_base_and_ko_valid HB0)).
  Qed.

  Lemma expand_cb_failed {s1 A A'}: expand s1 A = CutBrothers A' -> failed A = false.
  Proof.
    elim: A s1 A' => //.
    + move=> A HA s B HB A' ? /simpl_expand_or_cut [].
    + move=> A HA B0 HB0 C HC D s /simpl_expand_and_cut [].
      + by move=> [A2[+]] /[subst1] /= /[dup] /HA -> /expand_cb_success ->.
      + move=> [s1[A1[A2[+[+]]]]] /[subst1] /= => + /HC ->.
        by move=> /expand_solved_failed ->; case success.
  Qed.

  Lemma valid_state_cb {s A A'}:
    expand s A = CutBrothers A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> pr [] => //= t s [] /[subst1].
    + move=> A IHA s B IHB s1 C.
      by move=> /simpl_expand_or_cut.
    + move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_cut [].
      + move=> [A' [HA]] /[subst1] //= /andP [] /andP [] HB0 /(IHA _ _ HA) ->.
        by rewrite (expand_cb_success HA) => /eqP /[subst1]; rewrite HB0 eq_refl (base_and_base_and_ko_valid HB0); case: success.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /andP [] HB0 /(valid_state_solved HA) ->.
        rewrite (expand_solved_success HA).
        case X: success => /=.
        + by move=> /(IHB _ _ HB) ->; rewrite HB0.
        + by move=> /eqP /[subst1]; rewrite (IHB _ _ HB (base_and_base_and_ko_valid HB0)) HB0.
  Qed.

  Lemma full_expanded_big_and {pr l}:
    full_expanded (big_and pr l) = false.
  Proof. elim: l => //. Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      by rewrite valid_state_big_and base_or_big_or_aux.
  Qed.

  Lemma valid_state_big_or {pr s t} : valid_state (big_or pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ??; case F => //= -[] //=???; rewrite base_or_big_or_aux.
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

  Lemma expand_expanded_success {s1 A A'}: expand s1 A = Expanded A' -> success A = false.
  Proof.
    elim: A s1 A' => //.
    + move=> A HA s B HB A' ? /simpl_expand_or_expanded [].
      + by move=> [A2 [+]] /[subst1] //= => /HA.
      + move=> [A2 [+]] /[subst1] /expand_cb_success //= /expand_cb_failed.
    + move=> A HA B0 HB0 C HC D s /simpl_expand_and_expanded [].
      + by move=> [A2[+]] /[subst1] /= /[dup] /HA ->.
      + by move=> [s1[A1[A2[H[+]]]]] /[subst1] /= /HC ->; case success.
  Qed.

  Lemma expand_expanded_failed {s1 A A'}: expand s1 A = Expanded A' -> failed A = false.
  Proof.
    elim: A s1 A' => //.
    + move=> A HA s B HB A' ? /simpl_expand_or_expanded [].
      + by move=> [A2 [+]] /[subst1] //= => /HA.
      + by move=> [A2 [+]] /[subst1] //= /expand_cb_failed.
    + move=> A HA B0 HB0 C HC D s /simpl_expand_and_expanded [].
      + move=> [A2[+]] /[subst1] /= /[dup] /HA ->.
        by move=> /expand_expanded_success ->.
      + move=> [s1[A1[A2[+[+]]]]] /[subst1] /= => /expand_solved_failed -> /HC ->.
        by case success.
  Qed.

  Lemma success_cut {A} : success (cut A) = false.
  Proof. by elim: A => // A HA B HB C HC /=; rewrite HA. Qed.

  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cut B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //= _ _ _ HB HC /andP [] /eqP <- /HB ->.
    by rewrite eq_refl.
  Qed.

  Lemma base_or_base_or_ko_cut {B}: base_or B -> base_or_ko (cut B).
  Proof.
    rewrite /base_or /base_or_ko => /orP []; [by case B |].
    elim: B => //.
    + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cut.
      move=> -> /IHB /orP [] // ; case: B IHB => //=.
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP <- /base_and_base_and_ko_cut ->.
      by rewrite eq_refl.
  Qed.

  Lemma simpl_and_cut {A B C}: cut (And A B C) = And (cut A) (cut B) (cut C).
  Proof. by []. Qed.

  Lemma base_and_ko_cut {B}: base_and_ko B -> base_and_ko (cut B).
  Proof.
    elim: B => //.
    move=> A HA B HB C HC /=; case: A HA => //= _ /andP [] /eqP <- /HB ->.
    by rewrite eq_refl.
  Qed.
  
  Lemma base_or_ko_cut {B}: base_or_ko B -> base_or_ko (cut B).
  Proof.
    rewrite /base_or_ko => /orP [].
    + case: B => //.
    + elim: B => //. 
      + move=> [] => //.
        + move=> /= _ _ [] => //.
        + move=> [] //= A B H _ C HC /andP [] /[dup] /H /andP [] _ -> /andP [] /eqP -> _ /HC.
          rewrite eq_refl; case: C {HC} => //=.
      + move=> [] //= _ A HA B HB /andP [] /eqP <-.
        rewrite eq_refl.
        case: A HA => //.
  Qed.

  Lemma valid_state_expanded {s A A'}:
    expand s A = Expanded A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s A' => //.
    + by move=> pr [] => //= t s ? [] /[subst1]; rewrite valid_state_big_or.
    + by move=> s A [] <-.
    + by move=> s [] ?? // ? [] <-; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 C.
      move=> /simpl_expand_or_expanded [].
      + move=> [A' [/[dup] H]] + /[subst1] /= => + /andP [] /(IHA _ _ H) ->.
        by move=> _ ->.
      + move=> [A' [HA']] /[subst1] /= /andP [] /(valid_state_cb HA') ->.
        move=> H.
        have: base_or (cut B) || base_or_ko (cut B).
          by move: H => /orP []; [move=> /base_or_base_or_ko_cut | move=>/base_or_ko_cut] => ->; rewrite orbT.
        by move->.
    +  move=> A IHA B0 _ B IHB s1 C /simpl_expand_and_expanded [].
      + move=> [A' [HA]] /[subst1] //= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 -> /(IHA _ _ HA) ->.
        by rewrite (expand_expanded_success HA) /= => /eqP /[subst1]; rewrite eq_refl VB0; case success.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB -> /(valid_state_solved HA) ->.
        rewrite (expand_solved_success HA) /=.
        case X: success.
        + by move=> /(IHB _ _ HB) ->.
        + by move=> /eqP /[subst1]; rewrite (IHB _ _ HB VB).
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

  Lemma valid_state_expanded_valid_state {s1 A B}:
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

  Lemma valid_state_expanded_failed {s A B}:
    valid_state A -> expanded s A (Failed B) -> failed B.
  Proof.
    remember (Failed _) as F eqn:HF => + H.
    elim: H B HF; clear => //.
    + move=> s A B H ? [] <-.
      elim: A s B H; clear => //.
      + by move=> s B [] /[subst1].
      + by move=> p [] s B //=.
      + move=> A HA s B HB s1 C /simpl_expand_or_fail [A' [H]] /[subst1].
        move=> /=/andP[] /(HA _ _ H) FA.
        by rewrite (expand_failure_failed H).
      + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [].
        + by move=> [A'[HA']] /[subst1] /=/andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 H; rewrite (expand_failure_success HA') => /(HA _ _ HA') -> /=.
        + by move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] /=; rewrite (expand_failure_failed HB') (expand_solved_success HA') orbT.
    + move=> ???? H H1 IH ? /[subst1] H2; apply: IH erefl (valid_state_cb H H2).
    + move=> ???? H H1 IH ? /[subst1] H2; apply: IH erefl (valid_state_expanded H H2).
  Qed.

  Lemma next_alt_aux_base_and {s1 s2 A B}:
     base_and A || base_and_ko A ->  next_alt_aux true s1 A = Some (s2, B) -> A = B.
  Proof.
    elim: A s1 s2 B => //; move=> [] //.
    + move=> _ B0 HB0 B HB s1 s2 C /= /andP [] /eqP /[subst1] BA.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      rewrite BA in HB.
      by rewrite (HB _ _ _ (orbT _) NB).
    + move=> p a _ B0 HB0 B HB s1 s2 C /= /orP []// /andP []/eqP/[subst1] BB.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      by rewrite BB in HB; rewrite (HB _ _ _ isT NB).
  Qed.

  Lemma valid_state_next_alt_aux {b s1 s2 A B}: 
    valid_state A -> next_alt_aux b s1 A = Some (s2, B) 
    -> valid_state B.
  Proof.
    elim: A b s1 s2 B => //.
    + by move=> [] // ??? _ [] /[subst2].
    + by move=> [] // ??? _ [] /[subst2].
    + by move=> ?? [] // ??? _ [] /[subst2].
    + move=> A HA s B HB b s1 s2 C /= /andP [] VA /[dup] /base_or_base_or_ko_valid VB BO.
      case NA: next_alt_aux => [[s3 A']|] [] /[subst2] //=.
      by rewrite (HA _ _ _ _ VA NA) BO.
    + move=> A HA B0 HB0 B HB b s1 s2 C.
      move=> /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 H VA.
      case SA: success.
      + move=> VB.
        case NB: next_alt_aux => [[ ]|].
        + by move=> [] /[subst2] /= ; rewrite VA (HB _ _ _ _ VB NB) SA H.
        + case NA: next_alt_aux => [[ ]|] // [] /[subst2] /=.
           by rewrite (HA _ _ _ _ VA NA) eq_refl H VB0; case success.
      + move=> /eqP /[subst1].
        case NB: next_alt_aux => [[s3 D]|].
        + move=> [] /[subst2] /=; rewrite VA (HB _ _ _ _ (base_and_base_and_ko_valid H) NB) SA.
          rewrite H.
          by rewrite (next_alt_aux_base_and H NB) eq_refl.
        + case NA: next_alt_aux => // [[ ]] [] /[subst2] /=.
          by rewrite (HA _ _ _ _ VA NA) eq_refl (base_and_base_and_ko_valid H) H; case success.
  Qed.

  Lemma valid_state_next_alt {s s' A B} : 
    failed A -> next_alt s A (Some (s', B)) -> valid_state A ->  valid_state B.
  Proof.
    remember (Some _) as S eqn:HS.
    move=> + H; elim: H s' B HS => //; clear.
    + move=> s s2 A B' + FB s1 B [] /[subst2].
      by move=> /valid_state_next_alt_aux H1.
    + move=> s s1 s2 A B C NA FB NB IH s3 D [] /[subst2] FA VA.
      have VB:= valid_state_next_alt_aux VA NA.
      apply: IH erefl FB VB.
  Qed.

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
      have VS := valid_state_expanded_valid_state VA HA.
      apply: runP_fail => //.
    + move=> s s' r A B C HA HB HC IH VA.
      have EA := expandedP_expanded VA HA.
      have VB := valid_state_expanded_valid_state VA HA.
      have FB := valid_state_expanded_failed VA HA.
      have NA := valid_state_next_alt FB HB VB.
      (* have NNA := base_or_base_or_ko_valid NA. *)
      apply: runP_backtrack VA VB EA HB (IH NA).
  Qed.

End valid_state.
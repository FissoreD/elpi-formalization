From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Include Run.
  

  Lemma failed_cut {A}: failed (cut A).
  Proof.
    elim: A => //=.
    + by move=> A HA _ B HB; rewrite HA HB; case: is_dead => //.
    + by move=> A HA B HB C HC; rewrite HA.
  Qed.

  (* Fixpoint full_expanded (s : state) :=
    match s with
    | KO | OK => true
    | Top | Goal _ _ | Bot => false
    | And l _ r => full_expanded l && full_expanded r
    | Or l s r => full_expanded l && full_expanded r
    end. *)

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
    | Dead => false
    | Or Dead _ r => valid_state r
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
  | expandedP_cut {s s' r A B}   : F A -> F B -> expand s A = CutBrothers s' B -> expandedP s' B r -> expandedP s A r
  | expandedP_step {s s' r A B}  : F A -> F B -> expand s A = Expanded s' B    -> expandedP s' B r -> expandedP s A r.

  Inductive runP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
    | runP_done {s s' A B}            : F A -> F B -> expandedP F s A (Done s' B) -> runP s A (Done s' B)
    | runP_fail {s A B}               : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B None -> runP s A (Failed B)
    | runP_backtrack {s s' s'' A B C} : F A -> F B -> expandedP F s A (Failed B) -> next_alt s B (Some (s', C)) ->  runP s' C s'' -> runP s A s''.

  (* Lemma full_expanded_cut A: full_expanded (cut A).
  Proof. 
    elim: A => //.
    + by move=> A HA s B HB //=; rewrite HA HB.
    + by move=> A HA B HB C HC => //=; rewrite HA HC.
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
  Qed. *)

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA; rewrite (HVA HA) /=.
    by rewrite HA eq_refl.
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
      by move=> /[dup] H => ->; case A => //=; auto.
    + move=> A HA B HB C HC; rewrite /base_or => /orP []//=; case: A HA => //.
      move=> p a H /andP [] /eqP -> H1 ; move:(H1) ->; move: H1 => /base_and_valid ->; rewrite eq_refl//.
  Qed.

  Lemma is_dead_failed {A} : is_dead A -> failed A.
  Proof. by elim A => // {}A HA s B HB /=/andP[] /HA -> /HB ->; rewrite if_same. Qed.

  Lemma expand_solved_not_is_dead_left {s1 s2 A B}: expand s1 A = Solved s2 B -> is_dead A = false.
  Proof. 
    elim: A B => //; clear.
    + move=> A HA s B HB C /simpl_expand_or_solved [].
      + by move=> [A'[HA']] /[subst1] /=; rewrite (HA _ HA').
      + by move=> [B'[HA'[HB']]] /[subst1] /= ; rewrite (HB _ HB'); case is_dead.
  Qed.

  Lemma expand_failure_is_dead {s1 A}: expand s1 A = Failure Dead -> is_dead A.
  Proof. 
    elim: A => //.
    + move=> ? []//.
    + move=> A HA s B HB /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[? ]]] //.
      + move=> [B'[?[HA'[HB']]]] //.
      + move=> [] /HA /= -> [] /HB -> //.
    + move=> A HA B0 HB0 B HB /simpl_expand_and_fail [] [?[]] // ?[] ? [] ? []//.
  Qed.

  Lemma expand_failure_not_dead {s1 A B}: expand s1 A = Failure B -> not (is_dead A) -> ~ (is_dead B).
  Proof.
    elim: A B => //.
    + move=> ? [] /[subst1] //.
    + move=> ? [] //.
    + move=> A HA s B HB C /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[?]]] /[subst1] /= H /andP [] HA'' HB'.
        have {}HA:= HA _ HA'.
        by apply: HA _ HA'' => H1; apply H; rewrite H1 HB'.
      + move=> [B'[?[HA'[HB']]]] /[subst1] /= H H1.
        by apply: HB HB' _ H1 => H1; apply: H; rewrite H1 (expand_failure_is_dead HA').
      + move=> [+[+]] => /= /expand_failure_is_dead -> /expand_failure_is_dead -> //.
    + move=> A HA B0 HB0 B HB C /simpl_expand_and_fail [].
      + move=> [A'[HA']] /[subst1] //.
      + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] //.
  Qed.

  Lemma expand_failure_not_dead_left {s1 A B}: expand s1 A = Failure B -> B <> Dead -> (is_dead A) = false.
  Proof.
    elim: A B => //.
    + move=> ? [] /[subst1] //.
    + move=> A HA s B HB C /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[?]]] /[subst1] /= H.
        rewrite (HA _ HA') //.
      + move=> [B'[?[HA'[HB']]]] /[subst1] /= H.
        rewrite (HB _ HB' _) //; case: (is_dead A) => //.
      + move=> [+[+]] => /= /expand_failure_is_dead -> /expand_failure_is_dead -> //.
  Qed.


  Lemma expand_solved_not_is_dead_right {s1 s2 A B}: expand s1 A = Solved s2 B -> is_dead B = false.
  Proof. 
    elim: A B => //; clear.
    + by move=> ? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB C /simpl_expand_or_solved [].
      + by move=> [A'[HA']] /[subst1] /=; rewrite (HA _ HA').
      + move=> [A'[HA'[HB' ]]] /[subst1] /=; rewrite (HB _ HB') //.
    + by move=> A HA B0 _ B HB C /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1].
  Qed.

  Lemma expand_solved_failed {s1 A s2 B}: expand s1 A = Solved s2 B -> failed A = false /\ is_dead A = false.
  Proof.
    elim: A s1 s2 B => //.
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [].
      + move=> [A'[HA']] /[subst1] /=.
        have [FA DA]:= HA _ _ _ HA'.   
        by rewrite (expand_solved_not_is_dead_left HA').
      + move=> [B'[HA' [HB']]] /[subst1] /=.
        have [FB DB] := (HB _ _ _ HB').
        by rewrite (expand_failure_is_dead HA').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] /=.
      have [FA DA]:= HA _ _ _ HA'.   
      have [FB DB]:= HB _ _ _ HB'.
      rewrite FA FB; case: success => //.
  Qed.

  Lemma expand_solved_success1 {s1 A s2 B}: expand s1 A = Solved s2 B -> success A.
  Proof.
    elim: A s1 s2 B => //.
    (* + by move=> ??? [] /[subst2]. *)
    + by move=> ? [].
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [].
      + move=> [A' [HA']] /[subst1] /= [].
        rewrite (HA _ _ _ HA').
        by rewrite (proj2 (expand_solved_failed HA')).
      + move=> [B'[HA'[HB']]] /[subst1] /=; rewrite (HB _ _ _ HB').
        by rewrite (expand_failure_is_dead HA').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] //=.
      by rewrite (HA _ _ _ HA') (HB _ _ _ HB').
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: expand s1 A = Solved s2 B -> success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> ??? [] /[subst2].
    (* + by move=> ??? [] /[subst2]. *)
    + by move=> ? [].
    + move=> A HA s B HB s1 s2 C /= /simpl_expand_or_solved [].
      + move=> [A' [HA']] /[subst1] /= []; rewrite (HA _ _ _ HA').
        by destruct A' => //; have:= expand_solved_not_is_dead_right HA' => //= ->.
      + move=> [B'[HA'[HB']]] /[subst1] /=; rewrite (HB _ _ _ HB') //.
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] //=.
      by rewrite (HA _ _ _ HA') (HB _ _ _ HB').
  Qed.

  Lemma expand_failure_success {s1 A A'}:  expand s1 A = Failure A' -> success A = false.
  Proof.
    elim: A s1 A' => //; clear.
    + move=> A HA s B HB s1 C /simpl_expand_or_fail [|[]].
      + move=> [A' [HA' [HD]]] /[subst1] /= ; rewrite (HA _ _ HA').
        have H:= expand_failure_not_dead_left HA' HD.
        rewrite H//.
      + by move=> [B'[?[HA'[HB']]]] /[subst1] /=; rewrite (HA _ _ HA') (HB _ _ HB') if_same.
      + by move=> [HA'[HB']] /[subst1] /=; rewrite (HA _ _ HA') (HB _ _ HB') if_same.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [].
      + by move=> [A' [+]] ? /= => /HA ->.
      + by move=> [s1 [A' [B' [HA' [+]]]]] ? /= => /HB ->; case success.
  Qed.

  Lemma expand_cb_success {s1 s2 A A'}:  expand s1 A = CutBrothers s2 A' -> success A = false.
  Proof.
    elim: A s1 s2 A' => //; clear.
    (* success (Or A s B) /\ expand s1 (Or A s B) = Failure (Or A' s B) *)
    (* failed A && success B *)
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_cut [s3[B'[?[HB']]]] /[subst1] /=.
      by rewrite (HB _ _ _ HB').
    + move=> A HA B0 _ B HB s s2 C /simpl_expand_and_cut [].
      + by move=> [A' [+]] ? /= => /HA ->.
      + by move=> [s1 [A' [B' [HA' [+]]]]] ? /= => /HB ->; case success.
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
        move=> /[dup] /HB -> ->.
        by rewrite 2!orbT; destruct A.
      + by move=> [] // HA B0 HB0 B HB /= /andP [] /[dup] /eqP -> -> ->; rewrite orbT.
  Qed.

  Lemma base_or_base_or_ko_valid {B}:
    base_or B || base_or_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_or_valid | move=> /base_or_ko_valid] => ->. Qed.

  Lemma valid_state_dead {B}: valid_state B -> B <> dead B.
  Proof.
    rewrite /dead.
    elim: B => //.
    + move=> A HA s B HB /= H.
      have {H} [] : (A = Dead /\ valid_state B) \/ (A <> Dead /\ valid_state A && (base_or B || base_or_ko B)).
        case: A H {HA} => //; try move=> /andP [] // -> ->; try by right.
        move=> ->; left => //.
      + move=> [?] /HB; subst; congruence.
      + move=> [?] /andP [] /HA; congruence.
    + move=> A HA B0 HB0 B HB /=/andP [] /andP [] /base_and_base_and_ko_valid /HB0; congruence.
  Qed.

  Lemma simpl_valid_state_or {s A B}: valid_state (Or A s B) -> (A = Dead /\ valid_state B) \/ (A <> Dead /\ valid_state A /\ (base_or B || base_or_ko B)).
  Proof.
    move=> /=; case: A => //.
    + move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; left => //.
    + move=> ?? /orP [] ->; right; repeat split => //; rewrite orbT //.
    + move=> ??? /andP [] H ->; right => //.
    + move=> ??? /andP [] H ->; right => //.
  Qed.


  (* Lemma expand_is_dead_flow {s A}: valid_state A -> is_dead A -> expand s A = Failure Dead.
  Proof.
    rewrite /dead.
    elim: A s => //.
    (* + by move=> s r _ /[subst1]; eexists. *)
    + move=> A HA s B HB s1 /simpl_valid_state_or [].
      + move=> [] /[subst1] VB /= HB'.

        rewrite (HB _ VB HB')=> /=.
      + have := HA _ HA'; congruence.
      + have := HA _ HA'; congruence.
      + have := HA s1 HA'; rewrite X => -[] /[subst1] /=.
        have:= HB s1 HB' => -> /=; destruct A => //=; repeat f_equal.
        + rewrite (HB _ HB;) 
        + 
      + move=> /[subst1]; by have [? [?]] := HA _ _ HA' X.
      + have [C [[] ?]]:= HA _ _ HA' X => H1 /[subst].
        case Y: expand => //=.
        + have [?[??]]:= HB _ _ HB' Y; congruence.
        + have [?[??]]:= HB _ _ HB' Y; congruence.
        + have [D[[] H2]]:= HB _ _ HB' Y => /[subst] H; destruct C => //= /[subst1].
          + by eexists; repeat split.
          + by eexists; repeat split; move: H1 HB' => /= -> ->.
        + have:= expand_solved_not_is_dead_left Y; congruence.
      + move=> /[subst1]; have:= expand_solved_not_is_dead_left X; congruence.
  Qed. *)

  Lemma expand_failure_left {s1 A B}:
    expand s1 A = Failure B -> failed A.
  Proof.
    elim: A s1 B; clear => //.
    + by move=> ? [] //.
    + move=> A HA s1 B HB s2 C /simpl_expand_or_fail [|[]].
      + move=> [A' [HA'[HD]]] /[subst1] /=; rewrite (HA _ _ HA').
        by rewrite (expand_failure_not_dead_left HA' HD).
      + move=> [B'[HD[HA'[HB']]]]  /[subst1] /=.
        by rewrite (HA _ _ HA') (HB _ _ HB') if_same.
      + move=> [HA'[HB']] /[subst1] /=.
        by rewrite (HA _ _ HA') (HB _ _ HB') if_same.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [].
      + move=> [A'[HA']]  /[subst1] /=.
        by rewrite (HA _ _ HA').
      + move=> [s' [A' [B' [HA' [HB']]]]] /[subst1] /=.
        by rewrite (HB _ _ HB') (expand_solved_success1 HA') orbT.
  Qed.

  Lemma expand_failure_not_dead_right {s1 A B}:
    expand s1 A = Failure B -> B <> Dead -> is_dead B = false.
  Proof.
    elim: A s1 B => //.
    + by move=> ?? [] /[subst1] //.
    + by move=> ?? [] /[subst1] //.
    + by move=> ?[] /[subst1] //.
    + move=> A HA s B HB s1 C /simpl_expand_or_fail [|[]].
      + by move=> [A'[HA'[DA]]] /[subst1] _ /=; rewrite (HA _ _ HA' DA).
      + by move=> [B'[DB[HA'[HB']]]] /[subst1] _ /=; rewrite (HB _ _ HB' DB).
      + by move=> [HA' [HB']] /[subst1] //.
    + move=> A HA B0 HB0 B HB s C /simpl_expand_and_fail [].
      + by move=> [A'[HA']] /[subst1] _ /=.
      + by move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] _ /=.
  Qed.

  Lemma expand_failure_failed {s1 A B}: expand s1 A = Failure B -> failed B.
  Proof.
    move=> /[dup] + /expand_failure_left.
    elim: A s1 B => //.
    + by move=> ?? [] /[subst2].
    + by move=> /= _ ? [] /[subst1] //.
    + move=> A HA s B HB s1 C /= /simpl_expand_or_fail [|[]].
      + move=> [A' [HA'[DA]]] /[subst1] /=.
        rewrite (expand_failure_not_dead_left HA' DA) => /(HA _ _ HA') ->.
        by rewrite (expand_failure_not_dead_right HA' DA).
      + move=> [B'[DB[HA'[HB']]]] /[subst1] /=.
        by rewrite (expand_failure_is_dead HA') => /(HB _ _ HB').
      + move=> [HA' [HB']] /[subst1] //.
    + move=> A HA ? _ B HB s1 C /simpl_expand_and_fail [].
      + move=> [A' [HA']] /[subst1] /=/orP [].
        + by move=> /(HA _ _ HA') ->.
        + move=> /andP [].
          by rewrite (expand_failure_success HA').
      + move=> [s2 [A' [B' [HA'[HB']]]]] /[subst1] /=/orP [].
        + by have:= (expand_solved_failed HA') => -[] -> //.
        + move=> /andP [] SA; subst => /= FB.
          by rewrite (expand_solved_success HA') (HB _ _ HB' FB) orbT.
  Qed.


  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      rewrite valid_state_big_and base_or_big_or_aux IH; case: big_and => //.
  Qed.

  Lemma valid_state_big_or {pr s t} : valid_state (big_or pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ??; case F => //= -[] //=???; rewrite base_or_big_or_aux.
  Qed. 


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

  (* Lemma valid_state_valid_state_cut {A} : valid_state A -> valid_state (cut A).
  Proof.
    rewrite /cut.
    elim: A => //.
    + move=> A HA s B HB /simpl_valid_state_or [].
      + move=> [] /[subst1] /HB //; simpl const.
        unify const. *)


  Lemma expand_cb_not_dead {s1 s A B}: expand s1 A = CutBrothers s B -> B <> Dead.
  Proof.
    elim: A B => //.
    + move=> ?[] //= [] /[subst2] //.
    + move=> A HA s2 B HB C /simpl_expand_or_cut [s3[B'[?[HB']]]] /[subst1]//.
    + move=> A HA B0 HB0 B HB C /simpl_expand_and_cut [].
      + move=> [A'[HA']] /[subst1]//.
      + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] //.
  Qed.

  Lemma valid_state_solved {s A r}:
    expand s A = r -> valid_state A -> valid_state (get_state r).
  Proof.
    elim: A s r => //; try by move=> s r // /[subst1] //.
    + by move=> ? [|?] ?? /[subst1] //=; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 [s2 C|||].
      + move=> /simpl_expand_or_expanded [|[]].
        + move=> [A'[HA']] /[subst1] /simpl_valid_state_or [].
          + move=> [] /[subst1] //.
          + move=> [] _ [] VA /[dup] /base_or_base_or_ko_valid /= -> ->; rewrite (IHA _ _ HA' VA); destruct A' => //.
        + move=> [A'[HA']] /[subst1] /simpl_valid_state_or [].
          + move=> [] /[subst1] //.
          + move=> [] _ [] VA /[dup] /base_or_base_or_ko_valid /= VB BB.
            suffices:  valid_state A' && (base_or (cut B) || base_or_ko (cut B)).
              destruct A' => //.
            by move: BB; rewrite (IHA _ _ HA' VA) => /orP [/base_or_base_or_ko_cut|/base_or_ko_cut] ->; rewrite orbT.
        + move=> [] HA [B' +] /simpl_valid_state_or [] [] DA => -[] /[subst1] H /=.
          + by move: H => [] /IHB {}IHB /IHB ->.
          + by move: H => [] /IHB {}IHB [] _ /base_or_base_or_ko_valid /IHB //.
      + move=> s2 C /simpl_expand_or_cut [s3[B'[?[HB]]]] /[subst1] /simpl_valid_state_or [].
        + move=> [] _ VB; apply: IHB HB VB.
        + move=> []//.
      + move=> C /simpl_expand_or_fail [|[]].
        + move=> [A'[HA'[DA']]] /[subst1] /simpl_valid_state_or[] [].
          + move=> /[subst1]; simpl in HA'; congruence.
          + move=> DA [] VA /[dup] /base_or_base_or_ko_valid /= -> ->; rewrite (IHA _ _ HA' VA); destruct A' => //.
        + move=> [B'[DB'[HA'[HB']]]] /[subst1] /simpl_valid_state_or [] [].
          + by move=> ? VB /[subst] /=; rewrite (IHB _ _ HB' VB).
          + by move=> ? [] VA /base_or_base_or_ko_valid /(IHB _ _ HB') /= ->.
        + move=> [HA'[HAB']] /[subst1] /simpl_valid_state_or [] [].
          + move=> /[subst1] . 
      +
      move=> /simpl_expand_or_solved [].
      + move=> [A' []] /[dup] H /IHA HP /[subst1] /simpl_valid_state_or [].
        + move=> [] ? VB /[subst]; move: H => //.
        + move=> [] ? [] VA /[dup] /base_or_base_or_ko_valid /= -> ->; rewrite (HP VA); destruct A' => //.
        + move=> [B'[HA'[HB']]] /[subst1] /= H.
          have {H}: valid_state B || valid_state A && (base_or B || base_or_ko B).
            case: A H {HA' IHA}; try by move=> ->; rewrite ?orbT.
            by move=> ?? ->; rewrite orbT.
            by move=> ??? ->; rewrite orbT.
            by move=> ??? ->; rewrite orbT.
          move=> /orP [].
            + by move=> /(IHB _ _ _ HB').
            + by move=> /andP [] _ /base_or_base_or_ko_valid /(IHB _ _ _ HB').
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

  Lemma expand_cb_failed {s1 s2 A A'}: expand s1 A = CutBrothers s2 A' -> failed A = false.
  Proof.
    elim: A s1 s2 A' => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_cut [].
    + move=> A HA B0 HB0 C HC D ? s /simpl_expand_and_cut [].
      + by move=> [A2[+]] /[subst1] /= /[dup] /HA -> /expand_cb_success ->.
      + move=> [s1[A1[A2[+[+]]]]] /[subst1] /= => + /HC ->.
        by move=> /expand_solved_failed ->; case success.
  Qed.

  Lemma valid_state_cb {s s2 A A'}:
    expand s A = CutBrothers s2 A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s s2 A' => //.
    + by move=> pr [] => //= t s s2 [] /[subst2].
    + move=> A IHA s B IHB s1 s2 C.
      by move=> /simpl_expand_or_cut.
    + move=> A IHA B0 _ B IHB s1 s2 C /simpl_expand_and_cut [].
      + move=> [A' [HA]] /[subst1] //= /andP [] /andP [] HB0 /(IHA _ _ _ HA) ->.
        by rewrite (expand_cb_success HA) => /eqP /[subst1]; rewrite HB0 eq_refl (base_and_base_and_ko_valid HB0); case: success.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /andP [] HB0 /(valid_state_solved HA) ->.
        rewrite (expand_solved_success HA).
        case X: success => /=.
        + by move=> /(IHB _ _ _ HB) ->; rewrite HB0.
        + by move=> /eqP /[subst1]; rewrite (IHB _ _ _ HB (base_and_base_and_ko_valid HB0)) HB0.
  Qed.


  Lemma full_expanded_cb {s1 s2 A A'} : 
    expand s1 A = CutBrothers s2 A' -> full_expanded A -> full_expanded A'.
  Proof.
    elim: A A' s1 s2 => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_cut [].
    + move=> A HA B0 HB0 C HC D ? s /simpl_expand_and_cut [].
      + by move=> [A2[H]] /[subst1] /= /andP [] /(HA _ _ _ H) -> ->.
      + by move=> [s1[A1[A2[H[H1]]]]] /[subst1] /= /andP [] /(full_expanded_solved H) -> /(HC _ _ _ H1) ->.
  Qed.

  Lemma full_expanded_expanded {s1 s2 A A'} : 
    expand s1 A = Expanded s2 A' -> full_expanded A -> full_expanded A'.
  Proof.
    elim: A A' s1 s2 => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_expanded [].
      + by move=> [A2 [H]] /[subst1] //= /andP [] /(HA _ _ _ H) -> ->.
      + move=> [A2 [H]] /[subst1] //= /andP [] /(full_expanded_cb H) ->.
        by rewrite full_expanded_cut.
    + move=> A HA B0 HB0 C HC D s ? /simpl_expand_and_expanded [].
      + by move=> [A2[H]] /[subst1] /= /andP [] /(HA _ _ _ H) -> ->.
      + by move=> [s1[A1[A2[H[H1]]]]] /[subst1] /= /andP [] /(full_expanded_solved H) -> /(HC _ _ _ H1) ->.
  Qed.

  Lemma expand_expanded_success {s1 s2 A A'}: expand s1 A = Expanded s2 A' -> success A = false.
  Proof.
    elim: A s1 A' s2 => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_expanded [].
      + by move=> [A2 [+]] /[subst1] //= => /HA.
      + move=> [A2 [+]] /[subst1] /expand_cb_success //= /expand_cb_failed.
    + move=> A HA B0 HB0 C HC D ? s /simpl_expand_and_expanded [].
      + by move=> [A2[+]] /[subst1] /= /[dup] /HA ->.
      + by move=> [s1[A1[A2[H[+]]]]] /[subst1] /= /HC ->; case success.
  Qed.

  Lemma expand_expanded_failed {s1 s2 A A'}: expand s1 A = Expanded s2 A' -> failed A = false.
  Proof.
    elim: A s1 s2 A' => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_expanded [].
      + by move=> [A2 [+]] /[subst1] //= => /HA.
      + by move=> [A2 [+]] /[subst1] //= /expand_cb_failed.
    + move=> A HA B0 HB0 C HC D ? s /simpl_expand_and_expanded [].
      + move=> [A2[+]] /[subst1] /= /[dup] /HA ->.
        by move=> /expand_expanded_success ->.
      + move=> [s1[A1[A2[+[+]]]]] /[subst1] /= => /expand_solved_failed -> /HC ->.
        by case success.
  Qed.

  Lemma success_cut {A} : success (cut A) = false.
  Proof. by elim: A => // A HA B HB C HC /=; rewrite HA. Qed.

  Lemma valid_state_expanded {s s2 A A'}:
    expand s A = Expanded s2 A' -> valid_state A -> valid_state A'.
  Proof.
    elim: A s s2 A' => //.
    + by move=> pr ? [] => //= t s ? [] /[subst1]; rewrite valid_state_big_or.
    + by move=> s A [] /[subst2].
    + by move=> s [] ??? // ? [] /[subst2]; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 ? C.
      move=> /simpl_expand_or_expanded [].
      + move=> [A' [/[dup] H]] + /[subst1] /= => + /andP [] /(IHA _ _ _ H) ->.
        by move=> _ ->.
      + move=> [A' [HA']] /[subst1] /= /andP [] /(valid_state_cb HA') ->.
        move=> H.
        have: base_or (cut B) || base_or_ko (cut B).
          by move: H => /orP []; [move=> /base_or_base_or_ko_cut | move=>/base_or_ko_cut] => ->; rewrite orbT.
        by move->.
    +  move=> A IHA B0 _ B IHB s1 ? C /simpl_expand_and_expanded [].
      + move=> [A' [HA]] /[subst1] //= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 -> /(IHA _ _ _ HA) ->.
        by rewrite (expand_expanded_success HA) /= => /eqP /[subst1]; rewrite eq_refl VB0; case success.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB -> /(valid_state_solved HA) ->.
        rewrite (expand_solved_success HA) /=.
        case X: success.
        + by move=> /(IHB _ _ _ HB) ->.
        + by move=> /eqP /[subst1]; rewrite (IHB _ _ _ HB VB).
  Qed.

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> expandedP valid_state s A r.
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A1 A2 EA VA.
      apply: expandedP_done => //.
      apply: valid_state_solved EA VA.
    + move=> s A B HA HB.
      apply: expandedP_fail => //.
      apply: valid_state_failure HA HB.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_cb HA VA.
      apply: expandedP_cut (VA) VB (HA) (IH VB).
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expanded HA VA.
      apply: expandedP_step (VA) VB (HA) (IH VB).
  Qed.

  Lemma valid_state_expanded_done {s1 s2 A B}:
    valid_state A ->  expanded s1 A (Done s2 B) -> valid_state B.
  Proof.
    remember (Done _ _) as D eqn:HD => + [b H].
    elim: H s2 B HD => //; clear.
    + move=> s1 s2 A B HA s3 C [] /[subst2].
      apply: valid_state_solved HA.
    + move=> s1 s2 r A B b HA HB + s3 C ? /(valid_state_cb HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
    + move=> s1 s2 r A B b HA HB + s3 C ? /(valid_state_expanded HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
  Qed.

  Lemma valid_state_expanded_valid_state {s1 A B}:
    valid_state A ->  expanded s1 A (Failed B) -> valid_state B.
  Proof.
    remember (Failed _) as D eqn:HD => + [b H].
    elim: H B HD => //; clear.
    + move=> s1 A B HA s3 [] /[subst1].
      apply: valid_state_failure HA.
    + move=> s1 s2 r A B b HA HB + C ? /(valid_state_cb HA) VB /[subst].
      by move=> /(_ _ erefl VB).
    + move=> s1 s2 r A B b HA HB + C ? /(valid_state_expanded HA) VB /[subst].
      by move=> /(_ _ erefl VB).
  Qed.

  Lemma valid_state_expanded_failed {s A B}:
    valid_state A -> expanded s A (Failed B) -> failed B.
  Proof.
    remember (Failed _) as F eqn:HF => + [b H].
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
    + move=> ?????? H H1 IH ? /[subst1] H2; apply: IH erefl (valid_state_cb H H2).
    + move=> ?????? H H1 IH ? /[subst1] H2; apply: IH erefl (valid_state_expanded H H2).
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
    next_alt s A (Some (s', B)) -> valid_state A ->  valid_state B.
  Proof.
    remember (Some _) as S eqn:HS.
    move=> H; elim: H s' B HS => //; clear.
    + move=> s s2 A B' + FA s1 B [] /[subst2].
      by move=> /valid_state_next_alt_aux H1.
    + move=> s s1 r A B NA FB NB IH s2 D /[subst1] VA.
      have VB:= valid_state_next_alt_aux VA NA.
      apply: IH erefl VB.
  Qed.

  Lemma runP_run {s A r}:
    valid_state A -> run s A r -> runP valid_state s A r.
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A B b EA VA.
      have:= expandedP_expanded VA (ex_intro _ _ EA) => H.
      have ?:= valid_state_expanded_done VA (ex_intro _ _ EA).
      apply: runP_done => //.
    + move=> s A B b HA HB VA.
      have:= expandedP_expanded VA (ex_intro _ _ HA) => H.
      have VS := valid_state_expanded_valid_state VA (ex_intro _ _ HA).
      apply: runP_fail => //.
    + move=> s s' r A B C b1 b2 b3 HA HB HC IH Hb VA.
      have EA := expandedP_expanded VA (ex_intro _ _ HA).
      have VB := valid_state_expanded_valid_state VA (ex_intro _ _ HA).
      have NA := valid_state_next_alt HB VB.
      apply: runP_backtrack VA VB EA HB (IH NA).
  Qed.

End valid_state.
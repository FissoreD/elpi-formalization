From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Include Run.
  

  Lemma failed_cut {A}: failed (cut A).
  Proof.
    elim: A => //=.
    + move=> A HA s B HB.
      by case X: eq_op => //=; rewrite HA HB if_same.
    + move=> A HA B HB C HC.
      by case X: eq_op => //=; rewrite HA HC.
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

  Lemma is_dead_failed {A} : A = dead A -> failed A.
  Proof. elim: A => //.
    + by move=> A HA s B HB /= [] /HA -> /HB -> ; rewrite if_same.
    + by move=> A HA B0 HB0 B HB /= [] /HA ->.
  Qed.

  Lemma expand_solved_not_is_dead_left {s1 s2 A B}: expand s1 A = Solved s2 B -> dead A <> A.
  Proof. 
    elim: A B s2 => //; clear.
    + move=> A HA s B HB C ? /simpl_expand_or_solved [].
      + by move=> [A'[+]] /[subst1] /HA{}HA -[]/HA.
      + by move=> [B'[HA'[+]]] /[subst1] /HB{}HB [] _ /HB.
    + move=> A HA B0 HB0 B HB C ? /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1] /= -[].
      by move=> /(HA _ _ HA').
  Qed.

  Lemma expand_failure_is_dead {s1 A}: expand s1 A = Failure Dead -> dead A = A.
  Proof. 
    elim: A => //.
    + move=> ? []//.
    + move=> A HA s B HB /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[? ]]] //.
      + move=> [B'[?[HA'[HB']]]] //.
      + move=> [] /HA /= -> [] /HB -> //.
    + move=> A HA B0 HB0 B HB /simpl_expand_and_fail [|[]].
      + by move=> [] /HA /= ->.
      + move=> [A'[DA[]]] //.
      + move=> [?[?[?]]] [] ?[] //.
  Qed.

  Lemma expand_solved_not_is_dead_right {s1 s2 A B}: expand s1 A = Solved s2 B -> B <> dead B.
  Proof. 
    elim: A B s2 => //; clear.
    + by move=> ?? [] /[subst2].
    + by move=> ? [] //.
    + move=> A HA s B HB C ? /simpl_expand_or_solved [].
      + by move=> [A'[+]] /[subst1] /= /HA{}HA -[]  /HA.
      + by move=> [A'[HA'[+ ]]] /[subst1] /=/HB{}HB -[] /HB.
    + move=> A HA B0 _ B HB C ? /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1] /= -[].
      by move=> /(HA _ _ HA').
  Qed.

  Lemma expand_failure_not_dead_right {s1 A B}: expand s1 A = Failure B -> not (A = dead A) -> not (B = dead B).
  Proof.
    elim: A B s1 => //.
    + by move=> ?? [] /[subst1] //.
    + by move=> ? [] //.
    + move=> A HA s B HB C ? /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[?]]] /[subst1] /= H [] HA'' HB'.
        have {}HA:= HA _ _ HA'.
        by apply: HA _ HA'' => H1 ; apply H ; rewrite H1 HB' !dead_dead_same.
      + move=> [B'[?[HA'[HB']]]] /[subst1] /= H [] H1.
        by apply: HB HB' _ H1 => H1; apply: H; rewrite H1 (expand_failure_is_dead HA') !dead_dead_same.
      + move=> [+[+]] => /= /expand_failure_is_dead -> /expand_failure_is_dead -> //.
    + move=> A HA B0 HB0 B HB C ? /simpl_expand_and_fail [|[]].
      + move=> [HA'] /[subst1].
        by have:= expand_failure_is_dead HA' => <- /=; rewrite dead_dead_same.
      + move=> [A'[DA[HA']]] /[subst1] H [] DA'; apply: HA HA' _ DA' => H2.
        by apply: H => /=; rewrite H2 !dead_dead_same.
      + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] //= H [] H1.
        apply: expand_solved_not_is_dead_right HA' H1.
  Qed.

  Lemma expand_is_dead_flow s {A}: A = dead A -> expand s A = Failure Dead.
  Proof.
    elim: A s => //.
    (* + by move=> s r _ /[subst1]; eexists. *)
    + by move=> A HA s B HB s1 [] /HA{}HA /HB{}HB /=; rewrite HA HB.
    + by move=> A HA B0 HB0 B HB s [] /HA{}HA /= ; rewrite HA.
  Qed.


  Lemma expand_failure_not_dead_left {s1 A B}: expand s1 A = Failure B -> B <> Dead -> A <> dead A.
  Proof.
    elim: A B => //.
    + move=> ? [] /[subst1] //.
    + move=> A HA s B HB C /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[?]]] /[subst1] /= H -[].
        by move=> /(HA _ HA'); auto.
      + move=> [B'[?[HA'[HB']]]] /[subst1] /= H [] _.
        by move=> /(HB _ HB'); auto.
      + by move=> [+[+]] => /= /expand_failure_is_dead -> /expand_failure_is_dead -> //.
    + move=> A HA B0 HB0 B HB C /simpl_expand_and_fail [|[]].
      + move=> [HA'] /[subst1] //.
      + move=> [A'[DA[HA']]] /[subst1] _ /= H; apply: HA HA' DA _; congruence.
      + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] _ /= [] H.
        have:= expand_is_dead_flow s1 H; congruence.
  Qed.

  Lemma expand_solved_failed {s1 A s2 B}: expand s1 A = Solved s2 B -> failed A = false /\ failed B = false /\ A <> dead A /\ B <> dead B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> ??? [] /[subst2]; repeat split.
    + move=> ?[]//.
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [].
      + move=> [A'[HA']] /[subst1] /=.
        have [FA [FB[]]] := HA _ _ _ HA' => /eqP; case: eq_op => // _ /eqP; case: eq_op => // _; rewrite FA FB.
        by repeat split => //=; move=> [] DA DB; have:= HA _ _ _ HA' => -[_[_[]]] ; rewrite DA !dead_dead_same.
      + move=> [B'[HA' [HB']]] /[subst1] /=.
        have [FA [FB[]]] := (HB _ _ _ HB') => /eqP; case: eq_op => // _ /eqP; case: eq_op => // _; rewrite FA FB.
        rewrite (expand_failure_is_dead HA') eq_refl.
        by repeat split => //; move=> [] DB; by have:= HB _ _ _ HB' => -[_[_[]]]; rewrite DB !dead_dead_same //.
    + move=> A HA B0 _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] /=.
      have [FA [FA'[DA DA']]]:= HA _ _ _ HA'. 
      have [FB [FB'[DB DB']]]:= HB _ _ _ HB'.
      rewrite FA FB FA' FB' /=.
      have XX: And A B0 B <> And (dead A) B0 B.
        move=> []//.
      have YY: And A' B0 B' <> And (dead A') B0 B'.
        move=> []//.
      case: success => //=; case: success => //= ; repeat split => //.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: expand s1 A = Solved s2 B -> success A /\ success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ??? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [].
      + move=> [A' [HA']] /[subst1] /= [].
        have [] := (HA _ _ _ HA') => -> ->.
        have:= (expand_solved_failed HA') => -[FA[FA'[DA DA']]]; case: eqP => // _; case: eqP => //.
      + move=> [B'[HA'[HB']]] /[subst1] /=.
        rewrite (expand_failure_is_dead HA') eq_refl.
        by have:= (HB _ _ _ HB').
    + move=> A HA ? _ B HB s1 s2 C /simpl_expand_and_solved [s3 [A' [B' [HA' [HB']]]]] /[subst1] //=.
      have [A1 A2]:= (HA _ _ _ HA'); have[B1 B2]:= (HB _ _ _ HB'); repeat split; rewrite ?A1 ?A2 ?B1 ?B2 //.
  Qed.

  (* Lemma expand_failure_success {s1 A A'}:  expand s1 A = Failure A' -> success A = false.
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
  Qed. *)


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
    elim: B => //.
    + move=> A HA s B HB /= H.
      have {H} [] : (A = Dead /\ valid_state B) \/ (A <> Dead /\ valid_state A && (base_or B || base_or_ko B)).
        case: A H {HA} => //; try move=> /andP [] // -> ->; try by right.
        move=> ->; left => //.
      + move=> [?] /HB; subst; congruence.
      + move=> [?] /andP [] /HA; congruence.
    + move=> A HA B0 HB0 B HB /=/andP [] /andP [] /base_and_base_and_ko_valid /HB0.
      move=> H1 H2 H3 [] H; apply: HA H2 H.
  Qed.

  Lemma simpl_valid_state_or {s A B}: valid_state (Or A s B) -> (A = Dead /\ valid_state B) \/ (A <> Dead /\ valid_state A /\ (base_or B || base_or_ko B)).
  Proof.
    move=> /=; case: A => //.
    all: try by move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; left => //.
    + move=> ?? /orP [] ->; right; repeat split => //; rewrite orbT //.
    + move=> ??? /andP [] H ->; right => //.
    + move=> ??? /andP [] H ->; right => //.
  Qed.

  Lemma expand_failure_failed {s1 A B}:
    expand s1 A = Failure B -> failed A /\ failed B.
  Proof.
    elim: A s1 B; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2 C /simpl_expand_or_fail [|[]].
      + move=> [A' [+[HD]]] /[subst1] /= => /[dup].
        move=> /HA [] -> -> HA'.
        have:= (expand_failure_not_dead_left HA' HD). case: eqP =>// H.
        have:= expand_failure_not_dead_right HA' H; case: eqP => //.
      + move=> [B'[HD[+[+]]]]  /[subst1] /=.
        by move=> /HA [] -> _ /HB [] -> ->; rewrite if_same.
      + by move=> [+[+]] /[subst1] /= => /HA [] -> _ /HB [] -> _; rewrite if_same.
    + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [|[]].
      + by move=> [] /HA [] /= -> _ ->.
      + by move=> [?[A'[+]]]  /[subst1] /= /HA [] -> ->.
      + move=> [s' [A' [B' [+ [+]]]]] /[subst1] /=.
        by move=> /expand_solved_success [] -> -> /HB [] -> ->; rewrite !orbT.
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

  Lemma xx {A}: A = dead A -> base_and_ko (cut A) -> false.
  Proof.
    elim: A => //=.
    + move=> A HA s B HB [] /HA {}HA /HB {}HB.
      case X: eq_op => //.
    + by move=> A HA B0 HB0 B HB [] /[dup] /HA {}HA <-; rewrite eq_refl //.
  Qed.

  Lemma base_or_base_or_ko_cut {B}: base_or B -> base_or_ko (cut B).
  Proof.
    rewrite /base_or /base_or_ko => /orP []; [by case B |].
    elim: B => //.
    + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cut.
      case X: (Or A s B == Or (dead A) s (dead B)) => //.
      + by move: X => /eqP [] //=; by move=> /xx X _ /X.
      + by move=> /= -> /IHB /orP [/eqP|] -> .
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP <- /base_and_base_and_ko_cut ->.
      by rewrite eq_refl.
  Qed.

  Lemma base_and_ko_cut {B}: base_and_ko B -> base_and_ko (cut B).
  Proof.
    elim: B => //.
    move=> A HA B HB C HC /=; case: A HA => //= _ /andP [] /eqP <- /HB ->.
    by rewrite eq_refl.
  Qed.
  
  Lemma base_or_ko_cut {B}: base_or_ko B -> base_or_ko (cut B).
  Proof.
    rewrite /base_or_ko => /orP [].
    + by case: B => //.
    + elim: B => //.
      + move=> A HA s B HB. simpl base_or_ko_aux at 1 => /andP [] BA BB.
        suffices H: base_or_ko_aux (cut (Or A s B)).
          by rewrite H orbT.
        simpl cut.
        case X: (Or A s B == Or (dead A) s (dead B)) => //=.
        + by move: X => /eqP [] /xx /(_ (base_and_ko_cut BA)).
        + move: X => /eqP; rewrite (base_and_ko_cut BA).
          by move: (HB BB) => /orP [/eqP|] -> //.
      + move=> A HA B0 HB0 B HB.
        simpl base_or_ko_aux at 1; destruct A => // /andP [] /eqP /[subst1] /=.
        by move=> /base_and_ko_cut ->; rewrite eq_refl.
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
  Search dead expand Failure.

  Lemma toT {P}: P = true -> is_true P.
  Proof. case: P => //. Qed.

  Lemma succes_is_solved s {A}: success A -> exists B, expand s A = Solved s B.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=; case: eqP.
      + move=> H /(HB s) [B'] ->.
        rewrite (expand_is_dead_flow _ H); repeat eexists.
      + by move=> ? /(HA s) [A'] ->; repeat eexists.
    + by move=> A HA B0 HB0 B HB s /= /andP [] /(HA s) [A'] -> /(HB s) [B'] ->; repeat eexists.
  Qed. 

  Lemma is_failed_expand_is_failure s {A}: failed A -> exists A', expand s A = Failure A'.
  Proof. 
    elim: A s => //; try by eexists.
    move=> A HA s B HB s1 /toT /=. case: eqP.
    + move=> H /(HB s1) [B' HB'].
      have:= is_dead_failed H => /(HA s1) [A' HA']; rewrite HA' HB' /=.
      destruct A' => //; try by eexists.
      destruct B' => //; by eexists.
    + move=> X /(HA s1) [A'] /[dup] + ->.
      move: X => /expand_failure_not_dead_right X => /X.
      by destruct A' => //; eexists.
    + move=> A HA B0 HB0 B HB s /= /orP [].
      + by move=> /(HA s) [A'] ->; destruct A'; eexists.
      + move=> /andP[] /(succes_is_solved s) [A'] -> /(HB s) [B'] ->; repeat eexists.
  Qed.

  Lemma valid_state_dead1 {B}: dead B = B -> valid_state B = false.
  Proof. 
    elim: B=> //.
    + move=> A HA s B HB [] /HA /= -> /HB ->; destruct A =>//.
    + move=> A HA B0 _ B HB [] /HA /= ->; case: orP=> //.
   Qed.

  Lemma valid_state_expand {s A r}:
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
        + move=> [HA'[HB']] /[subst1] /simpl_valid_state_or [][].
          + move=> /[subst1]; simpl in *.
            have DB':= expand_failure_is_dead HB'.
            by rewrite (valid_state_dead1 DB').
          + by move=> DA [VA] /base_or_base_or_ko_valid; rewrite (valid_state_dead1 (expand_failure_is_dead HB')).
          + move=> s2 C /simpl_expand_or_solved [].
            + move=> [A'[HA']] /[subst1] /simpl_valid_state_or [] [].
              + move=> /[subst1] //.
              + by move=> DA [VA] /= /[dup] /base_or_base_or_ko_valid -> ->; rewrite (IHA _ _ HA' VA); destruct A' => //.
            + move=> [B'[HA'[HB']]] /[subst1] /simpl_valid_state_or [][].
              + by move=> /[subst1] VB /=; rewrite (IHB _ _ HB' VB).
              + by move=> DA [] VA /base_or_base_or_ko_valid /= VB; rewrite (IHB _ _ HB' VB).
    + move=> A IHA B0 _ B IHB s1 [].
      + move=> s2 C => /simpl_expand_and_expanded [].
        + move=> [A'[HA']] /[subst1] /=/andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 -> VA.
          rewrite (IHA _ _ HA' VA).
          case SA: success.
          + have:= succes_is_solved s1 SA; rewrite HA' => -[?] //.
          + by move=> /eqP /[subst1]; rewrite VB0 eq_refl if_same.
        + move=> [s[A'[B'[HA'[HB']]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB -> /(IHA _ _ HA') /= ->.
          by rewrite (proj1(expand_solved_success HA')) (proj2(expand_solved_success HA')) => /(IHB _ _ HB') ->.
      + move=> s2 C /simpl_expand_and_cut [].
        + move=> [A' [HA']] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid H -> /(IHA _ _ HA') ->.
          case SA: success.
          + have:= succes_is_solved s1 SA; rewrite HA' => -[?] //.
          + move=> /eqP /[subst1]; rewrite H eq_refl; case: success => //.
        + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid H -> /(IHA _ _ HA') ->.
          by rewrite (proj1(expand_solved_success HA')) (proj2(expand_solved_success HA')) => /(IHB _ _ HB') ->.
      + move=> s2 /simpl_expand_and_fail [|[]].
        + move=> [HA] /[subst1]/=.
          have:= expand_failure_is_dead HA => /valid_state_dead1 -> /andP []/andP [] //.
        + move=> [DA'[A'[HA']]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid H -> /(IHA _ _ HA') ->.
          by have:= expand_failure_failed HA' => -[] /failed_success -> /failed_success -> ->.
        + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid H -> /(IHA _ _ HA') ->.
          by rewrite (proj1(expand_solved_success HA')) (proj2(expand_solved_success HA')) => /(IHB _ _ HB') ->.
      + move=> s C /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1] /= /andP [] /andP [] /[dup] /base_and_base_and_ko_valid H -> /(IHA _ _ HA') ->.
        by rewrite (proj1(expand_solved_success HA')) (proj2(expand_solved_success HA')) => /(IHB _ _ HB') ->.
  Qed.

  (* Lemma expand_cb_failed {s1 s2 A A'}: expand s1 A = CutBrothers s2 A' -> failed A = false.
  Proof.
    elim: A s1 s2 A' => //.
    + move=> A HA s B HB A' ?? /simpl_expand_or_cut [].
    + move=> A HA B0 HB0 C HC D ? s /simpl_expand_and_cut [].
      + by move=> [A2[+]] /[subst1] /= /[dup] /HA -> /expand_cb_success ->.
      + move=> [s1[A1[A2[+[+]]]]] /[subst1] /= => + /HC ->.
        by move=> /expand_solved_failed ->; case success.
  Qed. *)

  (* Lemma full_expanded_cb {s1 s2 A A'} : 
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
  Qed. *)

  (* Lemma expand_expanded_success {s1 s2 A A'}: expand s1 A = Expanded s2 A' -> success A = false.
  Proof.
    case X: (success A) => //.
    by have [s3 [C H]]:= succes_is_solved s1 X; rewrite H.
  Qed. *)

  (* Lemma expand_expanded_failed {s1 s2 A A'}: expand s1 A = Expanded s2 A' -> failed A = false.
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
  Qed. *)

  Lemma success_cut {A} : success (cut A) = false.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      by case X: eq_op => //=; rewrite HA HB if_same.
    + move=> A HA B HB C HC /=.
      by case X: eq_op => //=; rewrite HA.
  Qed.

  (* Lemma valid_state_expanded {s s2 A A'}:
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
  Qed. *)

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> expandedP valid_state s A r.
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A1 A2 EA VA.
      apply: expandedP_done => //.
      apply: valid_state_expand EA VA.
    + move=> s A B HA HB.
      apply: expandedP_fail => //.
      apply: valid_state_expand HA HB.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand HA VA.
      apply: expandedP_cut (VA) VB (HA) (IH VB).
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand HA VA.
      apply: expandedP_step (VA) VB (HA) (IH VB).
  Qed.

  Lemma valid_state_expanded_done {s1 s2 A B}:
    valid_state A ->  expanded s1 A (Done s2 B) -> valid_state B.
  Proof.
    remember (Done _ _) as D eqn:HD => + [b H].
    elim: H s2 B HD => //; clear.
    + move=> s1 s2 A B HA s3 C [] /[subst2].
      apply: valid_state_expand HA.
    + move=> s1 s2 r A B b HA HB + s3 C ? /(valid_state_expand HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
    + move=> s1 s2 r A B b HA HB + s3 C ? /(valid_state_expand HA) VB /[subst].
      by move=> /(_ _ _ erefl VB).
  Qed.

  Lemma valid_state_expanded_valid_state {s1 A B}:
    valid_state A ->  expanded s1 A (Failed B) -> valid_state B.
  Proof.
    remember (Failed _) as D eqn:HD => + [b H].
    elim: H B HD => //; clear.
    + move=> s1 A B HA s3 [] /[subst1].
      apply: valid_state_expand HA.
    + move=> s1 s2 r A B b HA HB + C ? /(valid_state_expand HA) VB /[subst].
      by move=> /(_ _ erefl VB).
    + move=> s1 s2 r A B b HA HB + C ? /(valid_state_expand HA) VB /[subst].
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
      + move=> A HA s B HB s1 C /simpl_expand_or_fail [|[]].
        + move=> [A'[HA'[DA']]] /[subst1] /simpl_valid_state_or [].
          + move=> [] /[subst1]; simpl in HA'; congruence.
          + move=> [] DA [] /(HA _ _ HA') /= ->.
            have:= (expand_failure_not_dead_left HA' DA'); case: eqP => // H H1.
            have:= (expand_failure_not_dead_right HA' H1) => //.
        + move=> [B'[DB']] [] /HA {}HA [] /HB {}HB /[subst1] /=.
          by destruct A; auto => /andP [] _ /base_or_base_or_ko_valid; auto.
        + move=> [] _ [] _ /[subst1] //.
      + move=> A HA B0 _ B HB s C /simpl_expand_and_fail [|[]].
        + move=> []/[dup]DA H /[subst1] //.
        + move=> [A'[?[HA']]] /[subst1] /=/andP [] /andP [] /[dup] /base_and_base_and_ko_valid VB0 H.
          by have:= expand_failure_failed HA' => -[] /failed_success -> /failed_success -> /(HA _ _ HA') -> /=.
        + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] /= /andP[/andP[]].
          rewrite (proj1(expand_solved_success HA')) (proj2(expand_solved_success HA')) => _ VA VB.
          by rewrite (HB _ _ HB' VB) orbT.
    + move=> ?????? H H1 IH ? /[subst1] H2 ; apply: IH erefl (valid_state_expand H H2).
    + move=> ?????? H H1 IH ? /[subst1] H2; apply: IH erefl (valid_state_expand H H2).
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
    + move=> A HA s B HB b s1 s2 C /simpl_valid_state_or [].
      + move=> [] /[subst1] /HB {}HB /=.
        by case X: next_alt_aux => // [[s3 D]] ; move: X => /HB {}HB; destruct D => // -[]/[subst2]//.
      + move=> [] DA [] /[dup] VA /HA {}HA /[dup] VBa /base_or_base_or_ko_valid /[dup] VB /HB{}HB /simpl_next_alt_aux_some [|[]].
        + by move=> [B'[?[+]]] /[subst1] => /HB /= ->.
        + by move=> [A'[_ [+]]] /[subst1] /HA /= ->; rewrite VB VBa; destruct A'.
        + by move=> [_ [NA]] /[subst1] /=.
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
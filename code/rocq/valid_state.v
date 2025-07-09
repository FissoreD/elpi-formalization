From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Include Run.
  
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
    | Or l _ r => valid_state l && (base_or r || base_or_ko r)
    | And l r0 r => 
      valid_state l && (base_and r0 || base_and_ko r0) && if success l then valid_state r else (r0 == r)
    end.

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

  Lemma base_or_aux_big_and {pr l} : base_or_aux (big_and pr l).
  Proof. by elim: l => //= _ ??; rewrite eq_refl base_and_big_and. Qed.

  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof. elim: l => // x xs /=; by rewrite base_and_big_and eq_refl. Qed.

  Lemma base_or_big_and {pr l} : base_or (big_and pr l).
  Proof. case: l; rewrite /base_or // => ??; by rewrite base_or_aux_big_and. Qed.

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
      by move=> /[dup] H => ->; case A => //=; auto.
    + move=> A HA B HB C HC; rewrite /base_or => /orP []//=; case: A HA => //.
      move=> p a H /andP [] /eqP -> H1 ; move:(H1) ->; move: H1 => /base_and_valid ->; rewrite eq_refl//.
  Qed.

  Lemma dead_big_or p s t: big_or p s t <> dead (big_or p s t).
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
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

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof. by case: B => //= -[] //= A B /andP[]/eqP->->; rewrite eq_refl orbT. Qed.

  Lemma base_and_base_and_ko_valid {B}:
    base_and B || base_and_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_and_valid | move=> /base_and_ko_valid] => ->. Qed.

  Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B /\ (base_and B0 || base_and_ko B0).
  Proof. move=>/=/andP[]/andP[]//=> ->/[dup]/base_and_base_and_ko_valid + ->; case:success => // + /eqP <-//. Qed.

  Lemma simpl_valid_state_and1 {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ base_and B0 || base_and_ko B0 /\ (if success A then valid_state B else B0 == B).
  Proof. move=>/=/andP[]/andP[]// => ->/[dup]/base_and_base_and_ko_valid + ->; case:success => // + /eqP <-//. Qed.

  Lemma base_or_ko_valid {B}: base_or_ko B -> valid_state B.
  Proof.
    rewrite /base_or_ko => /orP [].
    + by move=> /eqP ->.
    + elim: B => //.
      + move=> A HA s B HB /= /andP [] /base_and_ko_valid ->.
        rewrite /base_or_ko /base_or.
        move=> /[dup] /HB -> ->.
        by rewrite 2!orbT; destruct A.
      + by move=> [] // HA B0 HB0 B HB /= /andP [] /[dup] /eqP -> _ ->; rewrite eq_refl orbT.
  Qed.

  Lemma base_or_base_or_ko_valid {B}:
    base_or B || base_or_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_or_valid | move=> /base_or_ko_valid] => ->. Qed.

  Lemma valid_state_is_not_dead A: valid_state A -> A <> dead A.
  Proof. 
    elim: A => //.
    move=> A HA s B HB /simpl_valid_state_or[].
      move=> [] -> /HB + []//.
    move=>[]+[]/HA++[]//.
  Qed.

  Lemma expand_failure_dead s1 {A}: valid_state A -> expand s1 A <> Failure Dead.
  Proof.
    elim: A s1 => //.
    + move=> /= p [] //.
    + move=> A HA s B HB s1 /simpl_valid_state_or[].
        by move=> [] ->/=/(HB s1) ; case X: expand => //= [[]]//.
      move=>[] DA[]/HA{}HA/base_or_base_or_ko_valid/HB{}HB.
      move=> /simpl_expand_or_fail[].
        by move=> [? []] + []//.
      move=> [].
        by move=> []+[]+[]+[]//.
      by move=> []+[]//; have:= (HA s1).
    + move=> A HA B0 _ B HB s1 /simpl_valid_state_and[]/HA{}HA[]/HB{}HB _.
      move=>/simpl_expand_and_fail[].
        by move=> []//; have:= HA s1.
      move=> [].
        by move=> []+[]+[]//.
      move=> []s'[]A'[]B'[]H1[]H2.
      case: eqP => ///[subst1].
      by have:= HB s'.
    Qed.

  Lemma success_dead {A}: success (dead A) = false.
  Proof. by elim: A=> // A HA s B HB /=; rewrite HA HB if_same. Qed.

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
    case: A => //= _ _ _ HB HC /andP [] /eqP <- /HB.
    by rewrite eq_refl.
  Qed.


  Lemma base_or_base_or_ko_cut {B}: base_or B -> base_or_ko (cut B).
  Proof.
    rewrite /base_or /base_or_ko => /orP []; [by case B |].
    elim: B => //.
    + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cut.
      move=> -> /IHB /orP[/eqP->|]//.
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP /[subst1].
      by rewrite eq_refl => /base_and_base_and_ko_cut. 
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
      + move=> A HA s B HB /= /andP[]/base_and_ko_cut->/HB/orP[/eqP->|]//.
      + move=> [] //= HA B0 HB0 B HB/andP[]/eqP/[subst1].
        rewrite eq_refl.
        apply: base_and_ko_cut.
  Qed.

  Lemma cut_dead1 {A}: cut A = dead A -> A = dead A.
  Proof. by elim: A=> // A HA s B HB[]/=/HA<-/HB<-. Qed.
  

  Lemma expand_not_dead {s A r}: 
    valid_state A -> expand s A = r -> get_state r <> dead (get_state r).
  Proof.
    elim: A s r; try by move=> //= _ r _ <-//.
    + by move=> p [|t] s r _ <- //=; apply dead_big_or.
    + move=> A HA s B HB s1 => // C /simpl_valid_state_or [].
        move=> []->/= VB <-.
        have {}HB:= HB _ _ VB.
        case X: expand => //=; have:= HB _ _ X => /=; try congruence.
        by move=> H; case: ifP => /eqP H1; subst => //= -[]//.
      move=> [DA[VA VB]].
      case: C.
      + move=> s2 C /simpl_expand_or_expanded [].
          by move=> [A'[+]] /[subst1] /HA => /(_ VA) /=; congruence.
        move=> [].
          by move=> [A'[]] /HA => /(_ VA)/= HA' -> /=; rewrite dead_cut_is_dead; congruence.
        move=> [H [B']] []-> []/HB => /(_ (base_or_base_or_ko_valid VB))/=; try congruence.
      + move=> s2 C /simpl_expand_or_cut [s3[B'[?]]]; subst => //.
      + move=> C /simpl_expand_or_fail[].
          move=>[A'[HA'[DA']]]->/=.
          have:= HA _ _ VA HA' => /=; congruence.
        move=>[].
          move=> [B'[DB'[HA'[HB']]]] -> /=; have:= HB _ _ (base_or_base_or_ko_valid VB) HB' => /=; congruence.
        move=> [HA'[HB' DD]].
        by have:= HA _ _ VA HA'.
      + move=> s2 C /simpl_expand_or_solved [].
          move=> [A'[]] /HA{} => /(_ VA) /= H ->/=; congruence.
        move=> [B'[HA'[]]] /HB => /(_ (base_or_base_or_ko_valid VB)) /= + ->/=; congruence.
    + move=> A HA B0 HB0 B HB s1 r /simpl_valid_state_and[]/[dup]VA/HA{}HA[]/[dup]VB/HB{}HB _.
      case: r.
      + move=> s2 C /simpl_expand_and_expanded [].
          by move=> [A'][] /HA H1 -> //.
        move=> [s'[A'[B'[]]]] /HA /= +[] _ ->//.
      + move=> s2 C /simpl_expand_and_cut [].
          move=> [A'][] /HA /= + ->//.
        move=> [s'[A'[B'[]]]] /HA/= + [] _->//.
      + move=> C /simpl_expand_and_fail [].
          by move=> []/HA//.
        move=>[].
          by move=> [A'[DA[]]] /= + ->//.
        move=> [s'[A'[B'[]]]]/HA/=+[]/HB/=.
        case: ifP => /eqP ? + + ->; subst => /=; try congruence.
      + move=> s2 C /simpl_expand_and_solved [s'[A'[B']]] []/HA.
        by move=>/= + []/HB/= + <-.
  Qed.

  Lemma valid_state_dead {A}: valid_state (dead A) = false.
  Proof. by elim: A => // A HA s B HB/=; rewrite HA HB; case: dead. Qed.

  Lemma succes_is_solved s {A}: valid_state A -> success A -> exists B, expand s A = Solved s B.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
      case: ifP => /eqP.
      + move=> ->; rewrite valid_state_dead; case X: (dead A) => // H1 H2 /=.
        have [C H]:= HB s H1 H2.
        by eexists; rewrite H => //.
      + move=> DA H.
        have {H}: (valid_state A && (base_or B || base_or_ko B)).
          destruct A => //.
        move=>/andP[]VA VB SA.
        have [A' H]:= HA s VA SA.
        by rewrite H; eexists.
    + move=> A HA B0 HB0 B HB s /simpl_valid_state_and[VA[VB _]] /=/andP[SA SB].
      have [A' H1]:= HA s VA SA; rewrite H1.
      have [B' H2]:= HB s VB SB; rewrite H2.
      by eexists.
  Qed. 

  Lemma expand_solved_failed {s1 A s2 B}: valid_state A -> expand s1 A = Solved s2 B -> failed A = false /\ failed B = false.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> ???? [] /[subst2]; repeat split.
    + move=> ?[]//.
    + move=> A HA s B HB s1 s2 C /simpl_valid_state_or[].
        move=> []->/=/HB{}HB; case X: expand => //= -[] _ <-/=; apply: HB X.
      move=> [] H []/[dup]VA/HA{}HA/base_or_base_or_ko_valid/HB{}HB/simpl_expand_or_solved [].
      + move=> [A'[+]] /[subst1] /=/[dup] /HA []->-> /(expand_not_dead VA) /=.
        repeat case: eqP => //.
        by move: VA => + DA H1; rewrite H1 valid_state_dead.
      + move=> [A'[]]/= + [] /HB[] /= -> + -> /= => + ->.
        by have:= expand_failure_dead s1 VA.
    + move=> A HA B0 _ B HB s1 s2 C + /simpl_expand_and_solved [s3 [A' [B' ]]][]/HA{}HA[]/HB{}HB.
      move=> /simpl_valid_state_and[]/HA []/= + + [] /HB[] + + _ <- /==> ->->->->.
      repeat case: success => //.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: valid_state A -> expand s1 A = Solved s2 B -> success A /\ success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ???? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB s1 s2 C /simpl_valid_state_or[].
        move=> [] -> /=/HB{}HB; case X: expand => //= -[] _ <-; move: X => /HB //.
      move=> []H[]/[dup] VA/HA{}HA/[dup]BB/base_or_base_or_ko_valid/HB{}HB/simpl_expand_or_solved [].
        move=> [A'] [] +  /[subst1] /[dup] + /HA[] /=->-> => /(expand_not_dead VA)/=; do 2 case: eqP =>//.
        by move: VA => + _ H1; rewrite H1 valid_state_dead.
      move=> [B'[H1]].
      by have:= expand_failure_dead s1 VA.
    + move=> A HA ? _ B HB s1 s2 C /simpl_valid_state_and[]/[dup]VA/HA{}HA[]/HB{}HB _.
      by move=> /simpl_expand_and_solved [s3 [A' [B']]] [] /HA [] + + [] /HB [] + + <- /= => ->->->->.
  Qed.

  Lemma expand_failure_not_dead_right {s1 A B}: valid_state A -> expand s1 A = Failure B -> (A <> dead A) -> (B <> dead B).
  Proof.
    elim: A B s1 => //.
    + by move=> ??? [] /[subst1] //.
    + by move=> ? [] //.
    + move=> A HA s B HB C s1 /simpl_valid_state_or [].
        move=> []->/[dup]VB /HB{}HB/=.
        case X: expand => // [D]-[] <-.
        move: X => /HB H H1.
        have {H1}: B <> dead B.
          move=> HH; apply: H1 => []; congruence.
        move=> /H; case: eqP.
          move=> ->//.
        move=> /= _ H2 []; auto.
      move=> []DA[]/[dup]/HA{}HA VA /base_or_base_or_ko_valid /[dup] VB /HB{}HB /simpl_expand_or_fail [].
        move=> [A'[]]/[dup]HH/HA{}HA[] H1-> /= H2 [] H3 H4.
        by move: VB; rewrite H4; rewrite valid_state_dead.
      move=> [].
        move=> [B'[+]] [] /HA{}HA[]/HB{}HB/=->/= + [] H.
        have: B <> dead B.
          by move=> H1; move: VB; rewrite H1 valid_state_dead.
        by move=> /HB.
      move=> []/HA {}HA; 
      have: A <> dead A.
        move: VA => + H; rewrite H valid_state_dead//.
      move=> /HA//.
    + move=> A HA B0 HB0 B HB C s1 /simpl_valid_state_and[]/[dup]VA/HA{}HA[]/[dup]VB/HB{}HB BB /simpl_expand_and_fail [].
        move=> [] /HA{}HA.
        have: A <> dead A.
          by move: VA => + H; rewrite H valid_state_dead//.
        move=> /HA//.
      move=> [].
        move=> [A'[DA[HA']]] -> //.
      move=> [s'[A'[B'[]]]] + [] /HB{}HB.      
      have: B <> dead B.
        move: VB => + H; rewrite H valid_state_dead//.
      move=> /HB{}HB + ->.
      case: eqP => //=.
        by move=> /[subst1]//.
  Qed.


  Lemma expand_failure_failed {s1 A B}:
    valid_state A -> expand s1 A = Failure B -> failed A /\ failed B.
  Proof.
    elim: A s1 B; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2 C /simpl_valid_state_or[].
        move=> [] ->/=; case X: expand => //= /HB{}HB [] <-; move: X=>/HB[]->.
        by case: eqP => //.
      move=> [DA] [] /[dup] VA /HA{}HA/[dup]BB/base_or_base_or_ko_valid/HB{}HB/simpl_expand_or_fail [].
        move=> [A' [+[HD]]] /[subst1] /= => /[dup].
        move=> /HA [] -> ->; move: VA; case: eqP.
          by move=> ->; rewrite valid_state_dead.
        move=> /expand_failure_not_dead_right{}HA/HA{}HA/HA.
        by case: eqP => //.
      move=>[].
        move=> [B'[HD[+[+]]]]  /[subst1] /=.
        by move=> /HA [] -> _ /HB [] -> ->; rewrite if_same.
      by move=> [+[+]] /[subst1] /= => /HA [] -> _ /HB [] -> _; rewrite if_same.
    + move=> A HA B0 _ B HB s C/simpl_valid_state_and[]/[dup]VA/HA{}HA[]/[dup]VB/HB{}HB BB.
      move=> /simpl_expand_and_fail[].
        by move=> [] /HA [] /= -> _ ->.
      move=> [].
        by move=> [?[A'[+]]]  /[subst1] /= /HA [] -> ->.
      move=> [s' [A' [B' [+ [+]]]]] /[subst1] /=.
      case: eqP.
        by move: VA => /expand_solved_success{}HA -> /HA[] -> ? /HB[]->/=; rewrite orbT.
      by move: VA => /expand_solved_success{}HA _/HA [] /= -> -> /HB [] -> ->; rewrite !orbT.
  Qed. 

  Lemma success_cut {A} : success A = success (cut A).
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      rewrite dead_cut_is_dead.
      case: eqP.
        move=>->; rewrite cut_dead_is_dead dead_dead_same eq_refl//.
      case: eqP.
        move=> /cut_dead1//.
      move=> //.
    + move=> A HA B HB C HC /=.
      by rewrite HA HC.
  Qed.

  Lemma valid_state_cut {A}: valid_state A -> valid_state (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/simpl_valid_state_or[].
        by move=>[]->/=.
      move=> []/=DA[]/HA->/[dup] /base_or_base_or_ko_valid/HB->.
      by move=> /orP[/base_or_base_or_ko_cut|/base_or_ko_cut] ->; rewrite orbT; case cut.
    move=> A HA B0 HB0 B HB /=/andP[]/andP[]/HA -> H.
    have: base_and_ko (cut B0).
      move: H => /orP [/base_and_base_and_ko_cut|/base_and_ko_cut] //.
    move=>->; rewrite orbT -success_cut.
    by case: success => ///eqP->; rewrite eq_refl.
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
          + move=> /[subst1] /(IHB _ _ HB') //.
          + move=> DA [VA] /base_or_base_or_ko_valid.
            by move=> /(IHB _ _ HB').
          + move=> s2 C /simpl_expand_or_solved [].
            + move=> [A'[HA']] /[subst1] /simpl_valid_state_or [] [].
              + move=> /[subst1] //.
              + by move=> DA [VA] /= /[dup] /base_or_base_or_ko_valid -> ->; rewrite (IHA _ _ HA' VA); destruct A' => //.
            + move=> [B'[HA'[HB']]] /[subst1] /simpl_valid_state_or [][].
              + by move=> /[subst1] VB /=; rewrite (IHB _ _ HB' VB).
              + by move=> DA [] VA /base_or_base_or_ko_valid /= VB; rewrite (IHB _ _ HB' VB).
    + move=> A IHA B0 HB0 B IHB s1 [].
      + move=> s2 C => /simpl_expand_and_expanded [].
          move=> [A'[HA']] /[subst1] /=/andP [] /andP [] VA /[dup] /base_and_base_and_ko_valid VB0.
          rewrite (IHA _ _ HA' VA) => /[dup]+->/=.
            case SA: success.
              have:= succes_is_solved s1 VA SA; rewrite HA' => -[?] //.
            by move=> _ /eqP /[subst1]; rewrite VB0 eq_refl if_same.
        move=> [s[A'[B']]] [] /[dup] /expand_solved_success H1 /IHA{}IHA[]/IHB{}IHB /[subst1].
        move=> /simpl_valid_state_and[] /[dup]/expand_solved_success H /[dup].
        by move=> /H1 [] /= _ -> /IHA /= -> []/IHB-> ->.
      + move=> s2 C /simpl_expand_and_cut [].
          move=> [A' [HA']] /[subst1] /= /andP [] /andP [] /[dup] VA /(IHA _ _ HA') -> /[dup] /base_and_base_and_ko_valid H ->.
          case SA: success.
            have:= succes_is_solved s1 VA SA; rewrite HA' => -[?] //.
          move=> /eqP /[subst1]; rewrite H eq_refl; case: success => //.
        move=> [s'[A'[B']]] [] + [] + -> /simpl_valid_state_and1 [] /[dup]VA/IHA {}IHA [] /[dup] /= /base_and_base_and_ko_valid /HB0{}HB0 ->.
        by rewrite -!success_cut => /[dup]/(expand_solved_success VA)[]->-> /IHA/valid_state_cut-> /IHB{}IHB/IHB->.
      + move=> s2 /simpl_expand_and_fail [].
          by move=> [] /expand_failure_dead H _ /simpl_valid_state_and1 [] /H.
        move=> [].
          move=> [DA'[A']] [] /[dup] HH /IHA{}IHA /[subst1] /=/andP [] /andP[] /[dup] /IHA -> + ->.
          move: HH => /expand_failure_failed{}HA/HA[] /failed_success->/failed_success->->//.
        move=> [s'[A'[B'[HA'[HB']]]]] /[subst1] /simpl_valid_state_and [] /[dup] + /(IHA _ _ HA')/= + [].
        move: HA' => /expand_solved_success H1 /H1[] _.
        move: HB' => /IHB{}IHB + + /IHB.
        by case: eqP => [->|]//= _ ->->->->.
      + move=> s C /simpl_expand_and_solved [s'[A'[B'[]]]] /[dup]/expand_solved_success H. 
        by move=> /IHA{}IHA [] /IHB{}IHB<- /simpl_valid_state_and [] /[dup] /H []/= _ -> /IHA -> []/IHB/= ->->.
  Qed.

  Lemma expand_failure_not_dead_left {s1 A B}: valid_state A -> expand s1 A = Failure B -> B <> Dead -> A <> dead A.
  Proof.
    elim: A B => //.
    + move=> A HA s B HB C VA /simpl_expand_or_fail [|[]].
      + move=> [A'[HA'[?]]] /[subst1] /= H -[] H1 H2.
        by move: VA; rewrite H1 H2; rewrite (@valid_state_dead (Or A s B)).
      + move=> [B'[?[HA'[HB']]]] /[subst1] /= H [] H1 H2.
        by move: VA; rewrite H1 H2; rewrite (@valid_state_dead (Or A s B)).
      + move=> [+[]] => //.
  Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      rewrite valid_state_big_and base_or_big_or_aux IH; case: big_and => //.
  Qed.

  Lemma toT {P}: P = true -> is_true P.
  Proof. case: P => //. Qed.

  Definition get_state_run r := match r with Done _ s => s | Failed s => s end.

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> valid_state (get_state_run r).
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A1 A2 EA VA /=.
      apply: valid_state_expand EA VA.
    + move=> s A B HA HB /=.
      apply: valid_state_expand HA HB.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand HA VA.
      apply: IH VB.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand HA VA.
      apply: (IH VB).
  Qed.

  Lemma valid_state_expanded {s1 A r}:
    valid_state A ->  expanded s1 A r -> valid_state (get_state_run r).
  Proof.
    move=> + [b H].
    elim: H; clear.
    + move=> s1 s2 A B HA VA /=; apply: valid_state_expand HA VA.
    + move=> s A B HA VA; apply: valid_state_expand HA VA.
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand HA VA)).
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand HA VA)).
  Qed.

  Lemma next_alt_aux_base_and {s1 s2 A B}:
     base_and A || base_and_ko A ->  next_alt_aux true s1 A = Some (s2, B) -> A = B.
  Proof.
    elim: A s1 s2 B => //; move=> [] //.
    + move=> _ B0 HB0 B HB s1 s2 C /= /andP [] /eqP /[subst1] BA.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      rewrite BA in HB.
      by rewrite (HB _ _ _ _ NB)//orbT.
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
      move=> /= /andP [] /andP [] VA /[dup] /base_and_base_and_ko_valid VB0 BB.
      case SA: success.
      + move=> VB.
        case NB: next_alt_aux => [[ ]|].
        + by move=> [] /[subst2] /= ; rewrite VA (HB _ _ _ _ VB NB) BB SA.
        + case NA: next_alt_aux => [[ ]|] // [] /[subst2] /=.
           by rewrite (HA _ _ _ _ VA NA) BB eq_refl VB0 if_same.
      + move=> /eqP /[subst1].
        case NB: next_alt_aux => [[s3 D]|].
        + by move=> [] /[subst2] /=; rewrite SA VA BB (next_alt_aux_base_and BB NB) eq_refl.
        + case NA: next_alt_aux => // [[ ]] [] /[subst2] /=.
          by rewrite (HA _ _ _ _ VA NA) eq_refl BB VB0 if_same.
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
    valid_state A -> run s A r -> valid_state (get_state_run r).
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A B b EA VA.
      have H := valid_state_expanded VA (ex_intro _ _ EA).
      exact H.
    + move=> s A B b HA HB VA.
      apply: valid_state_expanded VA (ex_intro _ _ HA).
    + move=> s s' r A B C b1 b2 b3 HA HB HC IH Hb VA.
      have VB := valid_state_expanded VA (ex_intro _ _ HA).
      have NA := valid_state_next_alt HB VB.
      apply: IH NA.
    Qed.

End valid_state.
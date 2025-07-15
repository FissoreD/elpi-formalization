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

  Definition base_or s := 
    match s with 
    | Bot => true
    | Or Bot _ t => base_or_aux t
    | _ => false
    end.

  Fixpoint base_and_ko s :=
    match s with
    | And KO r r1 => [&&base_and r, (cut r == r1) & base_and_ko r1] (* should also say something about the program *)
    | KO => true
    | _ => false
    end.

  Fixpoint base_or_aux_ko s :=
    match s with
    | Or l _ r => base_and_ko l && (base_or_aux_ko r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and_ko t
    end.

  (* same_structure_and *)
  Section ssa.
    Fixpoint ssa A B :=
      match A, B with
      | And _ _ _, Or _ _ _ => false
      | And _ _ _, Dead => true
      | And _ _ A, And _ _ B => ssa A B
      | Top, (Top|OK|KO) => true
      | _, _ => false
      end.
    Lemma ssa_id {A}: base_and A -> ssa A A.
    Proof. by elim: A =>// -[]// p a _ B0 HB0 B HB/=/andP[] _. Qed.

    Lemma ssa_cut {A}: base_and A -> ssa A (cut A).
    Proof. by elim: A =>// -[]// p a _ B0 HB0 B HB/=/andP[] _. Qed.

    Lemma ssa_cut1 {A B}: ssa A B -> ssa A (cut B).
    Proof.
      elim: A B => //.
        move=> []//.
      move=> A HA B0 _ B HB[]//.
    Qed.

    Lemma ssa_cut2 {A B}: base_and B -> ssa A (cut B) -> ssa A B.
    Proof.
      elim: A B => //.
        move=> []//.
      move=> A HA B0 _ B HB[]//[]//.
      move=> p a s1 s2/=/andP[]/eqP?;subst.
      apply: HB.
    Qed.

    (* Lemma xxx {B C D}: ssa B C -> ssa D C -> ssa B D.
    Proof.
      elim: B C D => //.
      + move=>[]//[]//.
      + move=> A HA B0 HB0 B HB[]//.
          move=> [] //=. *)

    Lemma ssa_expand {B0 B s r}: base_and B0 -> ssa B0 B -> expand s B = r -> ssa B0 (get_state r).
    Proof.
      elim: B0 B s r => //.
        move=>[]//s []//.
        - move=> ? _ _ [] <-//.
        - move=> ?? _ _ [] <-//<-//.
        - move=> ?? _ _ [] <-//<-//.
      move=> []// p a _ A HA B0 HB0 []//A' B0' B' s.
        move=>/=<-//.
      move=> r /= /andP[/eqP <-] bA ssA.
      case: r.
      + move=> s1 C /simpl_expand_and_expanded[].
          move=>[A2[HA' ->]]//.
        move=>[s' [A2 [B2 [HA' [HB' ->]]]]]//=.
        apply: HA _ _ _ bA ssA HB'.
      + move=> s1 C /simpl_expand_and_cut[].
          move=>[A2 [HA' ->]]//.
        move=> [s'[A2[B2 [HA'[HB' ->]]]]]/=.
        apply: HA _ _ _ bA ssA HB'.
      + move=> C /simpl_expand_and_fail[].
          move=> [HA' ->]//=.
        move=>[].
          move=> [A2 [DA[HA' ->]]]//.
        move=> [s'[A2[B2[HA'[HB' ->]]]]]/=.
        case: ifP => ///eqP H .
        by rewrite (HA _ _ _ bA ssA HB').
      + move=> s1 C /simpl_expand_and_solved.
        move=> [s'[A1[B1[HA'[HB' <-]]]]]/=.
        by have /= := (HA _ _ _ bA ssA HB').
    Qed.
  End ssa.

  
  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Bot | Top => true
    | Dead => false
    | Or Dead _ r => valid_state r
    | Or l _ r => valid_state l && (base_or_aux r || base_or_aux_ko r)
    | And l r0 r => 
      [&& valid_state l, 
        if success l then valid_state r else ((r0 == r) || (cut r0 == r)),
        ssa r0 r &
        (base_and r0)]
    end.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA; rewrite (HVA HA) /=.
    by rewrite HA eq_refl (ssa_id HA).
  Qed.

  Lemma base_and_big_and {pr A}: base_and (big_and pr A).
  Proof. by elim: A => // a l /= ->; rewrite eq_refl. Qed.

  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof.
    elim: l => // x xs /=.
    by rewrite base_and_big_and eq_refl/= (ssa_id base_and_big_and).
  Qed.

  Lemma base_or_big_and {pr l} : base_or_aux (big_and pr l).
  Proof. case: l; rewrite /base_or_aux //= => ??; by rewrite base_and_big_and eqxx. Qed.

  Lemma base_or_big_or_aux {pr s l}: base_or_aux (big_or_aux pr s l).
  Proof.
    elim: l s => //=; clear.
    + move=> ?; apply: base_or_big_and.
    + by move=> [[s r] rs] IH r1 /=; rewrite IH base_and_big_and.
  Qed.

  Lemma base_or_valid {A} : base_or_aux A -> valid_state A.
  Proof.
    elim A => //; clear.
    + move=> A HA s B HB/=/andP[]/base_and_valid->/[dup]/HB->->; destruct A => //.
    + by move=> []// p a Ha B0 HB0 B HB /=/andP[/eqP->]bB; rewrite eqxx bB (ssa_id bB).
  Qed.

  Lemma dead_big_or p s t: big_or p s t <> dead (big_or p s t).
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
  Qed.

  Lemma simpl_valid_state_or {s A B}: valid_state (Or A s B) -> (A = Dead /\ valid_state B) \/ (A <> Dead /\ valid_state A /\ (base_or_aux B || base_or_aux_ko B)).
  Proof.
    move=> /=; case: A => //.
    all: try by move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; left => //.
    + move=> ?? /orP [] ->; right; repeat split => //; rewrite orbT //.
    + move=> ??? /andP [] H ->; right => //.
    + move=> ??? /andP [] H ->; right => //.
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof.
    elim: B => //.
    by move=> []// HA B0 _ B HB/=/and3P[bB0 /eqP <-]; rewrite bB0 eqxx orbT (ssa_cut bB0).
  Qed.

  Lemma simpl_valid_state_and1 {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ (if success A then valid_state B else (B0 == B) || (cut B0 == B)) /\ ssa B0 B /\ base_and B0.
  Proof. by move=>/=/and3P[]//->->/andP[]->->. Qed.


  Lemma base_or_ko_valid {B}: base_or_aux_ko B -> valid_state B.
  Proof.
    elim: B => //.
    + move=> A HA s B HB /= /andP [] /base_and_ko_valid ->.
      move=> /[dup] /HB -> ->.
      by rewrite !orbT; destruct A.
    + by move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-; rewrite eq_refl bB0 orbT (ssa_cut bB0).
  Qed.


  Lemma base_or_base_or_ko_valid {B}:
    base_or_aux B || base_or_aux_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_or_valid | move=> /base_or_ko_valid] => ->. Qed.


  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cut B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //= _ _ _ HB HC /andP [] /eqP <- hB.
    by rewrite hB (HB hB) eqxx.
  Qed.

  Lemma base_or_base_or_ko_cut {B}: base_or_aux B -> base_or_aux_ko (cut B).
  Proof.
    elim: B => //.
    + by move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cut -> /IHB ->.
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP /[subst1] hC.
      by rewrite eq_refl hC (base_and_base_and_ko_cut hC). 
  Qed.

  Lemma base_and_ko_cut {B}: base_and_ko B -> base_and_ko (cut B).
  Proof.
    elim: B => //.
    move=> []// _ B _ C HC /= /and3P[] bB /eqP <-.
    by rewrite cut_cut_same eqxx bB => ->.
  Qed.
  
  Lemma base_or_ko_cut {B}: base_or_aux_ko B -> base_or_aux_ko (cut B).
  Proof.
    elim: B => //.
      by move=> A HA s B HB /= /andP[]/base_and_ko_cut->/HB->.
    move=> [] //= _ B0 _ B HB /and3P[] bB /eqP<-.
    by rewrite cut_cut_same bB eqxx => ->.
  Qed.

  Lemma cut_dead1 {A}: cut A = dead A -> A = dead A.
  Proof. by elim: A=> // A HA s B HB[]/=/HA<-/HB<-. Qed.

  Lemma success_cut {A} : success (cut A) = success A.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      rewrite dead_cut_is_dead.
      case: eqP.
        move=> /cut_dead1//.
        move=>->; rewrite dead_dead_same eq_refl//.
      by case: eqP => //->; rewrite dead_dead_same cut_dead_is_dead.
    + move=> A HA B HB C HC /=.
      by rewrite HA HC.
  Qed.

  Lemma valid_state_cut {A}: valid_state A -> valid_state (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/simpl_valid_state_or[].
        by move=>[]->/=.
      move=> [DA[VA bB]]/=.
      rewrite (HA VA) (HB (base_or_base_or_ko_valid bB)).
      move: bB => /orP[/base_or_base_or_ko_cut | /base_or_ko_cut]->; rewrite orbT; destruct A => //.
    move=> A HA B0 _ B HB /=/simpl_valid_state_and1[VA [+ [ssaB0 bB0]]].
    rewrite (HA VA) success_cut bB0 andbT/=.
    case: ifP => //.
      move=>// _ VB. rewrite (HB VB) ssa_cut1//.
    move=> _/orP[].
      move=>/eqP?;subst; rewrite eqxx orbT (ssa_cut)//.
    move=>/eqP<-; rewrite cut_cut_same eqxx orbT ssa_cut//.
  Qed.

  Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else ((B02 == B2) || (cut B02 == B2))) ->
      base_and B02  ->
        valid_state B2.
  Proof. 
    case: success => //.
      move=>/orP[].
        move=>/eqP->; apply: base_and_valid.
      move=>/eqP<-/base_and_valid.
      apply: valid_state_cut.  
  Qed.
  (* Lemma base_and_base_and_ko_valid {B}:
    base_and B || base_and_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_and_valid | move=> /base_and_ko_valid] => ->. Qed. *)



  Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B.
  Proof.
    move=>/= /and3P[]//=> ->; case:success => ///orP[]/eqP<-/andP[] _.
      move=>/base_and_valid//.
    by move=>/base_and_valid /valid_state_cut->.
  Qed.


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
    + move=> A HA B0 _ B HB s1 /simpl_valid_state_and[VA VB].
      move=>/simpl_expand_and_fail[].
        by move=>[]; have:= HA s1 VA.
      move=> [].
        by move=> []+[]+[]//.
      move=> []s'[]A'[]B'[]H1[]H2.
      case: eqP => ///[subst1].
      by have:= HB s' VB.
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
    + move=> A HA B0 HB0 B HB s1 r /simpl_valid_state_and[] VA VB.
      case: r.
      + move=> s2 C /simpl_expand_and_expanded [].
          by move=> [A'][] /HA H1 -> //.
        move=> [s'[A'[B'[]]]] /HA /= +[] _ ->//.
      + move=> s2 C /simpl_expand_and_cut [].
          move=> [A'][] /HA /= + ->//.
        move=> [s'[A'[B'[]]]] /HA/= + [] _->//.
      + move=> C /simpl_expand_and_fail [].
          move=> [] H; have:= HA _ _ VA H => //.
        move=>[].
          by move=> [A'[DA[]]] /= + ->//.
        move=> [s'[A'[B'[HA' [HB']]]]]->/=.
        by case: ifP => /eqP?;subst => //; have:= HB _ _ VB HB'.
      + move=> s2 C /simpl_expand_and_solved [s'[A'[B']]] [].
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
        have {H}: (valid_state A && (base_or_aux B || base_or_aux_ko B)).
          destruct A => //.
        move=>/andP[]VA VB SA.
        have [A' H]:= HA s VA SA.
        by rewrite H; eexists.
    + move=> A HA B0 HB0 B HB s /simpl_valid_state_and[] VA VB /=/andP[SA SB].
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
      move=> /simpl_valid_state_and[]VA VB <-/=.
      have:= HA VA => -[]->->.
      have:= HB VB => -[]->->.
      do 2 case: success => //.
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
    + move=> A HA ? _ B HB s1 s2 C /simpl_valid_state_and[VA VB].
      move=> /simpl_expand_and_solved [s3 [A' [B'[HA' [HB' <-]]]]]/=.
      have:= HA _ _ _ VA HA' => -[] ->->.
      by have:= HB _ _ _ VB HB' => -[] ->->.
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
    + move=> A HA B0 HB0 B HB C s1 /simpl_valid_state_and[] VA VB /simpl_expand_and_fail [].
        move=> [] /HA{}HA.
        have: A <> dead A.
          by move: VA => + H; rewrite H valid_state_dead//.
        move=> /HA []//.
      move=> [].
        move=> [A'[DA[HA']]] -> //.
      move=> [s'[A'[B'[HA' [HB' ->]]]]]/= _.
      have H1 := HB _ _ VB HB'.
      case: ifP => ///eqP/[subst1].
      have: B <> dead B.
        move: VB => + H; rewrite H valid_state_dead//.
      by move=>/H1.
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
    + move=> A HA B0 _ B HB s C/simpl_valid_state_and[VA VB].
      move=> /simpl_expand_and_fail[].
        move=> [] HA' ->/=.
        by have:= HA _ _ VA HA'=>-[]-> //.
      move=> [].
        move=> [A'[DA'[HA' ->]]]/=.
        by have:= HA _ _ VA HA' => -[]->->.
      move=> [s' [A' [B' [HA' [HB' ->]]]]]/=.
      have:= HB _ _ VB HB' => -[].
      have:= expand_solved_success VA HA' => -[] ->.
      case: ifP.
        by move=>/eqP -> _ ->; rewrite orbT.
      by move=> _ /= ->->->; rewrite !orbT.
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
            suffices:  valid_state A' && (base_or_aux (cut B) || base_or_aux_ko (cut B)).
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
    + move=> A HA B0 _ B HB s1 [].
      + move=> s2 C => /simpl_expand_and_expanded [].
          move=> [A'[HA' ->]] /simpl_valid_state_and1 [VA [VB [ssaB0 bB0]]]/=.
          rewrite (HA _ _ HA' VA) bB0 (valid_state_compose_and VB bB0) ssaB0.
          move: VB; case SA: success.
            have:= succes_is_solved s1 VA SA; rewrite HA' => -[?] //.
          by move=>->; rewrite if_same.
        move=> [s[A'[B'[HA'[HB' ->]]]]].
        move=> /simpl_valid_state_and1 [VA].
        have:= expand_solved_success VA HA' => -[]/=->-> [VB [ssaB0 bB0]].
        by rewrite (HA _ _ HA' VA) (HB _ _ HB' VB)  bB0 (ssa_expand bB0 ssaB0 HB').
      + move=> s2 C /simpl_expand_and_cut [].
          move=> [A' [HA' ->]] /simpl_valid_state_and1[VA [VB [ssaB0 bB0]]]/=.
          rewrite (HA _ _ HA' VA) bB0 (valid_state_compose_and VB bB0).
          move: VB; case SA: success.
            have:= succes_is_solved s1 VA SA; rewrite HA' => -[?] //.
          by move=>->; rewrite if_same ssaB0.
        move=> [s'[A'[B'[HA'[HB' ->]]]]]/simpl_valid_state_and1[VA [VB [ssaB0 bB0]]]/=.
        move: VB.
        have:= expand_solved_success VA HA' => -[] -> sA' VB.
        rewrite (HB _ _ HB' VB) success_cut bB0 sA' (valid_state_cut (HA _ _ HA' VA)).
        by rewrite (ssa_expand bB0 ssaB0 HB').
      + move=> s2 /simpl_expand_and_fail [].
          by move=> [] /expand_failure_dead H _ /simpl_valid_state_and1 [] /H.
        move=> [].
          move=> [A'[DA'[HA' ->]]] /simpl_valid_state_and1 [VA[VB [ssaB0 bB0]]] /=.
          rewrite (HA _ _ HA' VA) bB0 ssaB0.
          move: VB.
          have:= expand_failure_failed VA HA' => -[].
          do 2 move=> /failed_success->.
          by move=>->.
        move=> [s'[A'[B'[HA'[HB' ->]]]]] /simpl_valid_state_and1 [VA [VB [ssaB0 bB0]]]/=.
        have:= HA _ _ HA' VA.
        have:= HB _ _ HB' (valid_state_compose_and VB bB0).
        move=>/=.
        case: ifP => [/eqP->|]// _ /=->->.
        have:= expand_solved_success VA HA' => -[] _ ->.
        by rewrite (ssa_expand bB0 ssaB0 HB') bB0.
      + move=> s C /simpl_expand_and_solved [s'[A'[B'[HA' [HB'<-]]]]].
        move=> /simpl_valid_state_and1 [VA [+ [ssaB0 bB0]]].
        have:= expand_solved_success VA HA' => /= -[] ->-> VB.
        rewrite (HA _ _ HA' VA) (HB _ _ HB' VB) bB0.
        by rewrite (ssa_expand bB0 ssaB0 HB').
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
    + move=> _ B0 _ B HB s1 s2 C /= /and3P[] bB0 /eqP cB0 bcB0.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      by have:= HB _ _ _ _ NB; rewrite bcB0 orbT => /(_ isT) <-.
    + move=> p a _ B0 HB0 B HB s1 s2 C /= /orP []// /andP []/eqP/[subst1] BB.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      by rewrite BB in HB; rewrite (HB _ _ _ isT NB).
  Qed.

  Lemma next_alt_aux_base_and1 {s1 s2 A B}:
     base_and A ->  next_alt_aux true s1 A = Some (s2, B) -> A = B.
  Proof.
    elim: A s1 s2 B => //; move=> [] //.
    + move=> p a _ B0 HB0 B HB s1 s2 C /= /andP []/eqP/[subst1] BB.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      by rewrite BB in HB; rewrite (HB _ _ _ isT NB).
  Qed.

  Lemma next_alt_aux_base_and2 {s1 s2 A B}:
     base_and A ->  next_alt_aux true s1 (cut A) = Some (s2, B) -> cut A = B.
  Proof.
    elim: A s1 s2 B => //; move=> [] //.
    + move=> p a _ B0 HB0 B HB s1 s2 C /= /andP []/eqP/[subst1] BB.
      case NB: next_alt_aux => // [[ ]] [] /[subst2].
      by rewrite BB in HB; rewrite (HB _ _ _ isT NB).
  Qed.

  (* Lemma xx {A B s}:
    base_and A ->ssa A B -> 
      exists s', next_alt_aux false s B = Some (s', A).
  Proof.
    elim: A B s => //.
      move=>/= []//=. *)

    Lemma xxx {B C D}: base_and B -> base_and D -> ssa B C -> ssa D C -> ssa B D.
    Proof.
      elim: B C D => //.
      + move=>[]//[]//.
      + move=> []//p a _ A HA B HB[]//.
          move=>/= + /andP[/eqP? bB] + _; subst.
          move=>[]//=[]//.
          move=> _ _ C D/andP[]/eqP? bD _; subst.
          admit.
        move=> A1 A2 A3 []//.
        move=> []// p1 a1 A5 A6 /=/andP[]/eqP? bB; subst.
        move=>/andP[]/eqP? bA6 ssaB ssaA6; subst.
        by apply: HA ssaA6.
    Admitted.


  Lemma ssa_next_alt_aux {B0 B s1 s2 D b}: 
    base_and B0 -> ssa B0 B -> valid_state B ->
      (* valid_state B -> *)
        next_alt_aux b s1 B = Some (s2, D) -> ssa B0 D.
  Proof.
    elim: B0 B s1 s2 D b => //.
      by move=> []//= s1 s2 D []// _ _ _ []??;subst.
    move=>[]//p A IGN /= B0 HB0 B HB.
    move=>[]// A' B0' B' s1 s2 D b.
    move=>/andP[/eqP? bB]; subst => ssaB/=.
    move=>/and3P[VA' VB']/andP[ssB0 bB0].
    case NB' : (next_alt_aux true s1 B') => [[s3 E]|].
      move=>[]??;subst.
      rewrite (HB _ _ _ _ _ bB ssaB (valid_state_compose_and VB' bB0) NB')//.
      (* by rewrite (HB _ _ _ _ _ bB _ ssaB NB')./ *)
    case NA' : (next_alt_aux true s1 A') => // [[s3 E]].
    move=>[]??;subst.
    move: VB'.
    case: ifP.
      move=> H1 H2.
      apply: xxx ssaB ssB0 => //.
      (* admit. *)
    move=> _.
    move=>/orP[]/eqP?;subst => //.
    apply: ssa_cut2 => //.
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
        case X: next_alt_aux => // [[s3 D]].
        move: X => /HB {}HB; destruct D => // -[]/[subst2]//.
      + move=> [] DA [] /[dup] VA /HA {}HA /[dup] VBa.
        move=> /base_or_base_or_ko_valid /[dup] VB /HB{}HB /simpl_next_alt_aux_some [|[]].
        + by move=> [B'[?[+]]] /[subst1] => /HB /= ->.
        + by move=> [A'[_ [+]]] /[subst1] /HA /= ->; rewrite VB VBa; destruct A'.
        + by move=> [_ [NA]] /[subst1] /=.
    + move=> A HA B0 HB0 B HB b s1 s2 C /simpl_valid_state_and1 [VA [VB [ssaB0 bB0]]]/=.
      case NB: next_alt_aux => [[s3 D]|].
        move=> [] /[subst2] /=; rewrite VA bB0.
        have VD:= (HB _ _ _ _ (valid_state_compose_and VB bB0) NB).
        rewrite VD.
        move: VB.
        case: ifP => SA.
          move=>VB.
          have:= (ssa_next_alt_aux bB0 ssaB0 VB NB).
          by move=>->.
          (* by have:= next_alt_aux_base_and1 bB0 NB=>->; rewrite eqxx. *)
        move=>/orP[]/eqP?;subst.
          have ?:= (next_alt_aux_base_and1 bB0 NB); subst.
          by rewrite ssaB0 eqxx.
        have ?:= (next_alt_aux_base_and2 bB0 NB); subst.
        by rewrite eqxx orbT (ssa_cut bB0).
        (* by have:= next_alt_aux_base_and2 bB0 NB=>->; rewrite eqxx orbT. *)
      case NA: next_alt_aux => // [[s3 D]] [] /[subst2] /=.
      by rewrite (HA _ _ _ _ VA NA) eqxx bB0 (base_and_valid bB0) if_same ssa_id.
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
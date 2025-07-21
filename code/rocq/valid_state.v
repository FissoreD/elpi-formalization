From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Import Run.
  
  Fixpoint base_and s :=
    match s with
    | And (Goal _ _) r r1 => (r == r1) && base_and r1 (* should also say something about the program *)
    | Top => true
    | _ => false
    end.

  Lemma base_and_dead {A}: base_and (dead A) = false.
  Proof. case: A => // -[]//=. Qed.

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

  Definition base_and_ko s :=
    match s with
    | And KO r r1 => [&&base_and r, (r == r1) & base_and r1] (* should also say something about the program *)
    | KO => true
    | _ => false
    end.

  Fixpoint base_or_aux_ko s :=
    match s with
    | Or l _ r => base_and_ko l && (base_or_aux_ko r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and_ko t
    end.

  Lemma base_and_big_and {pr A}: base_and (big_and pr A).
  Proof. by elim: A => // a l /= ->; rewrite eq_refl. Qed.

  (* same_structure_and *)
  Section ssa.
    Fixpoint ssa A B :=
      match A, B with
      | And _ _ _, Or _ _ _ => false
      | And _ _ A, And _ _ B => ssa A B
      | Top, (Top|OK|KO|Dead) => true
      | _, _ => false
      end.

    Lemma xxx {B C D}: base_and B -> base_and D -> ssa B C -> ssa D C -> ssa B D.
    Proof.
      elim: B C D => //.
      + move=>[]//[]//=[]//.
      + move=> []//p a _ A HA B HB[]//=C D E []//.
        move=> []///= _ _ F G.
        move=>/andP[]/eqP <- bA /andP[]/eqP? ssA ssF.
        apply: HA => //.
    Qed.


    Lemma ssa_id {A}: base_and A -> ssa A A.
    Proof. by elim: A =>// -[]// p a _ B0 HB0 B HB/=/andP[] _. Qed.

    Lemma ssa_cut {A}: base_and A -> ssa A (cut A).
    Proof. elim: A =>// -[]// p a _ B0 HB0 B HB/=/andP[] _; apply ssa_id. Qed.

    Lemma ssa_dead {A}: base_and A -> ssa A (dead A).
    Proof. elim: A =>//= -[]// p a _ B0 HB0 B HB/=/andP[] _//; apply ssa_id. Qed.

    Lemma ssa_cut1 {A B}: ssa A B -> ssa A (cut B).
    Proof.
      elim: A B; try by move=> // [] //.
      - move=> A HA B0 _ B HB[]//.
    Qed.

    Lemma ssa_dead1 {A B}: ssa A B -> ssa A (dead B).
    Proof.
      elim: A B; try by move=> // [] //.
      - move=> A HA B0 _ B HB[]//.
    Qed.

    Lemma ssa_cut2 {A B}: base_and B -> ssa A (cut B) -> ssa A B.
    Proof.
      elim: A B; try by move=> []//.
      (* - move=> /= _ _ []//.
      - move=> A HA s B HB []//. *)
      - move=> A HA B0 _ B HB[]//[]//.
        (* move=> p a s1 s2/=/andP[]/eqP?;subst.
        apply: HB. *)
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
        - move=> ? _ _ [] <-//.
      move=> []// p a _ A HA B0 HB0 []// A' B0' B' s.
      move=>/= r /andP[]/eqP? bB ssB0;subst.
      case: r =>//.
      + move=> s1 C /simpl_expand_and_expanded[].
          move=>[A2[HA' ->]]//.
        move=>[s' [A2 [B2 [HA' [HB' ->]]]]]//=.
        by apply: HA _ _ _ bB _ HB'.
      + move=> s1 C /simpl_expand_and_cut[].
          move=>[A2 [HA' ->]]//.
        move=> [s'[A2[B2 [HA'[HB' ->]]]]]/=.
        by apply: HA _ _ _ bB _ HB'.
      + move=> C /simpl_expand_and_fail[].
          move=> [A2 [HA' ->]]//=.
        move=>[s' [A2[B2 [HA' [HB' ->]]]]]//=.
        by rewrite (HA _ _ _ bB ssB0 HB').
      + move=> s1 C /simpl_expand_and_solved.
        move=> [s'[A1[B1[HA'[HB' ->]]]]]/=.
        by have /= := (HA _ _ _ bB ssB0 HB').
    Qed.
  End ssa.

  Lemma base_or_dead {B}: base_or_aux B || base_or_aux_ko B -> B <> dead B.
  Proof.
    move=>/orP[].
      elim: B => //.
        move=> A HA s B HB /=/andP [bA bB][dA dB].
        by move: bA; rewrite dA; rewrite base_and_dead.
      move=> []//.
    elim: B => //.
      move=> A HA s B HB /=/andP[bA bB] [dA dB].
      apply: HB; auto.
    move=>[]//.
  Qed.


  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Bot | Top => true
    | Dead => false
    | Or A _ B => 
      if A == dead A then valid_state B
      else valid_state A && (base_or_aux B || base_or_aux_ko B)
    | And A B0 B => 
      [&& valid_state A,
        if success A then valid_state B 
        else (B0 == B)
        (* ssa B0 B & *)
        & (base_and B0)]
    end.

  Lemma valid_state_dead {A} : valid_state (dead A) = false.
  Proof.
    elim: A => //.
      by move=> A HA s B HB/=; rewrite dead_dead_same eqxx.
    move=> A HA Bo ? B HB/=.
    rewrite HA//.
  Qed.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA; rewrite (HVA HA) /=.
    by rewrite HA eq_refl ?(ssa_id HA).
  Qed.


  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof.
    elim: l => // x xs /=.
    by rewrite base_and_big_and eq_refl/= ?(ssa_id base_and_big_and).
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
    + move=> A HA s B HB/=/andP[bA bB].
      case:ifP => /eqP.
        by move=>H; move: bA; rewrite H base_and_dead.
      rewrite bB // base_and_valid//.
    + move=> []// p a Ha B0 HB0 B HB /=/andP[/eqP->]bB.
      by rewrite eqxx bB ?(ssa_id bB).
  Qed.


  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof.
    elim: B => //.
    move=> []// HA B0 _ B HB/=/and3P[bB0 /eqP <-] H; rewrite bB0 eqxx ?(ssa_id bB0)//.
  Qed.


  Lemma base_or_ko_valid {B}: base_or_aux_ko B -> valid_state B.
  Proof.
    elim: B => //.
    + move=> A HA s B HB /= /andP [] /base_and_ko_valid ->.
      move=> /[dup] /HB -> ->.
      by rewrite orbT if_same.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      by rewrite eq_refl bB0 ?(ssa_id bB0).
  Qed.


  Lemma base_or_base_or_ko_valid {B}:
    base_or_aux B || base_or_aux_ko B -> valid_state B.
  Proof. by move=> /orP []; [move=> /base_or_valid | move=> /base_or_ko_valid] => ->. Qed.


  Lemma simpl_valid_state_or {s A B}: 
    valid_state (Or A s B) -> 
      (A = dead A /\ valid_state B) \/ 
      (A <> dead A /\ valid_state A /\ (base_or_aux B || base_or_aux_ko B)).
  Proof.
    move=> /=; case: A => //.
    all: try by move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; left => //.
    + move=> ?? /orP [] ->; right; repeat split => //; rewrite orbT //.
    + move=> ???; case:ifP=>/eqP//.
        by move=>/=[]->->; rewrite !dead_dead_same eqxx; left.
      move=> H/andP[]->->; auto.
    + move=> ???; case:ifP=>/eqP.
        move=>->->; rewrite dead_dead_same; auto.
      move=>? /andP[]->->; auto.
  Qed.

  Lemma simpl_valid_state_or1 {s A B}: 
    valid_state (Or A s B) -> 
      (A = dead A /\ valid_state B) \/ 
      (A <> dead A /\ valid_state A /\ valid_state B).
  Proof.
    move=> /simpl_valid_state_or[]; auto.
    move=> [?[?/base_or_base_or_ko_valid]]; auto.
  Qed.


  Lemma simpl_valid_state_and1 {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ 
      ( 
        (* if A == dead A then B == dead B else  *)
        if success A then valid_state B 
        else ((B0 == B) )) 
      /\ (*ssa B0 B /\*) base_and B0.
  Proof. by move=>/=/and3P[]//->->/andP[]->->. Qed.



  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cut B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //= _ _ _ HB HC /andP [] /eqP <- hB.
    by rewrite hB eqxx.
  Qed.

  Lemma base_or_base_or_ko_cut {B}: base_or_aux B -> base_or_aux_ko (cut B).
  Proof.
    elim: B => //.
    + by move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cut -> /IHB ->.
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP /[subst1] hC.
      by rewrite eq_refl hC ?(base_and_base_and_ko_cut hC). 
  Qed.

  Lemma base_and_ko_cut {B}: base_and_ko B -> base_and_ko (cut B).
  Proof.
    elim: B => //.
    move=> []// _ B _ C HC /= /and3P[] bB /eqP <-.
    (* by rewrite cut_cut_same eqxx bB => ->. *)
  Qed.
  
  Lemma base_or_ko_cut {B}: base_or_aux_ko B -> base_or_aux_ko (cut B).
  Proof.
    elim: B => //.
      by move=> A HA s B HB /= /andP[]/base_and_ko_cut->/HB->.
    move=> [] //= _ B0 _ B HB /and3P[] bB /eqP<-.
    (* by rewrite cut_cut_same bB eqxx => ->. *)
  Qed.

  Lemma success_cut {A} : success (cut A) = success A.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      rewrite dead_cut_is_dead.
      case:ifP=>/eqP.
        by move=> /cut_dead1//->; rewrite eqxx.
      by case: eqP => //->; rewrite dead_dead_same cut_dead_is_dead.
    + move=> A HA B HB C HC /=.
      by rewrite HA ?HC.
  Qed.

  Lemma valid_state_cut {A}: valid_state A -> valid_state (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/simpl_valid_state_or[].
        by move=>[]/=->; rewrite cut_dead_is_dead dead_dead_same eqxx.
      move=> [DA[VA bB]]/=.
      rewrite (HA VA) (HB (base_or_base_or_ko_valid bB)).
      by move: bB => /orP[/base_or_base_or_ko_cut | /base_or_ko_cut]->; rewrite !orbT if_same.
    move=> A HA B0 _ B HB /=/simpl_valid_state_and1[VA [+ bB0]].
    rewrite (HA VA) success_cut bB0 andbT/=.
    case: ifP => sA.
      (* move=>->/eqP->; rewrite !cut_dead_is_dead !dead_dead_same !eqxx ssa_dead1//. *)
    (* move=> dA; case: ifP => sA. *)
      move=>vB; rewrite vB//?ssa_cut1//.
    move=> /eqP<-; rewrite eqxx ?ssa_id//.
  Qed.

  Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else ((B02 == B2))) ->
      base_and B02  ->
        valid_state B2.
  Proof. 
    case: success => //.
    (* move=>/orP[]. *)
      move=>/eqP->; apply: base_and_valid.
    (* move=>/eqP<-/base_and_valid;apply: valid_state_cut. *)
  Qed.

  Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B.
  Proof.
    move=>/= /and3P[]// -> VB bbB0.
    by rewrite (valid_state_compose_and VB bbB0).
  Qed.

  (* Lemma expand_failure_dead s1 {A}: valid_state A -> expand s1 A <> Failure Dead.
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
    Qed. *)

  Lemma valid_state_big_or {pr s t} : valid_state (big_or pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ?; case: F => //= -[] //=???; rewrite base_or_big_or_aux.
    + by move=> ??; case F => //= -[] //=???; rewrite base_or_big_or_aux.
  Qed.   

  Lemma expand_not_dead {s A r}: 
    valid_state A -> expand s A = r -> get_state r <> dead (get_state r) .
  Proof.
    elim: A s r; try by move=> //= _ r _ <-//.
    + move=> p [|t] s r _ <- //= /esym; apply dead_big_or.
    + move=> A HA s B HB s1 => // C /simpl_valid_state_or [].
        move=> []->/= VB <-.
        rewrite dead_dead_same eqxx.
        have {}HB:= HB _ _ VB.
        case X: expand => //=; have:= HB _ _ X => /=; try congruence.
        (* by move=> H; case: ifP => /eqP H1; subst => //= -[]//. *)
      move=> [DA[VA VB]].
      case: C.
      + move=> s2 C /simpl_expand_or_expanded [].
          move=> [A'[DA'[HA' ->]]]/=[].
          by have /= := HA _ _ VA HA'.
        move=> [].
          move=> [A'[dA []]] /HA => /(_ VA)/= HA' -> /=; rewrite dead_cut_is_dead; congruence.
        move=>  [->[B' [H]]]->/=.
        rewrite dead_dead_same => -[].
        by move: H => []/HB/=/(_ (base_or_base_or_ko_valid VB))//.
      + move=> s2 C /simpl_expand_or_cut [s3[B'[?]]]; subst => //.
      + move=> C /simpl_expand_or_fail[].
          move=>[A'[dA[HA']]]/=->.
          have:= HA _ _ VA HA' => /=; congruence.
        by move=>[B'[X]]; move: VA; rewrite X valid_state_dead.
      + move=> s2 C /simpl_expand_or_solved [].
          move=> [A'[]] /HA{} => /(_ VA) /= H ->/=; congruence.
        move=> [B'[HA'[]]] /HB => /(_ (base_or_base_or_ko_valid VB)) /= + ->/=; congruence.
    + move=> A HA B0 HB0 B HB s1 r /simpl_valid_state_and[] VA VB.
      case: r.
      + move=> s2 C /simpl_expand_and_expanded [].
          by move=> [A'][] /HA => /(_ VA) /= ? ->[].
        by move=> [s'[A'[B'[]]]] /HA /= +[] _ ->//= => /(_ VA) + [].
      + move=> s2 C /simpl_expand_and_cut [].
          by move=> [A'][] /HA /= + ->// => /(_ VA) + [].
        move=> [s'[A'[B'[]]]] /HA/= + [] _->// => /(_ VA) + [].
        rewrite dead_cut_is_dead => H /cut_dead1; congruence.
      + move=> C /simpl_expand_and_fail [].
          by move=>[A'[H ->]]/=[]; have:= (HA _ _ VA H).
        move=>[s'[A'[B'[HA'[HB' ->]]]]]/=[].
        by have:= HA _ _ VA HA'.
      + move=> s2 C /simpl_expand_and_solved [s'[A'[B'[HA'[HB'->]]]]]/=[].
        by have:= HA _ _ VA HA'.
  Qed.

  (* Lemma expand_failure_dead *)

  Lemma succes_is_solved s {A}: valid_state A -> success A -> exists B, expand s A = Solved s B.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /simpl_valid_state_or[].
        move=>[-> vB]/=.
        rewrite dead_dead_same eqxx.
        move=>sB.
        by have [B' H] := HB s vB sB; rewrite H; eexists.
      move=>[dA[vA bB]]/=.
      case:ifP => /eqP// _ sA.
      by have [A' H] := HA s vA sA; rewrite H; eexists.
    + move=> A HA B0 HB0 B HB s /simpl_valid_state_and[] VA VB /=/andP[SA SB].
      have [A' H1]:= HA s VA SA; rewrite H1.
      have [B' H2]:= HB s VB SB; rewrite H2.
      by eexists.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: 
    valid_state A -> expand s1 A = Solved s2 B -> success A /\ success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ???? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB s1 s2 C /simpl_valid_state_or[].
        move=> [] -> vB/=.
        rewrite dead_dead_same eqxx.
        case X: expand => //=-[]*;subst => /=.
        rewrite dead_dead_same eqxx.
        apply: HB X => //.
      move=> [dA[VA bB]] /simpl_expand_or_solved[].
        move=>[A'[HA' ->]]/=.
        have:= expand_not_dead VA HA' => /=.
        do 2 case: ifP => /eqP //; try congruence.
        move=> ???; apply: HA VA HA'.
      move=> [B'[]]//.
    + move=> A HA ? _ B HB s1 s2 C /simpl_valid_state_and[VA VB].
      move=> /simpl_expand_and_solved [s3 [A' [B'[HA' [HB' ->]]]]]/=.
      have:= HA _ _ _ VA HA' => -[] ->->.
      by have:= HB _ _ _ VB HB' => -[] ->->.
  Qed.

  Lemma expand_solved_failed {s1 A s2 B}: 
    valid_state A -> expand s1 A = Solved s2 B -> failed A = false /\ failed B = false.
  Proof.
    move=>/expand_solved_success H /H[].
    by do 2 move=> /success_failed->.
  Qed.

  Lemma expand_failure_failed {s1 A B}:
    valid_state A -> expand s1 A = Failure B -> failed A /\ failed B.
  Proof.
    elim: A s1 B; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2 C /simpl_valid_state_or[].
        move=> [] ->/=; rewrite dead_dead_same eqxx.
        case X: expand => //= /HB{}HB [] <-; move: X=>/HB[]->/=.
        by rewrite dead_dead_same eqxx.
      move=> [DA] [] /[dup] VA /HA{}HA/[dup]BB/base_or_base_or_ko_valid/HB{}HB/simpl_expand_or_fail [].
        move=> [A' [+[HD]]] /[subst1] /= dA.
        have /= dA' :=expand_not_dead VA HD.
        do 2 case: ifP => /eqP//; try congruence.
        move=> _ _.
        apply: HA HD.
      move=> [B'[dA[HB'->]]]; rewrite dA /=.
      rewrite dead_dead_same eqxx.
      by apply: HB HB'.
    + move=> A HA B0 _ B HB s C/simpl_valid_state_and[VA VB].
      move=> /simpl_expand_and_fail[].
        move=> [A' [HA'->]]/=.
        by have:= HA _ _ VA HA'=>-[]-> //->.
      move=> [s' [A' [B' [HA' [HB' ->]]]]]/=.
      have:= HB _ _ VB HB' => -[]->->.
      have:= expand_solved_success VA HA' => -[] ->->.
      by rewrite !orbT.
  Qed. 


  Lemma valid_state_expand {s A r}:
    valid_state A -> expand s A = r -> valid_state (get_state r).
  Proof.
    elim: A s r => //; try by move=> s r // *; subst.
    + by move=> ? [|?] ?? *;subst => //=; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 r /simpl_valid_state_or[].  
        move=> []->VB/=; rewrite dead_dead_same eqxx.
        case X: expand => *; subst => /= ; rewrite dead_dead_same eqxx;
        by have:= IHB _ _ VB X.
      move=> [dA [VA bB]].
      case: r.
      + move=> s2 C /simpl_expand_or_expanded [].
          move=> [A'[_[HA' ->]]]/=.
          rewrite (IHA _ _ VA HA') bB.
          have /= dA':= expand_not_dead VA HA'.
          case: ifP => // _.
          by apply: base_or_base_or_ko_valid.
        move=> [].
          move=>[A'[_[HA' ->]]]/=.
          have/=->:= IHA _ _ VA HA'.
          rewrite (valid_state_cut (base_or_base_or_ko_valid bB)).
          by move: bB => /orP[/base_or_base_or_ko_cut|/base_or_ko_cut]->; rewrite orbT if_same.
        move=>[]//.
      + move=> s2 C /simpl_expand_or_cut. 
        move=> [s3[B'[dA'[HB]]]]//.
      + move=> C /simpl_expand_or_fail [].
          move=>[A'[_[HA'->]]]/=.
          have /= dA':= expand_not_dead VA HA'.
          by case: ifP => /eqP// _; rewrite bB (IHA _ _ VA HA').
        move=>[B'[?]]//.
      + move=> s2 C /simpl_expand_or_solved [].
          move=> [A'[HA' ->]]/=.
          have /= dA':= expand_not_dead VA HA'.
          by case: ifP => /eqP//; rewrite bB (IHA _ _ VA HA').
        move=> [B'[?]]//.
    + move=> A HA B0 _ B HB s1 r /simpl_valid_state_and1[VA[VB bB0]].
      case: r.
      + move=> s2 C => /simpl_expand_and_expanded [].
          move=> [A'[HA' ->]]/=.
          rewrite (HA _ _ VA HA') bB0 (valid_state_compose_and VB bB0) ?ssB0.
          move: VB.
          case: ifP => //sA.
          have:= succes_is_solved s1 VA sA; rewrite HA' => -[?] //.
          by move=>->; rewrite if_same.
        move=> [s[A'[B'[HA'[HB' ->]]]]]/=.
        have:= expand_solved_success VA HA' => -[] _ ->.
        rewrite (HA _ _ VA HA') (HB _ _ (valid_state_compose_and VB bB0) HB') bB0.
        by rewrite ?(ssa_expand bB0 ssB0 HB').
      + move=> s2 C /simpl_expand_and_cut [].
          move=> [A' [HA' ->]]/=.
          rewrite (HA _ _ VA HA') bB0 (valid_state_compose_and VB bB0).
          move: VB; case SA: success.
            have:= succes_is_solved s1 VA SA; rewrite HA' => -[?] //.
          by move=>->; rewrite if_same ?ssB0.
        move=> [s'[A'[B'[HA'[HB' ->]]]]]/=.
        move: VB.
        have:= expand_solved_success VA HA' => -[] -> sA' VB.
        rewrite (HB _ _ VB HB') success_cut bB0 sA' (valid_state_cut (HA _ _ VA HA')).
        by rewrite ?(ssa_expand bB0 ssB0 HB').
      + move=> s2 /simpl_expand_and_fail [].
          move=>[A'[HA'->]]/=.
          rewrite (HA _ _ VA HA') bB0 ?ssB0.
          have []:= expand_failure_failed VA HA'.
          move: VB; case: ifP => //sA ->.
            by move=> /failed_success; rewrite sA.
          case: ifP => //.
          by move=>/success_failed ->.
        move=> [s'[A'[B'[HA'[HB' ->]]]]]/=.
        have:= HA _ _ VA HA'.
        have:= HB _ _ (valid_state_compose_and VB bB0) HB' => /=.
        move=>->->.
        have:= expand_solved_success VA HA' => -[] _ ->.
        by rewrite ?(ssa_expand bB0 ssB0 HB') bB0.
      + move=> s C /simpl_expand_and_solved [s'[A'[B'[HA' [HB'->]]]]]/=.
        move: VB.
        have:= expand_solved_success VA HA' => -[]->-> VB.
        rewrite (HA _ _ VA HA') (HB _ _ VB HB') bB0.
        by rewrite ?(ssa_expand bB0 ssB0 HB').
  Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      by rewrite valid_state_big_and base_or_big_or_aux IH /= if_same.
  Qed.

  Lemma toT {P}: P = true -> is_true P.
  Proof. case: P => //. Qed.

  Definition get_state_run r := match r with Done _ s => s | Failed s => s end.

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> valid_state (get_state_run r).
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A1 A2 EA VA /=.
      apply: valid_state_expand VA EA.
    + move=> s A B HA HB /=.
      apply: valid_state_expand HB HA.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand VA HA.
      apply: IH VB.
    + move=> s s' r A B b HA HB IH VA.
      have VB:= valid_state_expand VA HA.
      apply: (IH VB).
  Qed.

  Lemma valid_state_expanded {s1 A r}:
    valid_state A ->  expanded s1 A r -> valid_state (get_state_run r).
  Proof.
    move=> + [b H].
    elim: H; clear.
    + move=> s1 s2 A B HA VA /=; apply: valid_state_expand VA HA.
    + move=> s A B HA VA; apply: valid_state_expand VA HA.
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
  Qed.

  (* Lemma next_alt_aux_base_and {s1 s2 A B}:
     base_and A || base_and_ko A ->  next_alt s1 A = Some (s2, B) -> A = B.
  Proof.
    elim: A s1 s2 B => //; move=> [] //.
    + move=> _ B0 _ B HB s1 s2 C /= /and3P[] bB0 /eqP cB0 bcB0.
      case NB: next_alt => // [[ ]] [] /[subst2].
      by have:= HB _ _ _ _ NB; rewrite bcB0 orbT => /(_ isT) <-.
    + move=> p a _ B0 HB0 B HB s1 s2 C /= /orP []// /andP []/eqP/[subst1] BB.
      case NB: next_alt => // [[ ]] [] /[subst2].
      by rewrite BB in HB; rewrite (HB _ _ _ isT NB).
  Qed. *)

  Lemma next_alt_aux_base_and1 {A s}: base_and A -> next_alt s A = None.
  Proof.
    elim: A s => //-[]//p a _ B0 _ B HB/= c.
    move=>/andP[]/eqP? bB;subst.
    by rewrite HB.
  Qed.

  Lemma next_alt_aux_base_and2 {A s}: base_and A -> next_alt s (cut A) = None.
  Proof.
    elim: A s => //-[]//p a _ B0 _ B HB/= c.
    (* move=>/andP[]/eqP? bB;subst.
    rewrite next_alt_aux_base_and1//. *)
  Qed.

  (* Lemma ssa_next_alt_aux {B0 B s1 s2 D}: 
    base_and B0 -> ssa B0 B -> valid_state B ->
      (* valid_state B -> *)
        next_alt s1 B = Some (s2, D) -> ssa B0 D.
  Proof.
    elim: B0 B s1 s2 D => //.
      by move=> []//= s1 s2 D []// _ _ _ []??;subst.
    move=>[]//p A IGN /= B0 HB0 B HB.
    move=>[]// A' B0' B' s1 s2 D.
    move=>/andP[/eqP? bB]; subst => ssaB/=.
    move=>/and3P[VA' VB'] bB0.
    case NB' : (next_alt s1 B') => [[s3 E]|].
      case:ifP => //.
      move=>[]??;subst.
      rewrite (HB _ _ _ _ _ ssaB (valid_state_compose_and VB' bB0) NB')//.
      (* by rewrite (HB _ _ _ _ _ bB _ ssaB NB')./ *)
    case NA' : (next_alt s1 A') => // [[s3 E]].
    move=>[]??;subst.
    move: VB'.
    case: ifP.
      move=> H1 H2.
      apply: xxx ssaB ssB0 => //.
      (* admit. *)
    move=> _.
    move=>/eqP?;subst => //.
    (* apply: ssa_cut2 => //. *)
  Qed. *)

  Lemma valid_state_next_alt {s1 s2 A B}: 
    valid_state A -> next_alt s1 A = Some (s2, B) 
    -> valid_state B.
  Proof.
    elim: A s1 s2 B => //.
    (* + by move=> [] // ??? _ [] /[subst2].
    + by move=> [] // ??? _ [] /[subst2].
    + by move=> ?? [] // ??? _ [] /[subst2]. *)
    + move=> A HA s B HB s1 s2 C /simpl_valid_state_or [].
        move=> [-> VB]/=; rewrite dead_dead_same eqxx.
        case X: next_alt => // [[s3 D]].
        move=>[]??;subst => /=.
        rewrite dead_dead_same eqxx; apply: HB VB X.
      move=> [dA [VA bB]]/=.
      case: ifP=>/eqP.
        move=>->.
        case X: next_alt => //[[s3 D]].
        move=> []*;subst=>/=.
        rewrite dead_dead_same eqxx.
        apply: HB (base_or_base_or_ko_valid bB) X.
      move=> _; case: ifP => /eqP// dB.
      have VB:= base_or_base_or_ko_valid bB.
      case X: next_alt => //[[s3 D]|].
        move =>-[]*;subst=>/=.
        by rewrite bB VB (HA _ _ _ VA X) if_same.
      case:ifP => //.
        case Y: next_alt => //[[s3 D]] fB []??;subst=> /=.
        rewrite dead_dead_same eqxx.
        by apply: HB Y.
      move=> _ []??;subst => /=.
      by rewrite dead_dead_same eqxx VB.
    + move=> A HA B0 HB0 B HB s1 s2 C /simpl_valid_state_and1 [VA [VB bB0]]/=.
      have VB' := valid_state_compose_and VB bB0.
      case: ifP => ///eqP dA.
      case: ifP => // fA.
        case NA: next_alt => [[s3 D]|]//.
        case: ifP => //fB0 []??;subst => /=.
        rewrite bB0 eqxx (base_and_valid bB0) if_same !andbT.
        apply: HA VA NA.
      have N := @next_alt_aux_base_and1 B0 s1 bB0.
      case NB: next_alt => // [[s3 D]|].
        move=>[]??;subst => /=.
        rewrite VA bB0 andbT/=.
        move: VB.
        case: ifP => // sA.
          move=> vB.
          apply: HB VB' NB.
        move=>/eqP?;subst.
        congruence.
      case NA: next_alt => //[[s3 D]].
      case: ifP => // _ []??;subst => /=.
      by rewrite (HA _ _ _ VA NA) eqxx bB0 (base_and_valid bB0) if_same.
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
      have NA := valid_state_next_alt VB HB.
      apply: IH NA.
    Qed.

  Lemma base_and_ko_succes {B}: base_and_ko B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.

  Lemma base_and_succes {B}: base_and B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.

  Lemma base_or_succes {B}: base_or_aux B || base_or_aux_ko B -> success B = false.
  Proof.
    move=>/orP[].
      elim: B => //.
        move=> A HA s B HB/=/andP[].
        case: ifP=>/eqP.
          by move=>->; rewrite base_and_dead.
        by move=> dA /base_and_succes.
      move=> []//.
    elim: B=> //=.
      move=> A HA _ B HB/andP[].
      case: ifP=>/eqP//.
      by move=> _ /base_and_ko_succes.
    move=> []//.
  Qed.

  Lemma next_alt_aux_success {A B s1 s2}: valid_state A -> next_alt s1 A = Some (s2, B) -> success B = false.
  Proof.
    elim: A B s1 s2 => //.
      move=> A HA s B HB B0 s1 s2/simpl_valid_state_or[].
        move=>[-> VB]/=; rewrite dead_dead_same eqxx.
        have:= HB _ s1 _ VB.
        case X: next_alt => //[[s3 C]] => /(_ _ _ erefl).
        move=> _ []??;subst => /=.
        rewrite dead_dead_same eqxx.
        apply: HB VB X.
      move=> [dA [VA VB]]/=; case: ifP => /eqP// _.
      case: ifP => ///eqP dB.
      have:= HA _ s1 _ VA.
      case: next_alt => [[s3 C]|].
        move=>/(_ _ _ erefl) + []??; subst => /=.
        case: ifP => ///eqP.
        by rewrite (base_or_succes VB).
      have VB':= base_or_base_or_ko_valid VB.
      case:ifP => // fB _.
        case X: next_alt => //[[s3 C]].
        move=> []??;subst => /=.
        rewrite dead_dead_same eqxx.
        by apply: HB X.
      move=> []??;subst => /=.
      rewrite dead_dead_same eqxx.
      by apply: base_or_succes.
    move=> A HA B0 _ B HB B1 s1 s2 /simpl_valid_state_and1[VA [VB bB0]].
    move=>/=.
    case:ifP => ///eqP dA.
    case: ifP => //fA.
      case: next_alt => //[[s3 C]].
      case: ifP => //fB0.
      move=> []??;subst => /=.
      by rewrite (base_and_succes bB0) andbF.
    have:= HB _ s1 _ (valid_state_compose_and VB bB0).
    case: next_alt => [[s3 C]|].
      by move=>/(_ _ _ erefl) + []??;subst => /= ->; rewrite andbF.
    move=> _.
    have:= HA _ s1 _ VA.
    case: next_alt => [[s3 C]|]// /(_ _ _ erefl).
    case:ifP => //.
    move=> _ + []??; subst.
    by move=>/=->.
  Qed.


End valid_state.
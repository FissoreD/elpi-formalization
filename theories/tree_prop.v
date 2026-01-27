From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang tree.
From det Require Import zify_ssreflect.

Section RunP.
  (* Variable u: Unif.
  Variable p : program.
  Notation step := (step u p).
  Notation run := (run u p). *)

  (********************************************************************)
  (* EXPAND PROPERTIES                                                *)
  (********************************************************************)

  Lemma is_ko_step u p fv A s1: is_ko A -> step u p fv  s1 A = (fv, Failed, A).
  Proof.
    elim: A s1 => //.
    - move=> A HA s B HB s1 /=.
      case: ifP=> //dA/andP[kA kB].
        rewrite HB//.
      rewrite HA//.
    - move=> A HA B0 B HB s1 /= kA.
      rewrite HA//.
  Qed.

  Lemma failed_big_and t: failed (big_and t) = false.
  Proof. case: t => [|[]]//. Qed.

  Lemma is_dead_big_and r: is_dead (big_and r) = false.
  Proof. apply/contraFF/failed_big_and/r/is_dead_failed. Qed.

  Lemma is_ko_big_and r: is_ko (big_and r) = false.
  Proof. apply/contraFF/failed_big_and/r/is_ko_failed. Qed.

  Lemma is_dead_big_or r rs: is_dead (big_or r rs) = false.
  Proof. 
    elim: rs r => //=.
    - move=> *; apply: is_dead_big_and.
    - move=> [s r] l/= H rs; rewrite H andbF//.
  Qed. 

  Lemma is_dead_step u p fv s A: 
    is_dead A -> step u p fv  s A = (fv, Failed, A).
  Proof. move=>/is_dead_is_ko/is_ko_step//. Qed.

  (*SNIP: success_step*)
  Lemma success_step u p fv s A: success A -> step u p fv s A = (fv, Success, A).
  (*ENDSNIP: success_step*)
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
      case:ifP => //= H sA.
        rewrite HB//=.
      rewrite HA//.
    + move=> A HA B0 B HB s /=/andP[sA sB].
      rewrite HA//HB//.
  Qed.

  Ltac case_step_tag X A := let fv := fresh "_fv" in case X : step => [[fv []] A].
  Tactic Notation "case_step_tag" ident(X) ident(A) := case_step_tag X A.

  Lemma step_success u p fv fv' {s1 A B}: 
    step u p fv s1 A = (fv', Success, B) -> ((fv = fv') * (B = A) * (success A))%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + by move=> /= ???? [? <-].
    + by move=> []//= ?????; case: backchain.
    + move=> A HA s B HB ?? s1 C/=.
      case: ifP => dA/=.
        by case_step_tag X B1 => -[??] //; subst; rewrite !(HB _ _ _ _ X).
      by case_step_tag X A1 => -[??] //; subst; rewrite !(HA _ _ _ _ X).
    + move=> A HA B0 B HB s1 ?? C /=.
      case_step_tag X A1 => //=; case_step_tag Y B1 => //= -[??]; subst.
      by rewrite !(HA _ _ _ _ X) !(HB _ _ _ _ Y).
  Qed.

  Ltac push := rewrite !push.

  Lemma step_not_dead u p fv s A r: 
    is_dead A = false -> step u p fv  s A = r -> is_dead r.2 = false.
  Proof.
    move=> + <-.
    elim: A s; clear; try by move=> //=.
    - by move=> [] // t s/= _; push; apply: dead_big_or.
    + move=> A HA s B HB s1 => //=; push.
      by case: ifP => dA/= H; rewrite ?dA (HA, HB).
    + move=> A HA B0 B HB s1 //= dA; push.
      have:= HA s1 dA.
      case X: step => [[]A']//= dA'.
      rewrite 2!fun_if /= dA'; case: ifP => // _.
      by rewrite fun_if is_dead_cutl; case: ifP.
  Qed.

  Lemma step_failed u p fv fv' s1 A B:
    step u p fv s1 A = (fv', Failed, B) -> ((fv = fv') * (B = A) * failed A)%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + move=> ?? s1 B[<-]//.
    + move=> ?? s1 B[<-]//.
    + by move=> []//= ?????; push.
    + move=> A HA s B HB ?? s1 C/=; push.
      by case: ifP => dA /= [e + <-]{C}/=; do [case_step_tag S B1] in e *; subst => //; [rewrite !(HB _ _ _ _ S)|rewrite !(HA _ _ _ _ S)].
    + move=> A HA B0 B HB ?? s1 C /=.
      case_step_tag X A1 => //=.
        by move=> -[??]; subst; rewrite !(HA _ _ _ _ X).
      case_step_tag Y B1 => //= -[??]; subst.
      rewrite !(step_success X) in Y *.
      by rewrite !(HB _ _ _ _ Y) orbT.
  Qed.

  (* Lemma expanded_Done_success {s1 A s2 B b1}: 
    expandedb s1 A (Done s2 B) b1 -> success B.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    move=> s s' A B /step_success H ??; rewrite !H => -[_<-]; rewrite H//.
  Qed. *)

  Lemma is_ko_next_alt {A} b: is_ko A -> next_alt b A = None.
  Proof.
    elim: A b => //.
      move=> A HA s1 B HB b /= /andP[kA kB].
      rewrite HA//!HB// !if_same//.
    move=> A HA l B HB /= b kA.
    by rewrite is_ko_success//HA//is_ko_failed.
  Qed.

  Lemma next_alt_None_failed {A}: 
    next_alt false A = None -> failed A.
  Proof.
    elim: A => //=.
    - move=> A + s1 B +/=.
      by case: ifP => //=dA; do 2 case: next_alt => //.
    - move=> A + l B +.
      case sA: success.
        rewrite (success_failed sA)/=.
        by case: (next_alt _ B) => //=; auto.
      by case: ifP.
  Qed.

  Lemma next_alt_cutr {A b}:
    next_alt b (cutr A) = None.
  Proof. apply: is_ko_next_alt is_ko_cutr. Qed.

  Lemma is_dead_next_alt {A} b: is_dead A -> next_alt b A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed.

  Lemma next_alt_cutl_success {A}:
    success A -> next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB.
      case: ifP => [dA sB|dA sA]/=.
        rewrite dA HB// is_dead_next_alt//.
      rewrite is_dead_cutl dA HA// next_alt_cutr//.
    - move=> A HA l B HB /andP[sA sB].
      rewrite sA/= success_cut sA HA// HB//.
  Qed.

  Lemma next_alt_cutl_failed {A b}:
    failed (cutl A) -> next_alt b (cutl A) = None.
  Proof.
    elim: A b => //=.
    - move=> A HA s B HB b.
      case: ifP => dA /=; rewrite?is_dead_cutl dA => Hf.
        rewrite HB// is_dead_next_alt//.
      rewrite HA// next_alt_cutr//.
    - move=> A HA l B HB b.
      case: ifP => sA/=.
        rewrite failed_success_cut success_cut sA/=.
        move=> fB.
        rewrite HB//=next_alt_cutl_success//.
      rewrite !next_alt_cutr success_cutr failed_cutr//.
  Qed.

  Lemma next_alt_cutl_failedF {A b}:
    failed A -> next_alt b (cutl A) = None.
  Proof. move=> /failed_cut /next_alt_cutl_failed//. Qed.

  Lemma next_alt_cutl {A}:
    next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => /= dA.
        rewrite dA HB//is_dead_next_alt//.
      rewrite is_dead_cutl dA HA next_alt_cutr//.
    - move=> A HA l B HB; case: ifP => //sA/=.
        by rewrite success_cut sA HB HA //.
      by rewrite success_cutr next_alt_cutr//failed_cutr.
  Qed.

  Lemma step_not_solved u p fv  s1 A r:
    step u p fv s1 A = r -> ~ (is_sc r.1.2) -> success A = false.
  Proof. by case: r => -[?[]]//=b; case X: success; rewrite // (success_step _ _ _ s1 X). Qed.

  (*SNIP: failed_step*)
  Lemma failed_step u p fv s1 A: failed A -> step u p fv  s1 A = (fv, Failed, A).
  (*ENDSNIP: failed_step*)
  Proof.
    elim: A s1; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2/=.
      case: ifP => [dA fB|dA fA].
        rewrite HB//.
      rewrite HA//.
    + move=> A HA B0 B HB s/=.
      case X: failed => /=.
        move=>_; rewrite HA => //.
      move=>/andP[sA fB].
      rewrite success_step//.
      rewrite HB//.
  Qed. 

  Lemma step_not_failed u p fv s1 A r:
    step u p fv s1 A = r -> ~ (is_fl r.1.2) -> failed A = false.
  Proof.
    move=><-; clear r.
    elim: A s1; try by move=> // s1 <-//=.
    - move=> A HA s B HB s1/=.
      case: ifP => dA; push.
        by have:= HB s; case_step_tag X B1.
      by have:= HA s1; case_step_tag X A1.
    - move=> A HA B0 B HB s1/=.
      have:= HA s1.
      case_step_tag X A1 => //=; only 1,2: by move=> H/H->; rewrite (step_not_solved X).
      move=> /(_ notF)->//=.
      have [[<- <-] ->]:= (step_success X); subst.
      by rewrite 2!push /= => /HB.
  Qed.

  Lemma is_ko_big_or r A: is_ko (big_or r A) = false.
  Proof. by elim: A r => //=[|[s r] rs IH] r1/=; rewrite is_ko_big_and//. Qed.

  Lemma step_is_ko u p fv s1 A r:
    step u p fv s1 A = r -> ~ (is_fl r.1.2) -> is_ko A = false.
  Proof. by move=>*; apply/failed_is_ko/step_not_failed; eassumption. Qed.

  (********************************************************************)
  (* NEXT_ALT OP PROPERTIES                                           *)
  (********************************************************************)

  Lemma next_alt_dead {A D b}: 
    next_alt b A = Some (D) -> ((is_dead A = false) * (is_dead D = false))%type.
  Proof.
    elim: A D b => //=.
    - move=> D []//[<-]//.
    - move=>/= c d _ []// <-//.
    - move=> A HA s B HB C b/=.
      case: ifP => dA.
        case X: next_alt => //[D][<-]/=; rewrite dA/=.
        by rewrite !(HB _ _ X)//.
      case X: next_alt => //= [D|].
        by move=>[<-]; split => //=; rewrite ((HA _ _ X))//.
      case Y: next_alt => //[D] [<-]/=.
      by rewrite is_dead_dead ((HB _ _ Y))//.
    move=> A HA l B HB C b /=.
    case sA: success.
      case X: next_alt => //[B'|].
        by move=> [<-]/=;rewrite success_is_dead//.
      case Y: next_alt => //[A'][<-]/=.
      rewrite !(HA _ _ Y)//.
    case: ifP => //= fA.
      case X: next_alt => //[A'][<-]/=.
      rewrite !(HA _ _ X)//.
    by move=> [<-]/=; rewrite (contraFF is_dead_failed)//.
  Qed.

  Lemma next_alt_failed {b A r}: next_alt b A = r -> failed (odflt OK r) = false.
  Proof.
    move=><-; elim: A b {r} => //=.
    - move=> []//.
    - move=> A HA s B HB b.
      case: ifP => //=dA.
        by have:= HB b; case: next_alt => //=?; rewrite dA.
      have:= HA b; case X: next_alt => //=[A'|].
        rewrite (next_alt_dead X)//.
      by have {HB} := HB false; case: next_alt; rewrite//=is_dead_dead//.
    - move=> A HA l B HB b.
      case sA: success.
        have:= HB b; case: next_alt => //=.
          by move=> ? ->; rewrite sA success_failed.
        by have:= HA true; case: next_alt => //=A' ->; rewrite failed_big_and andbF.
      case: ifP => /=fA; last by rewrite sA fA.
      by have:= HA false; case: next_alt => //= ? ->; rewrite failed_big_and andbF.
  Qed.

  Lemma next_alt_is_ko {b A r}: next_alt b A = r -> (is_ko (odflt OK r) = false)%type2.
  Proof.
    move=>/next_alt_failed.
    by move=> /failed_is_ko.
  Qed.

  Lemma failed_big_or u p fv s t: failed (backchain u p fv s t).2.
  Proof. rewrite/backchain; case: bc => // ? -[|[]]//. Qed.

  Section same_structure.

    Fixpoint same_structure A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => [&& B0 == B0', same_structure A1 A' & same_structure B1 B']
        | _ => false
        end
      | Or A1 s B1 =>
        match B with 
        | Or A' s' B' => [&& s == s', same_structure A1 A' & same_structure B1 B']
        | _ => false
        end
      | _ => true
      end.

    Lemma same_structure_id {A}: same_structure A A.
    Proof. 
      elim: A => //=.
        by move=>?->??->; rewrite eqxx.
      by move=> ?->??->; rewrite eqxx.
    Qed.

    Lemma same_structure_trans: transitive same_structure.
    Proof.
      move=> + A; elim: A => //.
      - move=> A HA s B HB []//A' s' B'[]//A2 s2 B2/=.
        move=>/and3P[/eqP<-HA' HB']/and3P[/eqP<-HA2 HB2].
        rewrite eqxx (HA A' A2)//(HB B' B2)//.
      - move=> A HA B0 B HB[]//A1 B01 B1[]//A2 B02 B2/=.
        move=>/and3P[HA1 HB01 HB1]/and3P[HA2 HB02 HB2].
        by rewrite (HA A1 A2)//(HB B1 B2)// (eqP HA1) HA2.
    Qed.

    Lemma same_structure_cutr {A B}: same_structure A B -> same_structure A (cutr B).
    Proof. 
      elim: A B => //=.
        by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
      move=> A HA B0 B HB []//A' B0' B'/=/and3P[->/HA->]//.
    Qed.
    
    Lemma same_structure_cut {A B}: same_structure A B -> same_structure A (cutl B).
    Proof. 
      elim: A B => //=.
        move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<- H2 H3].
        case: ifP => //.
          by rewrite H2 HB//eqxx.
        by rewrite eqxx HA// same_structure_cutr//.
      move=> A HA B0 B HB []//A' B0' B'/=. 
      move=> /and3P[sB0 sA sB].
      by case: ifP => //=sA'; rewrite sB0 !(HA, same_structure_cutr, HB)//.
    Qed.
    
    Lemma same_structure_dead {B}: same_structure B (dead B).
    Proof. 
      elim: B => //=.
        move=> A HA s B HB; rewrite eqxx HA HB//.
      by move=> A HA B0 B HB; rewrite HA eqxx same_structure_id.
    Qed.

    Lemma step_same_structure u p fv s A r: 
      step u p fv s A = r -> same_structure A r.2.
    Proof.
      move=><-{r}.
      elim: A s fv => //.
        move=> A HA s B HB s1 fv; subst => /=.
        case: ifP => dA.
          move: (HB s fv).
          by case_step_tag eB B' => //=; rewrite eqxx same_structure_id.
        move: (HA s1 fv).
        by case_step_tag eA A' => //=;rewrite eqxx ?same_structure_cutr//?same_structure_id// => ->.
      move=> A HA B0 B HB s1 fv; subst => /=.
      have:= (HA s1) fv.
      case_step_tag eA A' => //= {}HA; only 1-3: by rewrite HA !same_structure_id eqxx.
      have := (HB (get_substS s1 A') _fv).
      by case_step_tag eB B' => //= H; rewrite ?same_structure_cut// ?same_structure_cutr// ?same_structure_id// ?HA// eqxx// ?eA.
    Qed.

    Definition same_structure_sup A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => true
        | _ => false
        end
      | Or A1 s B1 =>
        match B with 
        | Or A' s' B' => s == s'
        | _ => false
        end
      | _ => true
      end.

    Lemma same_structure_sup_refl A : same_structure_sup A A.
    Proof. case: A => //=. Qed.

    Lemma next_alt_same_structure {b A B}:
      next_alt b A = Some B -> same_structure_sup A B.
    Proof.
      case: A => //=.
      - move=> ???; case: ifP => dA.
          case: next_alt => //[?][<-]//.
        case next_alt => //[?[<-]|]//.
        case: next_alt => //?[<-]//.
      - move=> ???; case sA: success => //.
          case: next_alt => //.
            move=> ?[<-]//.
          by case nA: next_alt => //=-[<-].
        by case nA: next_alt => //=; case: ifP => //= _ [<-].
    Qed.

    Lemma same_structure_sup2_trans {A B C}:
      same_structure A B -> same_structure_sup B C -> same_structure_sup A C.
    Proof. by destruct A, B => //; destruct C => //=; do 2 case: eqP => ?//; subst. Qed.

    Lemma same_structure_sup_trans:
      transitive same_structure_sup.
    Proof. move=> B A C; by destruct A, B => //; destruct C => //=; do 2 case: eqP => ?//; subst. Qed.

    Lemma same_structure_sup_dead {A}:
      same_structure_sup A (dead A).
    Proof. case: A => //=. Qed.

    Lemma run_same_structure u p fv s A s1 r n:
      run u p fv s A s1 r n -> same_structure_sup A r.
    Proof.
      elim; clear => //.
      - move=> s1 s2 A B ? sA _ <-/=.
        case X: next_alt => [B'|]/=; subst; move: X.
          move=> /next_alt_same_structure//.
        move=> _.
        apply: same_structure_sup_dead.
      - move=> s1 s2 r A B n ?? /step_same_structure/= + _.
        apply: same_structure_sup2_trans.
      - move=> s1 s2 r A B n ?? /step_same_structure/= + _.
        apply: same_structure_sup2_trans.
      - move=> s1 s2 A B oB r n ?.
          move=> /next_alt_same_structure + _.
          apply: same_structure_sup_trans.
      - move=> *; apply: same_structure_sup_dead.
    Qed.

    Lemma run_dead1 u p fv s1 B s2 r n:  
      is_dead B -> run u p fv s1 B s2 r n -> (s2 = None /\ r = dead B /\ n = false)%type2.
    Proof.
      move=> dB H; inversion H; clear H; subst;
        try rewrite // is_dead_step//is_dead_dead in H0.
        by rewrite success_is_dead in dB.
      rewrite is_dead_next_alt// in H1.
    Qed.

    Lemma run_dead2 u p fv  s1 B s2 r n:  
      run u p fv s1 (dead B) s2 r n -> (s2 = None /\ r = dead B /\ n = false)%type2.
    Proof. move=> /(run_dead1 is_dead_dead)//; rewrite dead2//. Qed.

  End same_structure.

  Lemma ges_subst_cutl {s A} : 
    success A -> get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//; auto.
    - move=> A HA B0 B HB s /andP[sA sB]; rewrite sA/=success_cut sA HA// HB//.
  Qed.

  Lemma next_alt_not_failed {A}:
    (failed A) = false -> next_alt false A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA fB; by rewrite (HA,HB).
    - move=> A HA l B HB.
      case fA: failed => //.
      case sA: success => //= fB; rewrite (HA, HB)//=.
  Qed.

  Lemma next_alt_not_success {A b}:
    failed A = false ->
      (success A) = false -> next_alt b A = Some A.
  Proof.
    elim: A => //=.
    - by move=> A HA s B HB; case: ifP => dA fB sB; rewrite (HA, HB).
    - move=> A HA l B HB.
      case fA: failed => //=.
      case sA: success => //= fB sV.
      rewrite HB//.
  Qed.

  Lemma next_alt_alt_None_sf {b A}:
    next_alt b A = None -> success A \/ failed A.
  Proof.
    case s: success; auto.
    case f: failed; auto.
    rewrite next_alt_not_success//.
  Qed.

  Lemma next_alt_false_true {A b}:
    success A = false ->
      next_alt b A = next_alt false A.
  Proof.
    elim: A b => //=.
    - move=> A HA s B HB b.
      by case: ifP => [dA sB|dA sA]; rewrite (HA,HB)//.
    - move=> A HA l B HB b.
      by case sA: success => //=sB; rewrite HB//.
  Qed.

  Lemma next_alt_big_and r:
    next_alt false (big_and r) = Some (big_and r).
  Proof. elim: r => //=x xs IH p; case: x => //=. Qed.

  Lemma next_alt_big_or r rs:
    next_alt false (big_or r rs) = Some (big_or r rs).
  Proof.
    elim: rs r => //= [|[sr r] rs IH] r0/=;
    by rewrite ?is_dead_big_and next_alt_big_and//.
  Qed.

  Lemma get_substS_big_and A s1:
    get_substS s1 (big_and A) = s1.
  Proof. elim: A => //. Qed.

  Lemma is_ko_run u p fv s A: is_ko A -> run u p fv s A None (dead A) false.
  Proof.
    elim: A s => //=.
    - by move=> s _; apply: run_dead => //=.
    - move=> s _; apply: run_dead => //=.
    - move=> A HA s B HB s2 /andP[kA kB].
      have {}HA := HA s2 kA.
      have {}HB := HB s2 kB.
      apply: run_dead; rewrite/=.
        by rewrite !is_ko_failed//if_same.
      by rewrite !is_ko_next_alt// !if_same.
    - move=> A HA l B HB s kA.
      have {HB}HA := HA s kA.
      apply: run_dead => /=.
        by rewrite is_ko_failed.
      by rewrite is_ko_success//=is_ko_failed//is_ko_next_alt//.
  Qed.

  Lemma run_success1 u p fv A s: 
    success A -> run u p fv s A (Some (get_substS s A)) (build_na A (next_alt true A)) false.
  Proof.
    move=> sA.
    by apply: run_done.
  Qed.

  Lemma run_success u p fv A s1 s2 r n: 
    success A -> run u p fv s1 A s2 r n -> [/\ s2 = Some (get_substS s1 A), r = build_na A (next_alt true A) & n = false].
  Proof.
    move=> sA H; have:= success_step u p fv s1 sA.
    by inversion H; clear H; try congruence; subst; rewrite success_step//; rewrite failed_success in sA.
  Qed.

  Lemma run_consistent u p fv s A s1 B s2 C n1 n2:
    run u p fv s A s1 B n1 -> run u p fv s A s2 C n2 -> [/\ (s2 = s1), (C = B) & (n2 = n1)].
  Proof.
    move=> H; elim: H s2 C n2; clear.
    + move=> s1 _ A _ ? sA <-<- s3 C n2 H; subst.
      by apply: run_success sA H.
    + move=> s1 s2 r A B n1 ?? HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - by rewrite success_step in HA.
      - move: H0; rewrite HA => -[??]; subst.
        by case: (IH _ _ _ H1); subst.
      - by rewrite failed_step in HA.
      - by rewrite failed_step in HA.
    + move=> s1 s2 r A B n1 ?? HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - by rewrite success_step in HA.
      - move: H0; rewrite HA => -[??]; subst; by case: (IH _ _ _  H1); subst.
      - by rewrite failed_step in HA.
      - by rewrite failed_step in HA.
    + move=> s1 s2 A B r n1 ? fA nB rB IH s3 C n2 H.
      inversion H; clear H; try congruence; subst; try by rewrite failed_step in H0.
        by rewrite success_failed in fA.
      move: H1; rewrite nB => -[?]; subst.
      by apply: IH.
    + move=> s1 A ? fA nA s2 C n2 H.
      inversion H; subst; try congruence; try rewrite //failed_step// in H0.
      by rewrite success_failed in fA.
  Qed.

  Lemma tree_fv_step_cut u p A B fv fv' s:
    step u p fv s A = (fv', CutBrothers, B) -> fv' = fv.
  Proof.
    elim: A B fv fv' s => //=.
      by move=> [|?]????; [congruence|rewrite push].
      by move=> ??????>; rewrite !push; case: ifP => /=; case: step => [[?[]]]//.
    move=> A HA B0 B HB C fv fv' s.
    rewrite!push; case eA: step => [[?[]] A']//=.
      move=> [<- _]; by apply: HA eA.
    have [[??] _] := step_success eA; subst.
    case eB: step => [[?[]]]//=[<- _].
    by apply: HB eB.
  Qed.

End RunP.
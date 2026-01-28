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
    - move=> A HA s B HB s1 /= /andP[kA kB]; rewrite HA//.
    - move=> s B HB s1/= kB; rewrite HB//.
    - move=> A HA B0 B HB s1 /= kA; rewrite HA//.
  Qed.

  Lemma failed_big_and t: failed (big_and t) = false.
  Proof. case: t => [|[]]//. Qed.

  Lemma is_ko_big_and r: is_ko (big_and r) = false.
  Proof. apply/contraFF/failed_big_and/r/is_ko_failed. Qed.

  (*SNIP: success_step*)
  Lemma success_step u p fv s A: success A -> step u p fv s A = (fv, Success, A).
  (*ENDSNIP: success_step*)
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /= sA; rewrite HA//.
    + move=> s B HB/= _ sB; rewrite HB//.
    + move=> A HA B0 B HB s /=/andP[sA sB]; rewrite HA//HB//.
  Qed.

  Ltac case_step_tag X A := let fv := fresh "_fv" in case X : step => [[fv []] A].
  Tactic Notation "case_step_tag" ident(X) ident(A) := case_step_tag X A.

  Lemma step_success u p fv fv' {s1 A B}: 
    step u p fv s1 A = (fv', Success, B) -> ((fv' = fv) * (B = A) * (success A))%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + by move=> /= ???? [? <-].
    + by move=> []//= ?????; case: backchain.
    + move=> A HA s B HB ?? s1 C/=.
      by case_step_tag X B1 => //=-[??]; subst; rewrite !(HA _ _ _ _ X).
    + move=> s B HB ?? s1 C/=.
      by case_step_tag X B1 => //=-[??]; subst; rewrite !(HB _ _ _ _ X).
    + move=> A HA B0 B HB s1 ?? C /=.
      case_step_tag X A1 => //=; case_step_tag Y B1 => //= -[??]; subst.
      have [[??]->] := HA _ _ _ _ X; subst.
      by rewrite !(HB _ _ _ _ Y).
  Qed.

  Ltac push := rewrite !push.

  Lemma step_failed u p fv fv' s1 A B:
    step u p fv s1 A = (fv', Failed, B) -> ((fv = fv') * (B = A) * failed A)%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + move=> ?? s1 B[<-]//.
    + by move=> []//= ?????; push.
    + move=> A HA s B HB ?? s1 C/=; push.
      by case: ifP => dA /= [e + <-]{C}/=; do [case_step_tag S B1] in e * => //; subst; rewrite !(HA _ _ _ _ S).
    + move=> s B HB ?? s1 C/=; push.
      by case: ifP => dA /= [e + <-]{C}/=; do [case_step_tag S B1] in e * => //; subst; rewrite !(HB _ _ _ _ S).
    + move=> A HA B0 B HB ?? s1 C /=.
      case_step_tag X A1 => //=.
        by move=> -[??]; subst; rewrite !(HA _ _ _ _ X).
      case_step_tag Y B1 => //= -[??]; subst.
      rewrite !(step_success X) in Y *.
      by rewrite !(HB _ _ _ _ Y) orbT.
  Qed.

  Lemma is_ko_next_alt {A} b: is_ko A -> next_alt b A = None.
  Proof.
    elim: A b => //=.
      by move=> A HA s1 B HB b /= /andP[kA kB]; rewrite HA//HB.
      by move=> s1 B HB b /= kB; rewrite HB.
    move=> A HA l B HB /= b kA.
    by rewrite is_ko_success//HA//is_ko_failed.
  Qed.

  Lemma next_alt_None_failed {A}: 
    next_alt false A = None -> failed A.
  Proof.
    elim: A => //=.
    - move=> A + s1 B +/=; do 2 case: next_alt => //.
    - move=> s1 B +/=; case: next_alt => //.
    - move=> A + l B +.
      case sA: success.
        rewrite (success_failed sA)/=.
        by case: (next_alt _ B) => //=; auto.
      by case: ifP.
  Qed.

  Lemma next_alt_cutr {A b}:
    next_alt b (cutr A) = None.
  Proof. apply: is_ko_next_alt is_ko_cutr. Qed.

  (* Lemma is_dead_next_alt {A} b: is_dead A -> next_alt b A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed. *)

  Lemma next_alt_cutl_success {A}:
    success A -> next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB sA; rewrite HA//is_ko_next_alt//.
    - move=> s B HB sA; rewrite HB//is_ko_next_alt//.
    - move=> A HA l B HB /andP[sA sB].
      rewrite sA/= success_cut sA HA// HB//.
  Qed.

  Lemma next_alt_cutl_failed {A b}:
    failed (cutl A) -> next_alt b (cutl A) = None.
  Proof.
    elim: A b => //=.
    - move=> A HA s B HB b fA; rewrite HA// is_ko_next_alt//.
    - move=> s B HB b fA; rewrite HB// is_ko_next_alt//.
    - move=> A HA l B HB b.
      case: ifP => sA//=.
      rewrite failed_success_cut success_cut sA/=.
      move=> fB.
      rewrite HB//=next_alt_cutl_success//.
  Qed.

  Lemma next_alt_cutl_failedF {A b}:
    failed A -> next_alt b (cutl A) = None.
  Proof. move=> /failed_cut /next_alt_cutl_failed//. Qed.

  Lemma next_alt_cutl {A}:
    next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; rewrite HA//is_ko_next_alt//.
    - move=> s B HB; rewrite HB//is_ko_next_alt//.
    - move=> A HA l B HB; case: ifP => //sA/=.
      by rewrite success_cut sA HB HA //.
  Qed.

  Lemma step_not_solved u p fv  s1 A r:
    step u p fv s1 A = r -> ~ (is_sc r.1.2) -> success A = false.
  Proof. by case: r => -[?[]]//=b; case X: success; rewrite // (success_step _ _ _ s1 X). Qed.

  (*SNIP: failed_step*)
  Lemma failed_step u p fv s1 A: failed A -> step u p fv  s1 A = (fv, Failed, A).
  (*ENDSNIP: failed_step*)
  Proof.
    elim: A s1; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2/=fA; rewrite HA//.
    + move=> s1 B HB s2/=fA; rewrite HB//.
    + move=> A HA B0 B HB s/=.
      case X: failed => /=.
        move=>_; rewrite HA => //.
      move=>/andP[sA fB].
      by rewrite success_step//HB.
  Qed. 

  Lemma step_not_failed u p fv s1 A r:
    step u p fv s1 A = r -> ~ (is_fl r.1.2) -> failed A = false.
  Proof.
    move=><-; clear r.
    elim: A s1; try by move=> // s1 <-//=.
    - move=> A HA s B HB s1/=; have:= HA s1; case_step_tag X B1 => //=.
    - move=> s B HB s1/=; have:= HB s; case_step_tag X B1 => //=.
    - move=> A HA B0 B HB s1/=.
      have:= HA s1.
      case_step_tag X A1 => //=; only 1,2: by move=> H/H->; rewrite (step_not_solved X).
      move=> /(_ notF)->//=.
      have [[-> <-] ->]:= (step_success X); subst.
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

  Lemma next_alt_failed {b A r}: next_alt b A = r -> failed (odflt OK r) = false.
  Proof.
    move=><-; elim: A b {r} => //=.
    - move=> []//.
    - move=> A HA s B HB b; have:= HA b; case: next_alt => //=.
      by have:= HB false; case: next_alt.
    - move=> s B HB b; have:= HB b; case: next_alt => //=.
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
    Definition same_structure A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => true
        | _ => false
        end
      | Or A1 s B1 =>
        match B with 
        | Or A' s' B' => (s == s') && ((A1 != None) || (A' == None))
        | _ => false
        end
      | _ => true
      end.

    Lemma same_structure_refl {A}: same_structure A A.
    Proof. by case: A => //=>; rewrite orNb eqxx. Qed.

    Hint Resolve same_structure_refl : core.

    Lemma same_structure_trans: transitive same_structure.
    Proof.
      move=> +[]//=.
        move=> []//= > _ > _ []// > _ /andP[/eqP<-+]/andP[/eqP<-+]; rewrite eqxx/=.
        by move=> /orP[->|/eqP->]//=->; rewrite orbT.
      by move=> []//.
    Qed.

    Lemma step_same_structure u p fv s A r: 
      step u p fv s A = r -> same_structure A r.2.
    Proof.
      move=><-{r}; case: A=> //=[[]|]>; rewrite !push//=?eqxx//.
      by case: ifP => //.
    Qed.

    Lemma next_alt_same_structure {b A B}:
      next_alt b A = Some B -> same_structure A B.
    Proof.
      case: A => //=.
      - move=> [t|]//= ??; case n: next_alt => //=; only 1, 3: by move=> [<-]; rewrite eqxx.
        by case: next_alt => //?[<-]; rewrite eqxx.
      - move=> >; repeat case: ifP => _.
          by (do 2 case: next_alt => //=) => >; first move=>??; move=> [<-].
          by case: next_alt => [a|]//[<-].
        by move => [<-].
    Qed.

    Lemma run_same_structure u p fv1 fv2 s A s1 r n:
      run u p fv1 s A s1 r n fv2 -> same_structure A (odflt A r).
    Proof.
      elim; clear => //.
      - move=> s1 s2 A B ? sA _ <-/=.
        case X: next_alt => [B'|]/=; subst; move: X => //.
        by move=> /next_alt_same_structure//.
      - move=> s1 s2 r A B n ??? /step_same_structure/= + _.
        destruct r => //=.
        apply: same_structure_trans.
      - move=> s1 s2 r A B n ??? /step_same_structure/= + _.
        destruct r => //=.
        apply: same_structure_trans.
      - move=> s1 s2 A B oB r n ??.
        move=> /next_alt_same_structure + _.
        destruct oB => //=.
        apply: same_structure_trans.
    Qed.
  End same_structure.

  Lemma ges_subst_cutl {s A} : 
    success A -> get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=; auto.
    move=> A HA B0 B HB s /andP[sA sB]; rewrite sA/=success_cut sA HA// HB//.
  Qed.

  Lemma next_alt_not_failed {A}:
    (failed A) = false -> next_alt false A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB fA; rewrite HA//=.
    - move=> s B HB fB; rewrite HB//=.
    - move=> A HA l B HB.
      case fA: failed => //.
      case sA: success => //= fB; rewrite (HA, HB)//=.
  Qed.

  Lemma next_alt_not_success {A b}:
    failed A = false ->
      (success A) = false -> next_alt b A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB fA sA; rewrite HA//.
    - move=> s B HB fA sA; rewrite HB//.
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
    - move=> A HA s B HB b sA; rewrite HA//.
    - move=> s B HB b sA; rewrite HB//.
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

  Lemma is_ko_run u p fv s A: is_ko A -> run u p fv s A None None false fv.
  Proof.
    elim_tree A s => /=.
    - by move=> _; apply: run_dead => //=.
    - move=> /andP[kA kB].
      have {}HA := HA s kA.
      have {}HB := HB s kB.
      apply: run_dead; rewrite/=.
      by rewrite !is_ko_next_alt// !if_same.
    - move=> kB.
      have {}HB := HB s kB.
      apply: run_dead; rewrite/=.
      by rewrite !is_ko_next_alt// !if_same.
    - move=> kA.
      have {HB}HA := HA s kA.
      apply: run_dead => /=.
      by rewrite is_ko_success//=is_ko_failed//is_ko_next_alt//.
  Qed.

  Lemma run_success1 u p fv A s: 
    success A -> run u p fv s A (Some (get_substS s A)) ((next_alt true A)) false fv.
  Proof.
    move=> sA.
    by apply: run_done.
  Qed.

  Lemma run_success u p fv A s1 s2 r n fv1: 
    success A -> run u p fv s1 A s2 r n fv1 -> [/\ s2 = Some (get_substS s1 A), r = (next_alt true A), fv1 = fv & n = false].
  Proof.
    move=> sA H; have:= success_step u p fv s1 sA.
    inversion H; clear H; try congruence; subst; rewrite success_step//; rewrite failed_success in sA => //=.
    by rewrite next_alt_None_failed.
  Qed.

  Lemma run_consistent u p fv s A s1 B s2 C n1 n2 fv1 fv2:
    run u p fv s A s1 B n1 fv1 -> run u p fv s A s2 C n2 fv2 -> [/\ (s2 = s1), (C = B), fv2 = fv1 & (n2 = n1)].
  Proof.
    move=> H; elim: H s2 C n2; clear.
    + move=> s1 _ A _ ? sA <-<- s3 C n2 H; subst.
      by apply: run_success sA H.
    + move=> s1 s2 r A B n1 ??? HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - by rewrite success_step in HA.
      - move: H0; rewrite HA => -[??]; subst.
        by case: (IH _ _ _ H1); subst.
      - by rewrite failed_step in HA.
      - by rewrite (failed_step _ _ _ _ (next_alt_None_failed _)) in HA.
    + move=> s1 s2 r A B n1 ??? HA HB IH s4 r' n2 H.
      inversion H; clear H; try congruence; subst.
      - by rewrite success_step in HA.
      - move: H0; rewrite HA => -[??]; subst; by case: (IH _ _ _  H1); subst.
      - by rewrite failed_step in HA.
      - by rewrite (failed_step _ _ _ _ (next_alt_None_failed _)) in HA.
    + move=> s1 s2 A B r n1 ?? fA nB rB IH s3 C n2 H.
      inversion H; clear H; try congruence; subst; try by rewrite failed_step in H0.
        by rewrite success_failed in fA.
      move: H1; rewrite nB => -[?]; subst.
      by apply: IH.
    + move=> s1 A ? nA s2 C n2 H.
      have fA:= next_alt_None_failed nA.
      inversion H; subst; try congruence; try rewrite //failed_step// in H0.
      by rewrite success_failed in fA.
  Qed.

  Lemma tree_fv_step_cut u p A R fv fv' s:
    step u p fv s A = (fv', CutBrothers, R) -> fv' = fv.
  Proof.
    elim_tree A R fv fv' s => /=.
      by case: t => [|c]/=; [congruence|rewrite push].
      by push; case: step => [[?[]]]//.
      by push; case: step => [[?[]]]//.
    rewrite!push; case eA: step => [[?[]] A']//=.
      move=> [<- _]; by apply: HA eA.
    have [[??] _] := step_success eA; subst.
    case eB: step => [[?[]]]//=[<- _].
    by apply: HB eB.
  Qed.

End RunP.
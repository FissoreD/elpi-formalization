From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang tree.
From det Require Import zify_ssreflect.

Ltac case_step_tag X A := let fv := fresh "_fv" in case X : step => [[fv []] A].
Tactic Notation "case_step_tag" ident(X) ident(A) := case_step_tag X A.

Section RunP.
  (* Variable u: Unif.
  Variable p : program.
  Notation step := (step u p).
  Notation runT := (runT u p). *)

  (********************************************************************)
  (* EXPAND PROPERTIES                                                *)
  (********************************************************************)

  Variable u : Unif.
  Notation step := (step u).

  Lemma path_atom_or_Some A sm B: path_atom (Or (Some A) sm B) = path_atom A.
  Proof. by rewrite/path_atom path_end_or_Some. Qed.

  Lemma path_atom_or_None sm B: path_atom (Or None sm B) = path_atom B.
  Proof. by rewrite/path_atom path_end_or_None. Qed.

  Lemma path_atom_and A B0 B: path_atom (And A B0 B) = if success A then path_atom B else path_atom A.
  Proof. rewrite/path_atom path_end_and; case: ifP => //. Qed.

  Definition rew_pa:= 
  (
    path_atom_or_None, path_atom_or_Some,path_atom_and,
    success_or_None, success_or_Some, success_and,
    failed_or_None, failed_or_Some, failed_and
  ).

  Lemma failed_big_and t: failed (big_and t) = false.
  Proof. case: t => /=[|x []]//. Qed.

  Lemma success_step: forall p fv s A, success A -> step p fv s A = (fv, Success, A).
  Proof.
    move=> p fv s A.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /= sA; rewrite HA//.
    + move=> s B HB/= _ /[!success_or_None] sB; rewrite HB//.
    + move=> A HA B0 B HB s /=/[!success_and]/andP[sA sB]; rewrite sA HB//.
  Qed.

  Lemma step_success p fv fv' {s1 A B}: 
    step p fv s1 A = (fv', Success, B) -> ((fv' = fv) * (B = A) * (success A))%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + by move=> /= ???? [? <-].
    + by move=> []//= ?????; case: bc.
    + move=> A HA s B HB ?? s1 C/=.
      by case_step_tag X B1 => //=-[??]; subst; rewrite success_or_Some !(HA _ _ _ _ X).
    + move=> s B HB ?? s1 C/=.
      by case_step_tag X B1 => //=-[??]; subst; rewrite success_or_None !(HB _ _ _ _ X).
    + move=> A HA B0 B HB s1 ?? C /=.
      case sA: success; case_step_tag X A1 => //= -[??]; subst; rewrite success_and sA.
        by rewrite !(HB _ _ _ _ X).
      by rewrite !(HA _ _ _ _ X) in sA.
  Qed.

  (*SNIP: success_step*)
  Lemma succ_step_iff: forall p v s A, success A <-> step p v s A = (v, Success, A).
  (*ENDSNIP: success_step*)
  Proof. by split; [move=> /success_step->|move=>/step_success->]. Qed.

  Ltac push := rewrite !push.

  Lemma step_failed p fv fv' s1 A B:
    step p fv s1 A = (fv', Failed, B) -> ((fv = fv') * (B = A) * failed A)%type.
  Proof.
    elim: A fv fv' s1 B => //.
    + move=> ?? s1 B[<-]//.
    + by move=> []//= ?????; push.
    + move=> A HA s B HB ?? s1 C/=; push.
      by case: ifP => dA /= [e + <-]{C}/=; do [case_step_tag S B1] in e * => //; subst; rewrite failed_or_Some !(HA _ _ _ _ S).
    + move=> s B HB ?? s1 C/=; push.
      by case: ifP => dA /= [e + <-]{C}/=; do [case_step_tag S B1] in e * => //; subst; rewrite failed_or_None !(HB _ _ _ _ S).
    + move=> A HA B0 B HB ?? s1 C /=.
      rewrite failed_and.
      case: ifP => sA.
        rewrite success_failed//=.
        by case_step_tag Y B1 => //= -[??]; subst; rewrite !(HB _ _ _ _ Y).
      case_step_tag X A1 => //=.
      by move=> -[??]; subst; rewrite !(HA _ _ _ _ X).
  Qed.

  Lemma failed_step p fv s1 A: failed A -> step p fv  s1 A = (fv, Failed, A).
  Proof.
    elim: A s1; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2/=fA; rewrite HA//.
    + move=> s1 B HB s2/= /[!failed_or_None] fA; rewrite HB//.
    + move=> A HA B0 B HB s/=.
      rewrite failed_and.
      case X: failed => /=.
        by move=>_; rewrite HA// failed_success.
      move=>/andP[sA fB]; rewrite sA HB//.
  Qed. 

  (*SNIP: failed_step*)
  Lemma fail_step_iff: forall p v s A, failed A <-> step p v s A = (v, Failed, A).
  (*ENDSNIP: failed_step*)
  Proof. by split; [move=> /failed_step->|move=>/step_failed->]. Qed.


  (*SNIP: naNfail*)
  Lemma next_altFN_fail: forall A, next_alt false A = None -> failed A.
  (*ENDSNIP: naNfail*)
  Proof.
    move=> A; elim_tree A => /=.
    - by move: HA HB; do 2 case: next_alt.
    - by move: HB; case: next_alt; rewrite//rew_pa; auto.
    - rewrite rew_pa; move: HA HB.
      case sA: success.
        rewrite (success_failed sA)/=.
        by case: (next_alt _ B) => //=; auto.
      by case: ifP.
  Qed.

  (* Lemma is_dead_next_alt {A} b: is_dead A -> next_alt b A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed. *)

  Lemma next_alt_cutl_success {A}:
    success A -> next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB sA; rewrite HA//is_ko_next_alt//.
    - move=> s B HB /[!success_or_None] sA; rewrite HB//.
    - move=> A HA l B HB /[!success_and] /andP[sA sB].
      rewrite sA/= success_cut sA HA// HB//.
  Qed.

  Lemma next_alt_cutl_failed {A b}:
    failed (cutl A) -> next_alt b (cutl A) = None.
  Proof.
    elim: A b => //=.
    - move=> A HA s B HB b fA; rewrite HA// is_ko_next_alt//.
    - move=> s B HB b /[!failed_or_None] fA; rewrite HB// is_ko_next_alt//.
    - move=> A HA l B HB b.
      case: ifP => sA//=.
      rewrite failed_and failed_success_cut success_cut sA/=.
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

  Lemma step_not_solved p fv  s1 A r:
    step p fv s1 A = r -> ~ (is_sc r.1.2) -> success A = false.
  Proof. by case: r => -[?[]]//=b; case X: success; rewrite // (success_step _ _ s1 X). Qed.

  Lemma step_not_failed p fv s1 A r:
    step p fv s1 A = r -> ~ (is_fl r.1.2) -> failed A = false.
  Proof.
    move=><-; clear r.
    elim: A s1; try by move=> // s1 <-//=.
    - move=> A HA s B HB s1/=; have:= HA s1; case_step_tag X B1 => //=.
    - move=> s B HB s1/= /[!failed_or_None] ; have:= HB s; case_step_tag X B1 => //=.
    - move=> A HA B0 B HB s1/=/[!failed_and].
      case: ifP => sA/=.
        by rewrite success_failed//; have:= HB (get_subst s1 A); case: step => [[?[]]]//=.
      by have:= HA s1; case_step_tag X A1 => //=->.
  Qed.

  (********************************************************************)
  (* NEXT_ALT OP PROPERTIES                                           *)
  (********************************************************************)


  (*SNIP: na_failed *)
  Lemma next_alt_failedF b A A': next_alt b A = Some A' -> failed A' = false.
  (*ENDSNIP: na_failed *)
  Proof.
    elim_tree A b A' => //=.
    - by case: b => //-[<-].
    - move=> [<-]//.
    - have:= HA b; case: next_alt => //=.
        by move=> X /(_ _ erefl) + [<-]; rewrite rew_pa.
      by have:= HB false; case: next_alt => //= ? /(_ _ erefl) + _ [<-]; rewrite rew_pa.
    - by have:= HB b; case: next_alt => //=?/(_ _ erefl)+ [<-]; rewrite rew_pa.
    - case: ifP => sA.
        have:= HB b; case: next_alt => [X|]//=.
          by move=> /(_ _ erefl) + [<-]; rewrite rew_pa (success_failed sA) sA.
        by case nA: next_alt => //= _ [<-]; rewrite rew_pa (HA _ _ nA) failed_big_and andbF.
      case: ifP => /=fA; last by move=> [<-]; rewrite rew_pa sA fA.
      by case nA: next_alt => //=-[<-]; rewrite rew_pa (HA _ _ nA) failed_big_and andbF.
  Qed.

  (* Lemma failed_big_or u p fv s t: failed (backchain u p fv s t).2.
  Proof. rewrite/backchain; case: bc => // ? -[|[]]//. Qed. *)

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

    Lemma step_same_structure p fv s A r: 
      step p fv s A = r -> same_structure A r.2.
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

    Lemma run_same_structure p fv1 fv2 s A x n:
      runT u p fv1 s A (Some x) n fv2 -> same_structure A (odflt A x.2).
    Proof.
      case: x => //= + []//= => s' A'.
      remember (Some _) as sx eqn:Hx => H.
      elim_run H s' A' Hx => //=.
      - by move: Hx => [?]; subst => /=; apply/next_alt_same_structure.
      - apply: same_structure_trans (step_same_structure eA) (IH _ _ erefl).
      - apply: same_structure_trans (next_alt_same_structure nA) (IH _ _ erefl).
    Qed.
  End same_structure.

  Lemma get_subst_or_None s sm B: get_subst s (Or None sm B) = get_subst sm B.
  Proof. by rewrite/get_subst/=. Qed.
  
  Lemma get_subst_or_Some s sm A B: get_subst s (Or (Some A) sm B) = get_subst s A.
  Proof. by rewrite/get_subst/=. Qed.

  Lemma get_subst_and s A B0 B : 
    get_subst s (And A B0 B) = if success A then get_subst (get_subst s A) B else get_subst s A. 
  Proof. by rewrite/get_subst/success/=/path_end push !path_endP; case: path_end => //. Qed.

  Lemma ges_subst_cutl {s A} : 
    success A -> get_subst s (cutl A) = get_subst s A.
  Proof.
    elim_tree A s => //=; auto.
      move=> /[!success_or_Some]/HA{}HA/[!get_subst_or_Some]//.
      move=> /[!success_or_None]/HB{}HB/[!get_subst_or_None]//.
    rewrite success_and fun_if !get_subst_and success_cut => /andP[sA sB].
    by rewrite sA HB//HA//.
  Qed.

  Lemma failedF_next_alt {A}:
    failed A = false -> next_alt false A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB fA; rewrite HA//=.
    - move=> s B HB /[!failed_or_None] fB; rewrite HB//=.
    - move=> A HA l B HB /[!failed_and].
      case fA: failed => //.
      case sA: success => //= fB; rewrite (HA, HB)//=.
  Qed.

  Lemma next_alt_big_and r:
    next_alt false (big_and r) = Some (big_and r).
  Proof. case: r => //=+l; elim: l => //. Qed.

  Lemma next_alt_big_or r rs:
    next_alt false (big_or r rs) = Some (big_or r rs).
  Proof.
    elim: rs r => //= [|[sr r] rs IH] r0/=;
    by rewrite ?is_dead_big_and next_alt_big_and//.
  Qed.

  Lemma get_substS_big_and A s1:
    get_subst s1 (big_and A) = s1.
  Proof. case: A => //+l; elim: l => //. Qed.

  Lemma get_subst_and_big_and s1 A B C: get_subst s1 (And A B (big_and C)) = get_subst s1 A.
  Proof. by rewrite get_subst_and get_substS_big_and if_same. Qed.

  Lemma tree_fv_step_cut p A R fv fv' s:
    step p fv s A = (fv', CutBrothers, R) -> fv' = fv.
  Proof.
    elim_tree A R fv fv' s => /=.
      by case: t => [|c]/=; [congruence|rewrite push].
      by push; case: step => [[?[]]]//.
      by push; case: step => [[?[]]]//.
    case: ifP => sA; rewrite !push => -[<-].
      case_step_tag eB X => //= _ _; apply: HB eB.
    case_step_tag eA A' => //= _ _; apply: HA eA.
  Qed.

  Lemma path_atom_exp_cut p A fv s r:
    path_atom A -> step p fv s A = r -> r.1.2 = CutBrothers \/ r.1.2 = Expanded.
  Proof.
    move=> + <-{r}.
    elim_tree A fv s => //=.
    - destruct t; auto; rewrite push; auto.
    - move=> /[!path_atom_or_Some] pA; rewrite !push/=.
      have [] := HA fv s pA; case_step_tag eA A' => //=; auto.
    - move=> /[!path_atom_or_None] pA; rewrite !push/=.
      have [] := HB fv sm pA; case_step_tag eA A' => //=; auto.
    - move=> /[!path_atom_and]; case: ifP => sA pH; rewrite !push/=.
        by apply: HB.
      by apply: HA.
  Qed.

  Lemma path_atom_cut p A fv s fv' A':
    step p fv s A = (fv', CutBrothers, A') -> path_atom A.
  Proof.
    elim_tree A fv s fv' A' => /=; rewrite !push.
    - by case_step_tag eA A2 => //=.
    - by case_step_tag eA A2 => //=.
    - case: ifP=> sA; case_step_tag eA A2 => //= -[??]; subst; rewrite path_atom_and sA.
        apply: HB eA.
      apply: HA eA.
  Qed.

  Lemma path_atom_exp p A fv s fv' A':
    step p fv s A = (fv', Expanded, A') -> path_atom A.
  Proof.
    elim_tree A fv s fv' A' => /=; rewrite !push.
    - case_step_tag eA A2 => //=-[??]; subst; rewrite path_atom_or_Some.
        apply: HA eA.
      apply: path_atom_cut eA.
    - case_step_tag eA A2 => //=-[??]; subst; rewrite path_atom_or_None.
        apply: HB eA.
      apply: path_atom_cut eA.
    - case: ifP=> sA; case_step_tag eA A2 => //= -[??]; subst; rewrite path_atom_and sA.
        apply: HB eA.
      apply: HA eA.
  Qed.

  (*SNIP: path_atom_next_alt_id*)
  Lemma path_atom_next_alt_id b A: path_atom A -> next_alt b A = Some A.
  (*ENDSNIP: path_atom_next_alt_id*)
  Proof.
    elim_tree A b => /=; rewrite ?rew_pa.
    - move=> /HA->//.
    - move=> /HB->//.
    - case: ifP => [sA /HB->|]// sA /path_atom_failed->//.
  Qed.

  Lemma next_alt_run p fv fv' A B C s b1:
    next_alt false A = B ->
      runT u p fv s (odflt A B) C b1 fv' ->
        runT u p fv s A C b1 fv'.
  Proof.
    move=> <-{B}.
    case fA: (failed A).
      case X: next_alt => [A'|]//= H.
      by apply: BackT fA X H.
    rewrite failedF_next_alt//.
  Qed.
End RunP.
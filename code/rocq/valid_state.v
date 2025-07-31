From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run_prop.


Module valid_state (U:Unif).
  Module RunP := RunP(U).
  Import RunP Run Language.
  
  Fixpoint base_and s :=
    match s with
    | And (Goal _ _) r r1 => (r == r1) && base_and r1 (* should also say something about the program *)
    | Top => true
    | _ => false
    end.

  Lemma base_and_dead {A}: base_and A -> is_dead A = false.
  Proof. case: A => // -[]//=. Qed.

  Lemma base_and_big_and {pr A}: base_and (big_and pr A).
  Proof. by elim: A => // a l /= ->; rewrite eq_refl. Qed.

  Fixpoint base_or_aux s :=
    match s with
    | Or l _ r => base_and l && (base_or_aux r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and t
    end.

  Fixpoint base_and_ko s :=
    match s with
    | And KO r r1 => [&&base_and_ko r, (r == r1) & base_and_ko r1] (* should also say something about the program *)
    | KO => true
    | _ => false
    end.


  Definition base_or s := 
    match s with 
    | KO => true
    | Or KO _ t => base_or_aux t
    | _ => false
    end.

  Fixpoint base_or_aux_ko s :=
    match s with
    | Or l _ r => base_and_ko l && (base_or_aux_ko r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and_ko t
    end.


  Lemma base_or_dead {B}: base_or_aux B || base_or_aux_ko B -> is_dead B = false.
  Proof.
    move=>/orP[].
      elim: B => //.
        move=> A HA s B HB /=/andP[bA bB].
        rewrite HB//andbF//.
      move=> []//.
    elim: B => //.
      move=> A HA s B HB /=/andP[bA bB].
      rewrite HB//andbF//.
    move=>[]//.
  Qed.

  Definition bbOr B := base_or_aux B || base_or_aux_ko B. 
  Definition bbAnd B := base_and B||base_and_ko B. 

  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Top => true
    | Dead => false
    | Or A _ B => 
      if is_dead A then valid_state B
      else valid_state A && (bbOr B)
    | And A B0 B => 
      [&& valid_state A,
        if success A then valid_state B 
        else (B0 == B)
        & (bbAnd B0)]
    end.

  Lemma valid_state_dead {A} : is_dead A -> valid_state A = false.
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[->]//.
    move=> A HA Bo ? B HB/=dA.
    rewrite HA//.
  Qed.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA; rewrite (HVA HA) /=.
    rewrite /bbAnd HA eqxx//.
  Qed.

  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof. apply: base_and_valid base_and_big_and. Qed.

  Lemma bbAnd_valid {A} : bbAnd A -> valid_state A.
  Proof.
    move=>/orP[].
      apply: base_and_valid.
    elim: A=> //.
    move=> []// _ B0 HB0 B HB/=/and3P[H/eqP->]bB.
    rewrite eqxx /bbAnd bB orbT//.
  Qed.

  Lemma bbOr_big_or_aux {pr s l}: bbOr (big_or_aux pr s l).
  Proof.
    rewrite/bbOr.
    case: base_or_aux_ko; rewrite ?orbT//orbF.
    elim: l s => //=; clear.
    + move=> []//*; rewrite /base_or_aux //= base_and_big_and eqxx//.
    + by move=> [[s r] rs] IH r1 /=; rewrite IH base_and_big_and.
  Qed.

  Lemma valid_state_big_or {pr s t} : valid_state (big_or pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + by move=> ?; case: F => //= -[] //=???; rewrite bbOr_big_or_aux.
    + by move=> ?; case: F => //= -[] //=???; rewrite bbOr_big_or_aux.
    + by move=> ??; case F => //= -[] //=???; rewrite bbOr_big_or_aux.
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof.
    elim: B => //.
    move=> []// HA B0 _ B HB/= /and3P[bB0 /eqP <-] H.
    by rewrite /bbAnd ?eqxx H ?orbT.
  Qed.

  Lemma bbOr_valid {B}:
    bbOr B -> valid_state B.
  Proof. 
    move=> /orP [].
    elim B => //; clear.
    + move=> A HA s B HB/=/andP[bA bB].
      case:ifP => dA.
        apply: HB bB.
      rewrite /bbOr bB // base_and_valid//.
    + move=> []// p a Ha B0 HB0 B HB /=/andP[/eqP->]bB.
      by rewrite /bbAnd eqxx bB ?(ssa_id bB).
    elim: B => //.
    + move=> A HA s B HB /= /andP [] /base_and_ko_valid -> H.
      rewrite /bbOr H orbT HB// if_same//.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      rewrite /bbAnd bB0 eqxx ?orbT//.
  Qed.

  Lemma simpl_valid_state_or {s A B}: 
    valid_state (Or A s B) -> 
      (is_dead A /\ valid_state B) \/ 
      (is_dead A = false /\ valid_state A /\ (bbOr B)).
  Proof.
    move=> /=; case: A => //.
    all: try by move=> /= ->; right; repeat split => //; rewrite orbT //.
    + move=> /= ->; left => //.
    + move=> ??/= ->; auto.
    + move=> ??? /=; case:ifP; auto.
      move=> H/andP[]->->; auto.
    + move=> ???; case:ifP; auto.
      move=>? /andP[]->->; auto.
  Qed.

  Lemma simpl_valid_state_and1 {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ 
      (if success A then valid_state B else B0 == B) /\ bbAnd B0.
  Proof. by move=>/=/and3P[]//->->/andP[]->->. Qed.

  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //= _ _ _ HB HC /andP [] /eqP <-bB.
    rewrite HB//eqxx//.
  Qed.

  Lemma base_and_ko_base_and_ko_cutr {B} : base_and_ko B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // -[]//_ A HA B HB/=/and3P[bA/eqP->bB].
    rewrite HB//eqxx//.
  Qed.

  Lemma base_and_base_and_ko_cutr {B} : base_and B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //= _ _ _ HB HC /andP [] /eqP <- hB.
    rewrite eqxx HB//.
  Qed.
  
  Lemma base_or_base_or_ko_cutr {B}: base_or_aux B -> base_or_aux_ko (cutr B).
  Proof.
    elim: B => //.
    + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cutr -> /IHB ->//.
    + move=> [] //= _ _ _ B HB C HC /andP [] /eqP /[subst1] hC.
      rewrite base_and_base_and_ko_cutr//eqxx//.
  Qed.

  Lemma base_or_ko_cutr {B}: base_or_aux_ko B -> base_or_aux_ko (cutr B).
  Proof.
    elim: B => //.
      move=> A HA s B HB /= /andP[bA bB].
      rewrite HB//base_and_ko_base_and_ko_cutr//.
    move=> [] //= _ B0 _ B HB /and3P[] bB0 /eqP<- _.
    rewrite base_and_ko_base_and_ko_cutr//eqxx//.
  Qed.

  Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else ((B02 == B2))) ->
      bbAnd B02 ->
        valid_state B2.
  Proof. case: success => //; move=>/eqP->. apply: bbAnd_valid. Qed.

  Lemma base_and_cutl {B0}:
    base_and B0-> base_and_ko (cutl B0).
  Proof.
    elim: B0 => //.
    move=> /=[]//p a _ B0 HB0 B HB/=/andP[/eqP<-]bB.
    rewrite HB0//.
    rewrite eqxx//.
  Qed.

  Lemma bbAnd_cutl{B0}:
    bbAnd B0 -> bbAnd (cutl B0).
  Proof.
    rewrite /bbAnd.
    case: (base_and (cutl _)) => //=.
    move=>/orP[/base_and_cutl->|]//.
    elim: B0 => //-[]//_ B0 HB0 B HB/=/and3P[bB0/eqP<- _].
    rewrite HB0//eqxx//.
  Qed.

  Lemma bbOr_cutr {B}: bbOr B -> bbOr (cutr B).
  Proof.
    rewrite/bbOr.
    move=>/orP[/base_or_base_or_ko_cutr|/base_or_ko_cutr]->; rewrite orbT//.
  Qed.

  Lemma valid_state_cut {A}: valid_state A -> valid_state (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=; rewrite 2!fun_if.
      case: ifP => /=.
        by move=>->.
      move=> dA/andP[vA bB].
      rewrite cut_dead_is_dead dA HA//=.
      apply: bbOr_cutr bB.
    move=> A HA B0 _ B HB /=/simpl_valid_state_and1[VA [H bB0]].
    have vB := valid_state_compose_and H bB0.
    rewrite success_cut (HB(valid_state_compose_and H bB0))HA//=.
    rewrite bbAnd_cutl//.
    move: H; case: ifP => //_/eqP<-//; rewrite eqxx//.
  Qed.

  Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B.
  Proof.
    move=>/= /and3P[]// -> VB bbB0.
    by rewrite (valid_state_compose_and VB bbB0).
  Qed.

  Lemma valid_state_expand {s A r}:
    valid_state A -> expand s A = r -> valid_state (get_state r).
  Proof.
    elim: A s r => //; try by move=> s r // *; subst.
    + by move=> ? [|?] ?? *;subst => //=; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1 r/=.
      case: ifP => dA.
        move=>vB/=; case X: expand => *; subst => /=; rewrite dA;
        by have:= IHB _ _ vB X.
      move=> /andP[vA bB].
      case X: expand => //=<-/=; rewrite (expand_not_dead dA X) ?bB (IHA _ _ vA X)//.
      rewrite bbOr_cutr//.
    + move=> A HA B0 _ B HB s1 r /=/and3P[vA + bB0].
      case S: (success A).
        rewrite succes_is_solved//.
        move=>vB.
        move=><-; rewrite get_state_And.
        case Y: expand=>/=; rewrite ?success_cut S bB0 (HB _ _ vB Y)?vA//.
        rewrite valid_state_cut//.
      move=>/eqP?;subst.
      case Y: expand => <-/=; last first; [have[]:=expand_solved_success Y|..];rewrite ?S //eqxx bB0 (HA _ _ vA Y)bbAnd_valid// if_same//.
  Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      rewrite valid_state_big_and bbOr_big_or_aux IH if_same//.
  Qed.

  Lemma expandedP_expanded {s A r}:
    valid_state A -> expanded s A r -> valid_state (get_state_exp r).
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
    valid_state A ->  expanded s1 A r -> valid_state (get_state_exp r).
  Proof.
    move=> + [b H].
    elim: H; clear.
    + move=> s1 s2 A B HA VA /=; apply: valid_state_expand VA HA.
    + move=> s A B HA VA; apply: valid_state_expand VA HA.
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
  Qed.

  Lemma next_alt_aux_base_and1 {A s}: base_and A -> next_alt s A = None.
  Proof.
    elim: A s => //-[]//p a _ B0 _ B HB/= c.
    move=>/andP[]/eqP? bB;subst.
    by rewrite HB.
  Qed.

  Lemma next_alt_aux_bbase_and1 {A s}: bbAnd A -> next_alt s A = None.
  Proof.
    move=>/orP[].
      apply: next_alt_aux_base_and1.
    case: A => //=-[]//.
  Qed.

  Lemma next_alt_aux_base_and2 {A s}: base_and A -> next_alt s (cutl A) = None.
  Proof. elim: A s => //-[]//p a _ B0 _ B HB/= c. Qed.

  Lemma valid_state_next_alt {s1 s2 A B}: 
    valid_state A -> next_alt s1 A = Some (s2, B) 
    -> valid_state B.
  Proof.
    elim: A s1 s2 B => //.
    + move=> A HA s B HB s1 s2 C /simpl_valid_state_or [].
        move=>[dA vB]/=; rewrite dA.
        case X: next_alt => // [[s3 D]][_<-]/=; rewrite dA.
        apply: HB vB X.
      move=> [dA [VA bB]]/=; rewrite dA.
      case X: next_alt => [[s3 D]|].
        move=>[_<-]/=; rewrite (proj2 (next_alt_dead X)) (HA _ _ _ VA X) bB//.
      rewrite base_or_dead//.
      case: ifP => //fB.
        case Y: next_alt => //[[s3 D]] []??;subst=> /=.
        rewrite is_dead_dead (HB s1 s2)//bbOr_valid//.
      move=>[_<-]/=; rewrite is_dead_dead bbOr_valid//.
    + move=> A HA B0 HB0 B HB s1 s2 C /simpl_valid_state_and1 [VA [VB bB0]]/=.
      have VB' := valid_state_compose_and VB bB0.
      case: ifP => ///eqP dA.
      case: ifP => // fA.
        case NA: next_alt => [[s3 D]|]//.
        case: ifP => //fB0 []??;subst => /=.
        rewrite bB0 eqxx (bbAnd_valid bB0) if_same !andbT.
        apply: HA VA NA.
      have N := @next_alt_aux_bbase_and1 B0 s1 bB0.
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
      by rewrite (HA _ _ _ VA NA) eqxx bB0 (bbAnd_valid bB0) if_same.
  Qed.

  Lemma base_and_clean_success {A}:
    base_and A -> A = clean_success A.
  Proof. elim: A => //; move=> []//p a _ B0 _ B HB/=/andP[/eqP-> bB]. Qed.

  Lemma bbase_and_clean_success {A}:
    bbAnd A -> A = clean_success A.
  Proof.
    move=>/orP[].
      apply: base_and_clean_success.
    case: A => //=-[]//=B C/and3P[bB /eqP<-].
  Qed.

  Lemma valid_state_clean_success {A}:
    valid_state A -> valid_state (clean_success A).
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      rewrite 2!fun_if/=.
      case: ifP => //=.
      move=> dA/andP[vA bB].
      rewrite HA//bB bbOr_valid// if_same//.
    - move=> A HA B0 _ B HB/=/and3P[vA + bB0]; rewrite (fun_if valid_state)/=.
      rewrite vA bB0 andbT//=.
      case: ifP => [sA vB|sA /eqP?]; subst.
        apply: HB vB.
      rewrite eqxx//.
  Qed.

  Lemma runP_run {s1 A s2 B}:
    valid_state A -> run s1 A s2 B -> valid_state B.
  Proof.
    move=> + [b H]; elim H; clear.
    + move=> s1 s2 A B C b EA -> VA.
      have /= H := valid_state_expanded VA (ex_intro _ _ EA).
      by apply: valid_state_clean_success.
    + move=> s1 s2 s3 A B C D b1 b2 b3 HA HB HC IH Hb VA.
      have VB := valid_state_expanded VA (ex_intro _ _ HA).
      have NA := valid_state_next_alt VB HB.
      apply: IH NA.
  Qed.

  Lemma base_and_ko_succes {B}: base_and_ko B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.

  Lemma base_and_succes {B}: base_and B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.

  Lemma base_or_succes {B}: bbOr B -> success B = false.
  Proof.
    move=>/orP[].
      elim: B => //.
        move=> A HA s B HB/=/andP[].
        case: ifP => dA.
          move=> /base_and_dead; rewrite dA//.
        by move=> /base_and_succes.
      move=> []//.
    elim: B=> //=.
      move=> A HA _ B HB/andP[].
      case: ifP=>/eqP//.
      by move=> _ /base_and_ko_succes.
    move=> []//.
  Qed.
End valid_state.
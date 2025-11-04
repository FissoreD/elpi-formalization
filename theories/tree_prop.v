From mathcomp Require Import all_ssreflect.
From det Require Import tree.
From det Require Import zify_ssreflect.

Section RunP.
  Variable u: Unif.


  (********************************************************************)
  (* EXPAND PROPERTIES                                                *)
  (********************************************************************)

  Lemma is_ko_expand {A s1}: is_ko A -> expand u s1 A = Failure A.
  Proof.
    elim: A s1 => //.
    - move=> A HA s B HB s1 /=.
      case: ifP=> //dA/andP[kA kB].
        rewrite HB//.
      rewrite HA//.
    - move=> A HA B0 _ B HB s1 /= kA.
      rewrite HA//.
  Qed.

  Lemma is_dead_big_and {p r}: is_dead (big_and p r) = false.
  Proof. elim: r p => //=-[]//. Qed.

  Lemma is_dead_big_or {p r rs}: is_dead (big_or_aux p r rs) = false.
  Proof. 
    elim: rs r p => //=.
    - move=> *; apply: is_dead_big_and.
    - move=> [s r] l/= H rs p; rewrite H andbF//.
  Qed. 

  Lemma is_dead_expand {s A}: 
    is_dead A -> expand u s A = Failure A.
  Proof. move=>/is_dead_is_ko/is_ko_expand//. Qed.

  (* Lemma is_ko_expanded s {A}: 
    is_ko A -> dead_run s A (Failed A) 0.
  Proof. move=> dA; apply: expanded_fail (is_ko_expand _) => //. Qed.

  Lemma is_dead_expanded s {A}: 
    is_dead A -> expandedb s A (Failed A) 0.
  Proof. move=>/is_dead_is_ko/is_ko_expanded//. Qed. *)

  Lemma succes_is_solved s {A}: success A -> expand u s A = Success A.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
      case:ifP => //= H sA.
        rewrite HB//=.
      rewrite HA//.
    + move=> A HA B0 HB0 B HB s /=.
      move=>/andP[sA sB].
      rewrite HA//HB//.
  Qed.

  Lemma expand_solved_same {s1 A B}: 
    expand u s1 A = Success B -> (((A = B)) * (success B))%type.
  Proof.
    elim: A s1 B => //.
    + move=> /= ?? [] <-//.
    + move=> A HA s B HB s1 C/=.
      case: ifP => dA/=.
        case X: expand =>//-[?];subst => /=.
        rewrite dA !(HB _ _ X)//.
      case X: expand => //=-[?]; subst => /=.
      have {}HA := HA _ _ X.
      rewrite success_is_dead !HA//.
    + move=> A HA B0 _ B HB s1 C /=.
      case X: expand => // [A'].
      case Y: expand => //=[B'][?]; subst.
      have {}HA := HA _ _ X.
      have {}HB := HB _ _ Y.
      rewrite /= !HA !HB//.
  Qed.

  Lemma expand_not_dead {s A r}: 
    is_dead A = false -> expand u s A = r -> is_dead (get_tree r) = false.
  Proof.
    move=> + <-.
    elim: A s; clear; try by move=> //=.
    - move=> p t s/= _; apply dead_big_or.
    + move=> A HA s B HB s1 => //=.
      case: ifP => dA/=.
        rewrite get_tree_Or/=dA; apply: HB.
      move=> _.
      have:= HA s1 dA.
      case X: expand => //=->//.
    + move=> A HA B0 _ B HB s1 //= dA.
      have:= HA s1 dA.
      case X: expand => [|||A']//=dA'.
      rewrite get_tree_And/= fun_if dA'.
      case Y: expand => //[C]/=.
      have [?]:= expand_solved_same X; subst.
      rewrite -success_cut.
      apply: success_is_dead.
  Qed.

  Lemma expand_failed_same {s1 A B}: 
    expand u s1 A = Failure B -> ((A = B) * failed B)%type.
  Proof.
    elim: A s1 B => //.
    + move=> s1 B[<-]//.
    + move=> s1 B[<-]//.
    + move=> A HA s B HB s1 C/=.
      case: ifP => dA/=.
        case X: expand =>//-[?];subst => /=.
        rewrite !(HB _ _ X)//dA//.
      case X: expand => //=-[?]; subst => /=.
      rewrite !(HA _ _ X)// (expand_not_dead dA X)//.
    + move=> A HA B0 _ B HB s1 C /=.
      case X: expand => // [A'|A'].
        move=> [<-]; rewrite /= !(HA _ _ X)//.
      case Y: expand => //=[B'][<-].
      rewrite (expand_solved_same X)//=!(HB _ _ Y)(expand_solved_same X) orbT//.
  Qed.

  (* Lemma expanded_Done_success {s1 A s2 B b1}: 
    expandedb s1 A (Done s2 B) b1 -> success B.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    move=> s s' A B /expand_solved_same H ??; rewrite !H => -[_<-]; rewrite H//.
  Qed. *)

  Lemma is_ko_next_alt {A} b: is_ko A -> next_alt b A = None.
  Proof.
    elim: A b => //.
      move=> A HA s1 B HB b /= /andP[kA kB].
      rewrite HA//!HB// !if_same//.
    move=> A HA B0 _ B HB /= b kA.
    rewrite is_ko_failed//HA// if_same//.
  Qed.

  Lemma next_alt_cutr {A b}:
    next_alt b (cutr A) = None.
  Proof. apply: is_ko_next_alt is_ko_cutr. Qed.

  Lemma next_alt_cutl_success {A}:
    success A -> next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB.
      case: ifP => [dA sB|dA sA]/=.
        rewrite dA HB//.
      rewrite is_dead_cutl dA HA// next_alt_cutr if_same//.
    - move=> A HA B0 HB0 B HB /andP[sA sB].
      rewrite sA/= is_dead_cutl success_cut sA HA// HB//.
      rewrite success_is_dead//.
      rewrite failed_success_cut success_cut sA//.
  Qed.

  Lemma next_alt_cutl_failed {A b}:
    failed (cutl A) -> next_alt b (cutl A) = None.
  Proof.
    elim: A b => //=.
    - move=> A HA s B HB b.
      case: ifP => dA /=; rewrite?is_dead_cutl dA => Hf.
        rewrite HB//.
      rewrite HA// next_alt_cutr if_same//.
    - move=> A HA B0 _ B HB b.
      case: ifP => sA/=.
        rewrite failed_success_cut success_cut sA/= is_dead_cutl success_is_dead//.
        move=> fB.
        rewrite HB//=next_alt_cutl_success//.
      by rewrite !next_alt_cutr success_cutr failed_cutr if_same.
  Qed.

  Lemma next_alt_cutl_failedF {A b}:
    failed A -> next_alt b (cutl A) = None.
  Proof. move=> /failed_cut /next_alt_cutl_failed//. Qed.

  Lemma next_alt_cutl {A}:
    next_alt true (cutl A) = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => /= dA.
        rewrite dA HB//.
      rewrite is_dead_cutl dA HA next_alt_cutr if_same//.
    - move=> A HA B0 _ B HB; case: ifP => //sA/=.
        rewrite failed_success_cut success_cut sA/=.
        rewrite HB HA if_same//.
      rewrite !next_alt_cutr success_cutr failed_cutr if_same//.
  Qed.

  Lemma expand_not_solved_not_success {s1 A r}:
    expand u s1 A = r -> ~ (is_solved r) -> success A = false.
  Proof.
    case: r=> //[s|s|]/=; case X: success => //; try by rewrite // (succes_is_solved s1 X).
  Qed.

  (* Lemma expand_cb_same_subst {A B s1 s2}:
    expand u s1 A = CutBrothers B -> s2 = get_substS s1 A.
  Proof.
    elim: A B s1 s2 => //=.
    - move=> B s1 s2 []//.
    - move=> A HA s B HB C s1 s2; case: ifP => dA; case: expand u => //.
    - move=> A HA B0 _ B HB C s1 s2.
      case e: expand u => //[s' A'|s' A'].
        move=>[??]; subst.
        rewrite (HA _ _ _ e) (expand_not_solved_not_success e)//.
      have [[??] SA] := expand_solved_same e; subst.
      rewrite SA.
      case e1: expand u => //=[s3 B'][<-] _.
      apply: HB e1.
  Qed. *)

  Lemma expand_solved_cutl {s1 A B}: expand u s1 A = Success B -> cutl A = cutl B.
  Proof. move=> /expand_solved_same->//. Qed.

  Lemma failed_expand {s1 A}:
    failed A -> expand u s1 A = Failure A.
  Proof.
    elim: A s1; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2/=.
      case: ifP => [dA fB|dA fA].
        rewrite HB//.
      rewrite HA//.
    + move=> A HA B0 _ B HB s/=.
      case X: failed => /=.
        move=>_; rewrite HA => //.
      move=>/andP[sA fB].
      rewrite succes_is_solved//.
      rewrite HB//.
  Qed. 

  Lemma expand_not_failed {s1 A r}:
    expand u s1 A = r -> ~ (is_fail r) -> failed A = false.
  Proof.
    move=><-; clear r.
    elim: A s1; try by move=> // s1 <-//=.
    - move=> A HA s B HB s1/=.
      case: ifP => dA.
        by have:= HB s; case X: expand.
      by have:= HA s1; case X: expand.
    - move=> A HA B0 _ B HB s1/=.
      have:= HA s1.
      case X: expand => //= [||C] ->; try by rewrite?(expand_not_solved_not_success X)//.
      rewrite (expand_solved_same X)/=.
      have:= HB (get_substS s1 C).
      case Y: expand => //= ->//=; rewrite andbF//.
  Qed.

  Lemma expand_not_failed_Expanded {s1 A B}:
    (* This is wrong: if A is a call and there is no impl, then B = Bot which is failed *)
    expand u s1 A = Expanded B -> failed B = false.
  Proof.
  Abort.

  (********************************************************************)
  (* NEXT_ALT OP PROPERTIES                                           *)
  (********************************************************************)

  Lemma next_alt_success_diff {A B}: 
    success A -> next_alt true A = Some B -> (A != B).
  Proof.
    elim: A B => //=.
    - move=> A HA s B HB C; case: ifP => [dA sB|dA sA].
        case X: next_alt => //[B'][<-]/=.
        have:= HB _ sB X.
        repeat case: eqP => //; try congruence.
      case X: next_alt => //[A'|].
        move=> [<-].
        have:= HA _ sA X.
        repeat case: eqP => //; try congruence.
      case: ifP => //dB.
      case Y: next_alt => //[B'].
      move=> [<-]/=.
      case: eqP => //-[H ?]; subst.
      by move: dA; rewrite H is_dead_dead.
    - move=> A HA B0 _ B HB C /andP[sA sB].
      case: ifP => // dA.
      rewrite success_failed sA//.
      case X: next_alt => [B'|]//.
        move=> [<-].
        have:= HB _ sB X.
        repeat case: eqP => //; try congruence.
      case Y: next_alt => [A'|]//.
      case Z: next_alt => [B0'|]//[<-].
      have:= HA _ sA Y.
      repeat case: eqP => //; try congruence.
  Qed.

  Lemma next_alt_failed_diff {A B}: 
    failed A -> next_alt false A = Some B -> (A != B).
  Proof.
    elim: A B => //=.
    - move=> A HA s B HB C; case: ifP => [dA fB|dA fA].
        case X: next_alt => //[B'][<-]/=.
        have:= HB _ fB X.
        repeat case: eqP => //; try congruence.
      case X: next_alt => //[A'|].
        move=> [<-].
        have:= HA _ fA X.
        repeat case: eqP => //; try congruence.
      case: ifP => //dB.
      case Y: next_alt => //[B'].
      move=> [<-]/=.
      case: eqP => //-[H ?]; subst.
      by move: dA; rewrite H is_dead_dead.
    - move=> A HA B0 _ B HB C.
      case: ifP => // dA.
      move=> /orP[fA|/andP[sA fB]].
        rewrite fA.
        case X: next_alt => [A'|]//.
        case Y: next_alt => [B0'|]//[<-]/=.
        have:= HA _ fA X.
        repeat case: eqP => //; try congruence.
      rewrite success_failed//sA.
      case X: next_alt => [B'|]//.
        move=>[<-].
        have:= HB _ fB X.
        repeat case: eqP => //; try congruence.
      case Y: next_alt => [A'|]//.
      case Z: next_alt => [B0'|]//[<-]/=.
      have:= next_alt_success_diff sA Y.
      repeat case: eqP => //; try congruence.
    Qed.

  Lemma is_dead_next_alt {A} b: is_dead A -> next_alt b A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed.

  Lemma next_alt_dead {A D b}: 
    next_alt b A = Some (D) -> ((is_dead A = false) * (is_dead D = false))%type.
  Proof.
    elim: A D b => //=.
    - move=> D []//[<-]//.
    - move=>/= p c d _ []// <-//.
    - move=> D _ [<-]//.
    - move=> A HA s B HB C b/=.
      case: ifP => dA.
        case X: next_alt => //[D][<-]/=; rewrite dA/=.
        rewrite !(HB _ _ X)//.
      case X: next_alt => //= [D|].
        move=>[<-]; split => //=; rewrite ((HA _ _ X))//.
      case: ifP => dB//.
        case Y: next_alt => //[D] [<-]/=.
        rewrite is_dead_dead ((HB _ _ Y))//.
    move=> A HA B0 _ B HB C b /=.
    case: ifP => dA//.
    case: ifP => fA.
      case X: next_alt => //[A0].
      case Y: next_alt => //[B0'].
      move=> [<-]/=; rewrite (HA _ _ X)//.
    case: ifP => sA/=; last first.
      move=>[<-]//.
    case X: next_alt => [B'|].
      move=> [<-]/=; rewrite dA//.
    case Y: next_alt => //=[A'].
    case W: next_alt => //[B0'] [<-]/=.
    rewrite (HA _ _ Y)//.
  Qed.

  Lemma next_alt_failed {b A r}: next_alt b A = r -> failed (odflt OK r) = false.
  Proof.
    move=><-; elim: A b {r} => //=.
    - move=> []//.
    - move=> A HA s B HB b.
      case: ifP => //=dA.
        by have := HB b; case : next_alt; rewrite //= dA//.
      have:= HA b; case X: next_alt => //=[A'|].
        rewrite (next_alt_dead X)//.
      case: ifP => //dB.
      by have {HB} := HB false; case: next_alt; rewrite//=is_dead_dead//.
    - move=> A HA B0 HB0 B HB b.
      case: ifP => // dA; case: ifP => fA.
        have:= HA false; case: next_alt => //=A'.
        have:= HB0 false; by case Y: next_alt => //=[B0'] ->->; rewrite andbF.
      case: ifP => sA/=; last first.
        rewrite fA sA//.
      have:= HB b.
      case X: next_alt => //=[B'|].
        by move=> ->; rewrite success_failed// andbF.
      have:= HA true; case: next_alt => //=A'.
      have:= HB0 false; by case Y: next_alt => //=[B0'] ->->; rewrite andbF.
  Qed.

  Lemma failed_big_or p s t: failed (big_or u p s t).
  Proof. rewrite/big_or; case: F => //-[]//. Qed.

  Section same_structure.

    Fixpoint same_structure A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => [&& same_structure B0 B0', same_structure A1 A' & same_structure B1 B']
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
      by move=> ?->? ->?->.
    Qed.

    Lemma same_structure_trans: transitive same_structure.
    Proof.
      move=> + A; elim: A => //.
      - move=> A HA s B HB []//A' s' B'[]//A2 s2 B2/=.
        move=>/and3P[/eqP<-HA' HB']/and3P[/eqP<-HA2 HB2].
        rewrite eqxx (HA A' A2)//(HB B' B2)//.
      - move=> A HA B0 HB0 B HB[]//A1 B01 B1[]//A2 B02 B2/=.
        move=>/and3P[HA1 HB01 HB1]/and3P[HA2 HB02 HB2].
        rewrite (HA A1 A2)//(HB B1 B2)//(HB0 B01 B02)//.
    Qed.

    Lemma same_structure_cutr {A B}: same_structure A B -> same_structure A (cutr B).
    Proof. 
      elim: A B => //=.
        by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=/and3P[/HB0-> /HA-> /HB->]//.
    Qed.
    
    Lemma same_structure_cut {A B}: same_structure A B -> same_structure A (cutl B).
    Proof. 
      elim: A B => //=.
        move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<- H2 H3].
        case: ifP => //.
          by rewrite H2 HB//eqxx.
        by rewrite eqxx HA// same_structure_cutr//.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=. 
      move=> /and3P[sB0 sA sB].
      case: ifP => //=sA'; rewrite !same_structure_cutr//=.
      rewrite HA//HB//.
    Qed.
    
    Lemma same_structure_dead {B}: same_structure B (dead1 B).
    Proof. 
      elim: B => //=.
        move=> A HA s B HB; rewrite eqxx HA HB//.
      move=> A HA B0 HB0 B HB; rewrite HA HB0 HB//.
    Qed.

    Lemma expand_same_structure {s A r}: 
      expand u s A = r -> same_structure A (get_tree r).
    Proof.
      move=><-{r}.
      elim: A s => //.
        move=> A HA s B HB s1; subst => /=.
        case: ifP => dA.
          move: (HB s).
          case eB: expand => //=[B'|B'|B'|B']; rewrite eqxx same_structure_id//.
        move: (HA s1).
        case eA: expand => //=[A'|A'|A'|A'] ->; rewrite eqxx ?same_structure_cutr//same_structure_id//.
      move=> A HA B0 HB0 B HB s1; subst => /=.
      have:= (HA s1).
      case eA: expand => //=[A'|A'|A'|A'] {}HA; rewrite ?HA ?same_structure_id//.
      have := (HB (get_substS s1 A')).
      case eB: expand => //=[B'|B'|B'|B'] H; rewrite ?same_structure_cut// ?same_structure_cutr// ?same_structure_id// ?HA//.
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
      - move=> ???; case: ifP => _.
          case: next_alt => //[?][<-]//.
        case next_alt => //[?[<-]|]//; case: ifP => _//.
        case: next_alt => //?[<-]//.
      - move=> ???; case: ifP => // _; case: ifP => _.
          do 2 case: next_alt => // ?.
          move=> [<-]//.
        case: ifP => //[_|_[<-]]//; case: next_alt => //[?[<-]|]//.
        (do 2 case: next_alt => //?).
        move=> [<-]//.
    Qed.

    Lemma same_structure_sup2_trans {A B C}:
      same_structure A B -> same_structure_sup B C -> same_structure_sup A C.
    Proof. by destruct A, B => //; destruct C => //=; do 2 case: eqP => ?//; subst. Qed.

    Lemma same_structure_sup_trans:
      transitive same_structure_sup.
    Proof. move=> B A C; by destruct A, B => //; destruct C => //=; do 2 case: eqP => ?//; subst. Qed.

    Lemma same_structure_sup_dead {A}:
      same_structure_sup A (dead1 A).
    Proof. case: A => //=. Qed.

    Lemma runb_same_structure {s A s1 r n}:
      runb u s A s1 r n -> same_structure_sup A r.
    Proof.
      elim; clear => //.
      - move=> s1 s2 A B sA _ <-/=.
        case X: next_alt => [B'|]/=; subst; move: X.
          move=> /next_alt_same_structure//.
        move=> _.
        apply: same_structure_sup_dead.
      - move=> s1 s2 r A B n /expand_same_structure/= + _.
        apply: same_structure_sup2_trans.
      - move=> s1 s2 r A B n /expand_same_structure/= + _.
        apply: same_structure_sup2_trans.
      - move=> s1 s2 A B oB r n.
          move=> /next_alt_same_structure + _.
          apply: same_structure_sup_trans.
      - move=> *; apply: same_structure_sup_dead.
    Qed.

    Lemma run_dead1 {s1 B s2 r n}:  
      is_dead B -> runb u s1 B s2 r n -> (s2 = None /\ r = dead1 B /\ n = 0)%type2.
    Proof.
      move=> dB H; inversion H; clear H; subst;
        try rewrite // is_dead_expand//is_dead_dead in H0.
        by rewrite success_is_dead in dB.
      rewrite is_dead_next_alt// in H1.
    Qed.

    Lemma run_dead2 {s1 B s2 r n}:  
      runb u s1 (dead1 B) s2 r n -> (s2 = None /\ r = dead1 B /\ n = 0)%type2.
    Proof. move=> /(run_dead1 is_dead_dead)//; rewrite dead2//. Qed.

  End same_structure.

  Lemma ges_subst_cutl {s A} : 
    success A -> get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//; auto.
    - move=> A HA B0 _ B HB s /andP[sA sB]; rewrite sA/=success_cut sA HA// HB//.
  Qed.

  Definition choose_cutl b1 A := (if (b1 == 0) then A else cutl A).
  
  Lemma choose_cutl_id {A}: choose_cutl 0 A = A.
  Proof. rewrite/choose_cutl eqxx//. Qed.

  Lemma choose_cutl_cutl {b2 A}: choose_cutl b2 (cutl A) = (cutl A).
  Proof. rewrite/choose_cutl cutl2 if_same//. Qed.

  Lemma choose_cutl_lt {b2 A}: 0 < b2 -> choose_cutl b2 A = cutl A.
  Proof. rewrite/choose_cutl; case: eqP => //; lia. Qed.

  Lemma expand_cutl_cb {s C B}: expand u s (cutl C) = CutBrothers B -> False.
  Proof.
    elim: C s B=> //=.
    - move=> A HA s B HB s1 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA; case expand => //.
    - move=> A HA B0 _ B HB s1 C.
      case:ifP => sA//=.
        case X: expand => //=[A'|A'].
          by have:= HA _ _ X.
        case e: expand => //[ A''].
        by have:= HB _ _ e.
      rewrite is_ko_expand//is_ko_cutr//.
  Qed.

  Lemma expand_cutl_exp {s C B}: expand u s (cutl C) = Expanded B -> False.
  Proof.
    elim: C s B=> //=.
    - move=> A HA s B HB s1 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA.
        case X: expand => //=.
          by have:= HB _ _ X.
        by have:= expand_cutl_cb X.
      case X: expand => //.
        by have:= HA _ _ X.
      by have:= expand_cutl_cb X.
    - move=> A HA B0 _ B HB s1 C.
      case:ifP => sA/=.
        case e: expand => //[A'|A'].
          by have:= HA _ _ e.
        case X: expand => //[B'].
        by have:= HB _ _ X.
      rewrite is_ko_expand//is_ko_cutr//.
  Qed.
End RunP.
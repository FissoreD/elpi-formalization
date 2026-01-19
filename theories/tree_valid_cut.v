From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.
From det Require Import finmap.

Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition disj_tree T1 T2 := (vars_tree T1) `&` (vars_tree T2) == fset0.


Section valid_tree.
  Variable u : Unif.

  (* We do not consider Bot and Dead as Cut,
     since we want to define a valid state where if in a state like
     A /\_R B, B has a cut, then R should either have a cut or be ko
  *)
  Fixpoint has_cut A :=
    match A with
    | CutS => true
    | OK | CallS _ _ | Bot | Dead => false
    | And A B0 B => [||has_cut A | (has (fun x => x == ACut) B0.2 && has_cut B)]
    | Or _ _ _ => false
    end.
  
  Fixpoint base_and s :=
    match s with
    | And (CallS _ _ | CutS) r r1 => (r == r1) && base_and r1 (* should also say something about the program *)
    | OK => true
    | _ => false
    end.

  Lemma base_and_dead {A}: base_and A -> is_dead A = false.
  Proof. case: A => // -[]//=. Qed.

  Lemma base_and_big_and {pr A}: base_and (big_and pr A).
  Proof. by elim: A => // -[|t] l /= ->; rewrite eq_refl. Qed.

  Fixpoint base_or_aux s :=
    match s with
    | Or l _ r => 
      (*todo: should also say something about the substitution and the program? *)
      [&& (*disj_tree l r,*) base_and l & (base_or_aux r)] 
      (* [&& base_and l & (base_or_aux r)] todo: should also say something about the substitution and the program? *)
    | t => base_and t
    end.

  Fixpoint base_and_ko s :=
    match s with
    | And Bot r r1 => [&&base_and_ko r, (r == r1) & base_and_ko r1] (* should also say something about the program *)
    | Bot => true
    | _ => false
    end.

  Definition base_or s := 
    match s with 
    | Bot => true
    | Or Bot _ t => base_or_aux t
    | _ => false
    end.

  Fixpoint base_or_aux_ko s :=
    match s with
    | Or l _ r => base_and_ko l && (base_or_aux_ko r) (* todo: should also say something about the substitution and the program? *)
    | t => base_and_ko t
    end.

  Definition bbOr B := base_or_aux B || base_or_aux_ko B. 
  Definition bbAnd B := base_and B||base_and_ko B. 

  Definition check_cut B B0:=  
    (if has_cut B then is_ko B0 || has_cut B0 else has_cut B0 == false).

  Lemma check_cut_refl A: check_cut A A.
  Proof. rewrite/check_cut; case: ifP => ->; rewrite ?orbT//. Qed.

  Fixpoint resetR' B0 B :=
    match B0, B with
    | OK, OK => true
    | And L1 _ R1, And L2 _ R2 =>
      if L1 == L2 then R1 == R2
      else disj_tree L1 L2 && resetR' R1 R2
    | _, _ => false
    end.

  Definition resetR B0 B := (is_ko B0 || resetR' B0 B).

  Fixpoint valid_tree s :=
    match s with
    | CutS | CallS _ _ | OK | Bot => true
    | Dead => false
    | Or A _ B =>
      (* disj_tree A B && *)
      if is_dead A then valid_tree B
      else valid_tree A && (bbOr B)
    | And A B0 B => 
      [&& valid_tree A,
        if success A then (valid_tree B (*&& resetR B0 B*))
        else (B0 == B),
        (if success A || failed A then bbAnd B0 else base_and B0)
        & check_cut B B0]
    end.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/= /andP[sA sB].
    by rewrite HA//HB//=andbF.
  Qed.

  Goal forall x r, (valid_tree (And CutS x r)) -> is_ko r = false.
  Proof.
    move=> x r/= /andP[] /eqP->.
    elim: r => //-[]//.
  Qed.


  Lemma is_dead_valid_tree {A} : is_dead A -> valid_tree A = false.
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[]dA dB.
      rewrite HA// dA HB//andbF//.
    move=> A HA Bo ? B HB/=dA.
    rewrite HA// andbF//.
  Qed.

  Lemma valid_tree_is_dead {A} : valid_tree A -> is_dead A = false.
  Proof. apply: contraPF => /is_dead_valid_tree->//. Qed.

  Lemma base_and_valid {A} : base_and A -> valid_tree A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //=.
      move=> p a _ + A + /andP [] /eqP H ; rewrite H; subst.
      by by move=> _ H H1; rewrite H1//eqxx//check_cut_refl.
    by move=> _ H _ _ /andP[/eqP<-] H1; rewrite H1//eqxx//check_cut_refl.
  Qed.

  Lemma valid_tree_big_and {pr l} : valid_tree (big_and pr l).
  Proof. apply: base_and_valid base_and_big_and. Qed.

  Lemma bbAnd_valid {A} : bbAnd A -> valid_tree A.
  Proof.
    move=>/orP[].
      apply: base_and_valid.
    elim: A=> //.
    move=> []// _ B0 HB0 B HB/=/and3P[H/eqP->]bB.
    by rewrite eqxx /bbAnd bB orbT//check_cut_refl.
  Qed.

  Lemma big_or_aux_not_bot {pr l rs}: big_or_aux pr l rs != Bot.
  Proof. case: rs => [|[] xs]//=; case: l => //. Qed.

  Lemma vars_big_and pr r1:
    vars_tree (big_and pr r1) = varsU (map vars_atom r1).
  Proof.
    elim: r1 => //= x xs IH; rewrite IH//.
    rewrite -fsetUA fsetUid.
    destruct x => //.
  Qed.

  Lemma vars_big_or_aux pr r rs:
    vars_tree (big_or_aux pr r rs) = 
      varsU (map vars_atom r) `|` varsU [seq varsU_rprem x.2 | x <- rs].
  Proof. by elim: rs r => //=[|[s r] rs IH] r1/=; rewrite vars_big_and ?fsetU0// IH. Qed.

  Lemma bbOr_big_or_aux {pr s l}:
    varsD (varsU (map vars_atom s) :: ((map (fun x => varsU_rprem x.2) l))) ->
    bbOr (big_or_aux pr s l).
  Proof.
    rewrite/bbOr => /=/andP[].
    case: base_or_aux_ko; rewrite ?orbT//orbF/=.
    elim: l s => //=; clear.
    + move=> []//a l; rewrite /base_or_aux //= base_and_big_and eqxx//.
      case: a => //.
    + move=> [s r] rs IH r1 /=.
      rewrite !fsetIUr !fsetU_eq0.
      move=> /andP[H1 H2] /andP[H4 H5].
      rewrite base_and_big_and/= IH//=.
      (* rewrite/disj_tree.
      rewrite vars_big_and vars_big_or_aux.
      by rewrite !fsetIUr !fsetU_eq0 H1 H2. *)
  Qed.

  Definition is_base s := match s with 
    | Bot | Dead | OK | CutS => true 
    | Or _ _ _ | And _ _ _ | CallS _ _ => false
    end.

  Lemma disj_tree_baseL b r: is_base b -> disj_tree b r.
  Proof. by destruct b; rewrite ///disj_tree/= fset0I. Qed.

  Hint Resolve disj_tree_baseL : core.

  Lemma disj_tree_commE A B: disj_tree A B = disj_tree B A.
  Proof. by rewrite/disj_tree fsetIC. Qed.

  Lemma disj_tree_comm A B: disj_tree A B -> disj_tree B A.
  Proof. by rewrite disj_tree_commE. Qed.

  Lemma disj_tree_AndE A B C D:
    disj_tree (And A B C) D = disj_tree A D && disj_tree B D && disj_tree C D.
  Proof. by rewrite/disj_tree /= !fsetIUl !fsetU_eq0. Qed.

  Lemma disj_tree_And A B C D:
    [/\ disj_tree A D, disj_tree B D & disj_tree C D] <-> disj_tree (And A B C) D.
  Proof. by rewrite disj_tree_AndE; split => [[]|/andP[/andP[]]]->->->. Qed.

  Lemma disj_tree_OrE A s B C:
    disj_tree (Or A s B) C = disj_tree A C && disj_tree B C.
  Proof. by rewrite/disj_tree /= !fsetIUl !fsetU_eq0. Qed.

  Lemma disj_tree_Or A s B C:
    (disj_tree A C /\ disj_tree B C) <-> disj_tree (Or A s B) C.
  Proof. rewrite disj_tree_OrE//; split => [[]|/andP[]]->->//. Qed.

  Lemma disj_tree_cutrL A C: disj_tree (cutr A) C.
  Proof.
    elim: A => /=; only 1-5: by rewrite disj_tree_baseL.
      by move=> A HA s B HB; apply/disj_tree_Or; rewrite HA HB.
    by move=> A HA B0 HB0 B HB; apply/ disj_tree_And; rewrite HA HB HB0.
  Qed.

  Lemma disj_tree_cutrR A C: disj_tree C (cutr A).
  Proof. apply: disj_tree_comm (disj_tree_cutrL _ _). Qed.

  Lemma disj_tree_cutlL A C: disj_tree A C -> disj_tree (cutl A) C.
  Proof.
    elim: A => //=; first by rewrite disj_tree_baseL.
      move=> A HA s B HB /disj_tree_Or[dAC dBC];
      case: ifP => dA; apply/disj_tree_Or; split; auto;
      apply: disj_tree_cutrL.
    move=> A HA B0 HB0 B HB/disj_tree_And[dA dB0 dB];
    case: ifP => _; apply/disj_tree_And; split; auto;
    apply: disj_tree_cutrL.
  Qed.

  Lemma disj_tree_cutlR A C: disj_tree A C -> disj_tree A (cutl C).
  Proof. by move=> H; apply/disj_tree_comm/disj_tree_cutlL/disj_tree_comm. Qed.

  Lemma disj_tree_deadL A C: disj_tree (dead A) C.
  Proof.
    elim: A => /=; only 1-5: by rewrite disj_tree_baseL.
      move=> A HA s B HB; apply/ disj_tree_Or; split; auto.
    by move=> A HA B0 HB0 B HB; apply/ disj_tree_And; split.
  Qed.

  Lemma valid_tree_big_or {pr s t} : valid_tree (big_or u pr s t).
  Proof.
    rewrite /big_or//=.
    case: t => [k|v|c t]; case H: F => // [[s1 r] rs]; 
    rewrite /=!(bbOr_big_or_aux,disj_tree_baseL)//;
    apply: backchain_fresh_premE H.
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_tree B.
  Proof.
    elim: B => //.
    move=> []// HA B0 _ B HB/= /and3P[bB0 /eqP <-] H.
    by rewrite eqxx /bbAnd H orbT check_cut_refl.
  Qed.

  Lemma base_and_base_or_aux {A}: base_and A -> base_or_aux A.
  Proof. case: A => //. Qed.

  Lemma base_and_ko_base_or_aux_ko {A}: base_and_ko A -> base_or_aux_ko A.
  Proof. case: A => //. Qed.

  Lemma base_and_ko_disj A C:
    base_and_ko A -> disj_tree A C.
  Proof.
    elim: A => //; first by rewrite disj_tree_baseL//.
    move=> []// _ _ _ B HB/= /and3P[_ /eqP->] => /HB{}HB.
    apply/disj_tree_And; split => //; rewrite disj_tree_baseL//.
  Qed.    

  Lemma bbOr_valid {B}:
    bbOr B -> valid_tree B.
  Proof. 
    move=> /orP [].
    elim B => //; clear.
    + move=> A HA s B HB/=/andP[bA bB].
      rewrite HA ?base_and_base_or_aux// /bbOr bB HB// if_same//.
    + by move=> s; case: s => //[p t|] Ha B0 HB0 B HB /=/andP[/eqP->]bB; rewrite eqxx bB//check_cut_refl.
    elim: B => //.
    + move=> A HA s B HB /= /andP [bA bB].
      rewrite HB//HA?base_and_ko_base_or_aux_ko// /bbOr bB orbT if_same//base_and_ko_disj//.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      by rewrite /bbAnd bB0 eqxx // orbT//check_cut_refl.
  Qed.

  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //=[_ _|] _ HB HC /andP [] /eqP <-bB; rewrite HB//eqxx//.
  Qed.

  Lemma base_and_ko_base_and_ko_cutr {B} : base_and_ko B -> (cutr B) = B.
  Proof. 
    elim: B => // -[]//_ A HA B HB/=/and3P[bA/eqP->bB].
    rewrite HB//eqxx//.
  Qed.

  Lemma base_and_base_and_ko_cutr {B} : base_and B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //=[_ _|] _ HB HC /andP [] /eqP <- hB; rewrite eqxx HB//.
  Qed.
  
  Lemma base_or_base_or_ko_cutr {B}: base_or_aux B -> base_or_aux_ko (cutr B).
  Proof.
    elim: B => //.
    + move=> A IHA s B IHB /= /andP[] /base_and_base_and_ko_cutr -> /IHB ->//.
    + move=> a; case: a => //=[_ _|] _ B HB C HC /andP [] /eqP /[subst1] hC;
      rewrite base_and_base_and_ko_cutr//eqxx//.
  Qed.

  Lemma base_or_ko_cutr {B}: base_or_aux_ko B -> (cutr B) = B.
  Proof.
    elim: B => //.
      move=> A HA s B HB /= /andP[bA bB].
      by rewrite HB//=base_and_ko_base_and_ko_cutr.
    move=> [] //= _ B0 _ B HB /and3P[] bB0 /eqP<- _.
    by rewrite base_and_ko_base_and_ko_cutr//.
  Qed.

  (* Lemma valid_tree_compose_and {A2 B2 B02}: 
    (if success A2 then valid_tree B2 else ((B02 == B2))) ->
      bbAnd B02 ->
        valid_tree B2.
  Proof. case: success => //; move=>/eqP->. apply: bbAnd_valid. Qed. *)

  Lemma base_and_cutl {B0}:
    base_and B0-> (B0 == OK) || base_and_ko (cutl B0).
  Proof.
    elim: B0 => //= s; case: s => //= [_ _|] _ _ _ B HB /andP[/eqP->] bB;
    rewrite eqxx !base_and_base_and_ko_cutr//.
  Qed.

  Lemma base_ko_and_cutl {B0}:
    base_and_ko B0-> base_and_ko (cutl B0).
  Proof.
    elim: B0; move=> //=[]//= _ _ _ B HB /and3P[_ /eqP->].
    by move=> H; rewrite base_and_ko_base_and_ko_cutr//H eqxx.
  Qed.

  Lemma bbAnd_cutl{B0}:
    bbAnd B0 -> (B0 == OK) || base_and_ko (cutl B0).
  Proof. move=> /orP[/base_and_cutl|/base_ko_and_cutl]//->; rewrite orbT//. Qed.

  Lemma bbOr_cutr {B}: bbOr B -> bbOr (cutr B).
  Proof.
    rewrite/bbOr.
    move=> /orP[|]H; last by rewrite base_or_ko_cutr// H orbT.
    by rewrite base_or_base_or_ko_cutr//orbT.
  Qed.

  Lemma bbAnd_cutr {A}: bbAnd A -> bbAnd (cutr A).
  Proof.
    rewrite /bbAnd => /orP[].
      move=>/base_and_base_and_ko_cut-->; apply orbT.
    move=> /[dup]/base_and_ko_base_and_ko_cutr->->; apply orbT.
  Qed.

  Lemma has_cut_cutr A: has_cut (cutr A) = false.
  Proof. elim: A => //=A -> B0 -> B ->//=. Qed.

  Lemma check_cut_cutrR A B: check_cut A (cutr B).
  Proof. by rewrite/check_cut is_ko_cutr has_cut_cutr if_same. Qed.

  Lemma has_cut_dead A: has_cut (dead A) = false.
  Proof. by elim: A => //=A -> B0 -> B ->. Qed.

  (* Lemma valid_tree_cutr {A}: valid_tree A -> valid_tree (cutr A).
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      rewrite is_dead_cutr disj_tree_cutrL.
      case: ifP => [dA /andP[dAB vA]|dA/and3P[dAB vA bB]]//;
      by rewrite !(HA, HB, bbOr_cutr)//.
    - move=> A HA B0 HB0 B HB/=/and4P[vA ++ C]; rewrite check_cut_cutrR/=.
      case: ifP => /=[sA vB bB| sA /eqP -> bB];
      rewrite !(HA, success_cutr, failed_cutr, bac)//=.
      rewrite?has_cut_cutr//=HA//HB//. 
        (* ?bbOr_valid// iscuc. *)
      (* rewrite HA//HB//bbAnd_cutr// success_cutr failed_cutr/=andbT. *)
  Abort. *)

  Lemma resetR_cutrR B0 B: resetR (cutr B0) B.
  Proof. rewrite/resetR is_ko_cutr//. Qed.

  Lemma valid_tree_cut {A}: success A -> valid_tree A -> valid_tree (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB => /=.
      case: ifP => //[dA sB vB| dA sA /andP[vA bB]]/=;
      rewrite !(dA, HB, HA,is_dead_cutl,bbOr_cutr,disj_tree_cutlR,disj_tree_cutrR)//.
    move=> A HA B0 HB0 B HB /= /andP[sA sB] /and4P[vA ++ C].
    rewrite sA/= => vB bB.
    rewrite success_cut sA HA//HB//=bbAnd_cutr// check_cut_cutrR//.
  Qed.

  Lemma base_and_bbAnd {A}: base_and A -> bbAnd A.
  Proof. rewrite/bbAnd=>->//. Qed.

  Lemma step_keep_cut s A r:
    step u s A = r -> ~~(is_cb r) -> has_cut (get_tree r) = has_cut A.
  Proof.
    move=> <-{r}; elim: A s => //=.
    - by move=> p c s; rewrite/big_or; case: F => [|[]]//.
    - move=> A HA s B HB smid.
      case: ifP => deadA; first by rewrite get_tree_Or/=.
      by case eA: step => //=. 
    move=> A HA B0 HB0 B HB s.
    move: (HA s).
    case eA: step => [A'|A'|A'|A']//= /(_ isT) {}HA; cycle-1; [|by rewrite HA..].
    move: (HB (get_substS s A')).
    have [? sA] := step_solved_same _ eA; subst A'.
    by case eB: step => [B'|B'|B'|B']//= /(_ isT) {}HB _; rewrite HB//.
  Qed.

  Lemma check_cut_step A B0 s r:
    step u s A = r -> ~~(is_cb r) -> check_cut (get_tree r) B0 = check_cut A B0.
  Proof. by move=> eA H; rewrite/check_cut (step_keep_cut eA)//. Qed.

  Lemma disj_tree_step s X B l: 
    step u s B = l ->
    disj_tree B X -> disj_tree (get_tree (l)) X.
  Proof.
    move=> <-{l}.
    elim: B s => //=.
    - move=> p c s H; rewrite/big_or.
      case F: F => [|[s1 r] rs]; first by rewrite disj_tree_baseL.
      apply/disj_tree_Or; split; first by apply:disj_tree_baseL.
      move: H.
      rewrite/disj_tree vars_big_or_aux/=.
      move=> /=.
      move=> H.
      (* move:H; rewrite/ditreq   *)

       admit.
    - move=> A HA s B HB s1 /disj_tree_Or[dA dB].
      case:ifP => deadA.
        have:= HB s dB; case step => /= B' {}HB;
        by apply/disj_tree_Or; rewrite dA//.
      have:= HA s1 dA; case: step => /= A' {}HA;
      by apply/disj_tree_Or; split; rewrite//disj_tree_cutrL.
    - move=> A HA B0 HB0 B HB s /disj_tree_And[dA dB0 dB].
      have:= HA s dA; case: step => /= A' {}HA; 
      only 1-3: by (apply/disj_tree_And; split).
      by have:= HB (get_substS s A') dB; case: step => //=B' {}HB;
      apply/disj_tree_And; split; auto; rewrite (disj_tree_cutlL,disj_tree_cutrL).
  Admitted.

  Lemma disj_tree_stepR s X B l: 
    step u s B = l ->
    disj_tree X B -> disj_tree X (get_tree (l)).
  Proof. by move=> /disj_tree_step H /disj_tree_comm/H /disj_tree_comm. Qed.

  Lemma base_and_ko_is_ko {A}: base_and_ko A -> is_ko A.
  Proof. elim: A => //=-[]//. Qed.

  Lemma base_and_failed {A}: base_and A -> failed A = false.
  Proof. elim: A => //=-[]//=p a _ A HA B HB /andP[]//. Qed.

  Lemma base_and_is_ko A: base_and A -> is_ko A = false.
  Proof. move=> bA; rewrite failed_is_ko//base_and_failed//. Qed.

  Lemma resetR_base_and_ko B0 C:
    base_and_ko B0 -> resetR B0 C.
  Proof. by rewrite/resetR; move=> /base_and_ko_is_ko->. Qed.

  Definition is_call A := match A with CallS _ _ => true | _ => false end.

  Lemma base_and_AndP A B0 B: base_and (And A B0 B) <-> 
    [/\ (A = CutS \/ is_call A), (B0 = B) & base_and B].
  Proof.
    split => /=; first by (destruct A => //= /andP[/eqP->->]; split; auto).
    by move=> []; destruct A => -[]// _ ->->//; rewrite eqxx.
  Qed.

  (* Print resetR'. *)

  Lemma resetR'P L1 L2 B B' R1 R2:
    resetR' (And L1 B R1) (And L2 B' R2) <-> 
      if L1 == L2 then R1 == R2 else disj_tree L1 L2 && resetR' R1 R2.
  Proof. move=> //=. Qed.

  Lemma resetR'_refl A: base_and A -> resetR' A A.
  Proof. elim: A => //=-[]//=p c _ ?? B HB /andP[/eqP<-]; rewrite eqxx//. Qed.

  Lemma resetR_refl A: base_and A -> resetR A A.
  Proof. move=> H; rewrite/resetR resetR'_refl//base_and_is_ko//. Qed.

  Lemma step_Exp_CutF s A r:
    step u s A = r -> get_tree r <> CutS.
  Proof.
    move=> <-{r}.
    case: A => //=.
    - move=> p c; rewrite/big_or; case: F => [|[]]//.
    - move=> A sm B; case: ifP; case: step => //.
    - move=> A B0 B; case: step => // A'; case: step => //.
  Qed.

  Lemma step_Exp_CallF s A r:
    step u s A = r -> not (is_call (get_tree r)).
  Proof.
    move=> <-{r}.
    case: A => //=.
    - move=> p c; rewrite/big_or; case: F => [|[]]//.
    - move=> A sm B; case: ifP; case: step => //.
    - move=> A B0 B; case: step => // A'; case: step => //.
  Qed.

  (* Lemma resetR_base_and s B0 B C:
    base_and B0 -> 
    (*valid_tree B ->*) resetR B0 B -> step u s B = C -> resetR B0 (get_tree C).
  Proof.
    rewrite/resetR => HB + <-.
    rewrite base_and_is_ko//=.
    elim: B s B0 HB => //[p c s []|_ []|?????? []|]//.
    move=> A HA B0 HB0 B HB s []// L _ R /base_and_AndP[[]+ -> bR];
    case: L => //.
      move=> _.
      move=> /resetR'P; case:eqP => H; subst.
        move=> /eqP ?; subst => /=.
        by rewrite disj_tree_baseL//resetR'_refl.
      move=> /andP[_]/= H1.
      have:= HA s.
      case eA: step => //=[A'|A'|A'|A'];
      only 1, 2, 3: (move=> {}HA; case: eqP => //?; subst; (try by have:= step_Exp_CutF eA); rewrite disj_tree_baseL//=).
      move=>{}HA.
      have [? sA]:= step_solved_same _ eA; subst.
      have:= HB (get_substS s A') _ bR H1; case eB: step => //=[B'|B'|B'|B']->;
      rewrite disj_tree_baseL//=; case: eqP; auto.
      destruct A' => //=; case: ifP => //.
    move=> p c _ /resetR'P; case: eqP => H.
      move=> /eqP?; subst => /=; case: ifP => //= _.
      rewrite resetR'_refl//andbT disj_tree_callS_big_or//.
    move=> /andP[H1 HR]/=.
    have:= HA s.
    case eA: step => //=[A'|A'|A'|A'];
    only 1, 2, 3: (move=> {}HA; case: eqP => //?; subst; (try by have:= step_Exp_CallF eA); rewrite HR (disj_tree_stepR eA)//).
    move=> {}HA.
    have [? sA]:= step_solved_same _ eA; subst.
    have:= HB (get_substS s A') _ bR HR; case eB: step => //=[B'|B'|B'|B']->;
    case: eqP; auto; rewrite?H1//.
      by destruct A' => //=; case: ifP => //.
    rewrite disj_tree_cutlR//.
  Qed.

  Lemma resetR_step s B0 B C:
    bbAnd B0 -> resetR B0 B -> step u s B = C -> resetR B0 (get_tree C).
  Proof.
    move=> /orP[]; last by move=> + _ => /resetR_base_and_ko ->//.
    apply: resetR_base_and.
  Qed. *)

  Lemma valid_tree_step {s A r}:
    valid_tree A -> step u s A = r -> valid_tree (get_tree r).
  Proof.
    move=>+<-; clear r.
    elim: A s => //; try by move=> s r // *; subst.
    + by move=> ? ? ?? *;subst => //=; rewrite valid_tree_big_or.
    + move=> A IHA s B IHB s1/=.
      case:ifP => //[dA vB|dA/andP[vA bB]].
        rewrite get_tree_Or/=dA IHB//.
        (* rewrite disj_tree_commE (disj_tree_step erefl)//disj_tree_commE//. *)
      have /= := IHA s1 vA.
      case X: step => //=[A'|A'|A'|A'] H; 
      rewrite !(step_not_dead _ dA X, H,bB,bbOr_cutr,disj_tree_cutrR,disj_tree_step X)//=.
    + move=> A HA B0 _ B HB s1 /=/and4P[vA ++ CC].
      case: ifP => [sA vB /= bB0 | sA /eqP->]/=.
        rewrite succes_step//=.
        have {HB} := HB (get_substS s1 A) vB.
        case X: step => //[C|C|C|C]/=vC; cycle 1; [|by rewrite sA vA vC /=bB0/=(check_cut_step _ X isT) CC..].
        rewrite success_cut sA/= valid_tree_cut//vC bbAnd_cutr//check_cut_cutrR//.
      case: ifP => [fA bB|fA bB].
        by rewrite failed_step//= vA sA eqxx bB/=fA// check_cut_refl.
      have:= HA s1 vA.
      case X: step => //[A'|A'|A'|A']/=vA'; last first;
       [|by rewrite //vA' base_and_valid///bbAnd bB eqxx !if_same//check_cut_refl// if_same..].
      have [? sA']:= step_solved_same _ X; subst.
      congruence.
  Qed.

  Lemma next_alt_aux_base_and {A}: base_and A -> next_alt false A = Some (A).
  Proof. elim: A => //; move=>a; case: a => //=[p t|] _ B0 HB0 B HB s/andP[/eqP->bB]/=; rewrite HB//. Qed.

  Lemma base_and_ko_failed {A}: base_and_ko A -> failed A.
  Proof. case: A => // -[]//. Qed.

  Lemma next_alt_aux_base_and_ko {A} b: base_and_ko A -> next_alt b A = None.
  Proof. elim: A => //=; move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=. Qed.

  Lemma base_and_is_dead {A}: base_and A -> is_dead A = false.
  Proof. move=>/base_and_failed; apply: contraFF is_dead_failed. Qed.

  Lemma base_and_ko_is_dead {A}: base_and_ko A -> is_dead A = false.
  Proof. case: A => //-[]//. Qed.

  Lemma base_or_failed {A}: base_or_aux A -> failed A = false.
  Proof. 
    elim: A=> //=.
    - move=> A HA s B HB /andP[bA bB]; case: ifP => _; auto.
      by apply: base_and_failed.
    - move=> []//=.
  Qed.

  Lemma base_or_is_dead {A}: base_or_aux A -> is_dead A = false.
  Proof. move=>/base_or_failed; apply: contraFF is_dead_failed. Qed.

  Lemma base_or_aux_ko_is_ko {A}: base_or_aux_ko A -> is_ko A.
  Proof.
    elim: A => //=.
    - by move=> A HA _ B HB /andP[]/base_and_ko_is_ko->/HB->.
    - move=> []//.
  Qed.
  Lemma base_or_aux_is_ko {A}: base_or_aux A -> is_ko A = false.
  Proof. move=> /base_or_failed/failed_is_ko//. Qed.

  Lemma base_or_aux_is_dead {A}: base_or_aux_ko A -> is_dead A = false.
  Proof. elim: A => //.
    - move=> A HA s B HB/=/andP[bA bB].
      rewrite HB//andbF//.
    - move=> []//. 
  Qed.

  Lemma base_or_aux_failed {A}: base_or_aux_ko A -> failed A.
  Proof. elim: A => //.
    - move=> A HA s B HB/=/andP[bA bB].
      rewrite (base_and_ko_is_dead bA)base_and_ko_failed//.
    - move=> []//. 
  Qed.

  Lemma next_alt_aux_base_or_ko {A} b: base_or_aux_ko A -> next_alt b A = None.
  Proof. 
    elim: A b => //. 
    - move=> A HA s B HB /= b /andP[bA bB].
      rewrite !HB// next_alt_aux_base_and_ko// !if_same//.
    - move=>/=[]//p a _ B0 HB0 B HB/andP[/eqP->bB]/=. 
  Qed.

  Lemma next_alt_aux_base_or_none {A}: base_or_aux A -> next_alt false A = None -> A = Bot.
  Proof. 
    elim: A => //. 
    - move=> A HA s B HB /= /andP[bA bB].
      rewrite base_and_dead//next_alt_aux_base_and//.
    - move=>A; case: A => //[p a|] _ B0 HB0 B HB/andP[/eqP->bB]/=;
      rewrite next_alt_aux_base_and//. 
  Qed.

  Lemma next_alt_keep_cut {A B b}:
    valid_tree A -> next_alt b A = Some B -> has_cut B = has_cut A.
  Proof.
    elim: A B b => //=.
    - move=> B []// _ [<-]//.
    - move=> _ _ _ _ _ [<-]//.
    - move=> []//.
    - move=> A HA s B HB C b.
      case: ifP => [dA vB|dA /andP[vA bB]].
        rewrite is_dead_next_alt//.
        case nB: next_alt => [v|]; last (by []); by move=> [<-]/=.
      case nA: next_alt => [A'|]; first by move=>[<-]/=.
      case nB: next_alt => [B'|//][<-]//.
    - move=> A HA B0 HB0 B HB C b /and4P[vA].
      case: ifP => [sA vB /=bB CC|sA /eqP->{B0 HB0}]/=.
        rewrite success_failed//=.
        case nB: next_alt => [B'|]; first by move=> [<-]/=; rewrite (HB _ _ vB nB).
        case nA: next_alt => //=[A'].
        case nB0: next_alt => //=[B0'][<-]{C}/=.
        have {}HA:= HA _ _ vA nA.
        have {}HB0:= HB0 _ _ (bbAnd_valid bB) nB0.
        rewrite HA HB0.
        do 2 f_equal.
        move:CC; rewrite /check_cut.
        case: has_cut => [/orP[kB|->]|/eqP->//]//.
        by rewrite is_ko_next_alt in nB0.
      case:ifP => [fA bB|fA bB CC [<-]]//= _.
      case nA: next_alt => //=[A'].
      case nB: next_alt => //=[B'][<-]{C}/=.
      by rewrite (HA _ _ vA nA) (HB _ _ (bbAnd_valid bB) nB).
  Qed.

  Lemma next_alt_check_cut {A B b B0}:
    valid_tree A -> next_alt b A = Some B -> check_cut B B0 = check_cut A B0.
  Proof. move=> vA nA; rewrite /check_cut (next_alt_keep_cut vA nA)//. Qed.

  Lemma disj_tree_next_alt A B D b:
    disj_tree A D -> next_alt b A = Some B -> disj_tree B D.
  Proof.
    elim: A B b => //=.
    - move=> B []// _ [<-]//.
    - move=> p c B// _ H [<-]//.
    - move=> B _ H [<-]//.
    - move=> A HA s B HB C b /disj_tree_Or[dA dB].
      case nA: next_alt => [A'|].
        by move=> [<-]; apply/disj_tree_Or; rewrite dB (HA _ _ dA nA).
      case nB: next_alt => [B'|]//[<-].
      apply/disj_tree_Or; rewrite (HB _ _ dB nB).
      case:ifP; split; rewrite //disj_tree_deadL//.
    - move=> A HA B0 HB0 B HB C b /disj_tree_And[dA dB0 dB].
      case:ifP => fA.
        case nA: next_alt => [A'|]//.
        case nB0: next_alt => [B0'|]//[<-].
        by apply/disj_tree_And; split; rewrite //(HA _ _ _ nA,HB0 _ _ _ nB0).
      case: ifP => sA; last by move=> [<-]; apply/disj_tree_And; split.
      case nB: next_alt => [B'|].
        by move=>[<-]; apply/disj_tree_And; split; rewrite//(HB _ _ _ nB).
      case nA: next_alt => [A'|]//.
      case nB0: next_alt => [B0'|]//[<-].
      by apply/disj_tree_And; split; rewrite //(HA _ _ _ nA,HB0 _ _ _ nB0).
  Qed.

  Lemma disj_tree_next_altR A B D b:
    disj_tree D A -> next_alt b A = Some B -> disj_tree D B.
  Proof. by move=> /disj_tree_comm dA /(disj_tree_next_alt dA)/disj_tree_comm. Qed.

  Lemma resetR_next_alt A B B0 b:
    bbAnd B0 ->
    valid_tree A -> next_alt b A = Some B -> 
    resetR B0 A -> resetR B0 B.
  Proof.
    rewrite/resetR.
    move=> /orP[]bB; last by rewrite base_and_ko_is_ko//.
    rewrite base_and_is_ko//=.
    elim: A B B0 b bB => //=.
    - move=> B []//[]// _ _ [<-]//.
    - move=> p c B []//=.
    - move=> B []//.
    - move=> A HA s B HB C []//.
    - move=> A HA B0 HB0 B HB C []// L _ R b /base_and_AndP[H -> bR] /and4P[vA ++ cK] + /resetR'P.
      case:ifP => [sA vB/= bB0|sA/eqP->{B0 HB0 cK}]/=.
        rewrite success_failed//=.
        case nB: next_alt => [B'|].
          move=> [<-]; case: eqP => H1; subst.
            by move: H => []; destruct A => //.
          move=> /andP[->]; apply: HB; eauto.
        case nA: next_alt => //=[A'].
        case nB0: next_alt => //=[B0'][<-].
        case: eqP => H1; subst.
          by move: H => []; destruct A => //.
        move=> /andP[H2 H3].
        case: eqP => H4; subst.
           (*to satisfy nA A should be == A': contradicts H1*)
          admit.
        rewrite (disj_tree_next_altR H2 nA)/=.
        move/orP: bB0 => []bB; last first.
          by rewrite (is_ko_next_alt _ (base_and_ko_is_ko bB)) in nB0.
        move: nB0; rewrite next_alt_aux_base_and//.
        move=> [<-]{B0'}.
        (* move/orP: rB; rewrite base_and_is_ko// => -[]//rR'. *)
        (* Print resetR'. *)

  Abort.

  Lemma valid_tree_next_alt {A B b}: 
    valid_tree A -> next_alt b A = Some (B) 
    -> valid_tree B.
  Proof.
    elim: A  B b => //=.
    + move=> B b _; case: ifP => // _ [<-]//.
    + move=> p c B _ _ [<-]//.
    + move=> B _ _ [<-]//.
    + move=> A HA s B HB  C b/=.
      case: ifP => [dA vB|dA /andP[vA bB]].
        rewrite is_dead_next_alt//.
        case X: next_alt => //[D] [<-]/=.
        by rewrite dA (HB _ _ vB X)// (disj_tree_next_altR _ X).
      case X: next_alt => [D|].
        by move=>[<-]/=; rewrite bbOr_valid// bB (HA _ _ vA X) if_same.
      by case Y: next_alt => [D|]//[<-]/=; rewrite is_dead_dead (HB _ _ _ Y)//bbOr_valid.
    + move=> A HA B0 HB0 B HB  C b /=/and4P[vA ++ CC].
      case: ifP => /=[sA vB  bB0|sA /eqP?]; subst.
        rewrite success_failed//.
        case X: next_alt => [D|].
          move=>[<-]/=; rewrite vA sA/= (HB _ _ vB X)//bB0/=.
          by rewrite (next_alt_check_cut vB X) CC.
        case Y: next_alt => //=[A'].
        move: bB0 => /orPT[]/[dup]bB; last first.
          move=> /(next_alt_aux_base_and_ko false) -> //.
        move=> /next_alt_aux_base_and->[<-]/=.
        by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA Y) !if_same// check_cut_refl.
      case: ifP => fA bB; last first.
        move=> [<-]/=; rewrite vA sA eqxx /bbAnd bB if_same//.
      case X: next_alt => [D|]//.
      move: bB => /orPT[]/[dup]bB; last first.
        move=> /(next_alt_aux_base_and_ko false) -> //.
      move=> /next_alt_aux_base_and->[<-]/=.
      by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA X) //!if_same//.
    Qed.

  Lemma valid_tree_run {s1 A s2 B b}:
    valid_tree A -> run u s1 A s2 B b -> (B = dead B) + valid_tree B.
  Proof.
    move=> + H; elim: H; clear => //=.
    + move=> s1 s2 A B sA _ <- vA.
      case X: next_alt => [B'|]/=.
        by rewrite (valid_tree_next_alt vA X); auto.
      by rewrite dead2; auto.
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_tree_step vA eA).
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_tree_step vA eA).
    + move=> s1 s2 A B r n fA + rB + vA; subst.
      move=> /(valid_tree_next_alt vA) vB /(_ vB)//.
    + by move => *; rewrite dead2; auto.
  Qed.

  Lemma base_and_ko_succes {B}: base_and_ko B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.
End valid_tree.
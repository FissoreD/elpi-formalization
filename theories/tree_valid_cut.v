From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Hint Resolve is_dead_dead : core.

Section valid_tree.
  Variable u : Unif.

  Fixpoint has_cut A :=
    match A with
    | CutS => true
    | OK | CallS _ _ | Bot | Dead => false
    | And A B0 B => 
      [||has_cut A, ((next_alt true A == None) && has_cut B) |
      (has_cut B0 && (is_ko B || has_cut B))]
      (* here, B0 is useless. B0 is used if A is failed while backtracking,
         but B0 is resumed inside or and its cut have no effect outside the
         And A B0 B tree
      *)
      (* ((failed A == false) && (has_cut A || has_cut B)) *)
      (* has_cut A TODO: should be more permessive *)
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
    | Or l _ r => base_and l && (base_or_aux r) (* todo: should also say something about the substitution and the program? *)
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

  Fixpoint valid_tree s :=
    match s with
    | CutS | CallS _ _ | OK | Bot => true
    | Dead => false
    | Or A _ B => 
      if is_dead A then valid_tree B
      else valid_tree A && (bbOr B)
    | And A B0 B => 
      [&& valid_tree A,
        if success A then valid_tree B 
        else (B0 == B),
        (if success A || failed A then bbAnd B0 else base_and B0)
        & (~~ has_cut B0 || has_cut B)]
    end.

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
      move=> _ H H1; rewrite H1//eqxx//orNb//.
    move=> _ H _ _ /andP[/eqP<-] H1; rewrite H1//eqxx//orNb//.
  Qed.

  Lemma valid_tree_big_and {pr l} : valid_tree (big_and pr l).
  Proof. apply: base_and_valid base_and_big_and. Qed.

  Lemma bbAnd_valid {A} : bbAnd A -> valid_tree A.
  Proof.
    move=>/orP[].
      apply: base_and_valid.
    elim: A=> //.
    move=> []// _ B0 HB0 B HB/=/and3P[H/eqP->]bB.
    by rewrite eqxx /bbAnd bB orbT//orNb.
  Qed.

  Lemma big_or_aux_not_bot {pr l rs}: big_or_aux pr l rs != Bot.
  Proof. case: rs => [|[] xs]//=; case: l => //. Qed.

  Lemma bbOr_big_or_aux {pr s l}: bbOr (big_or_aux pr s l).
  Proof.
    rewrite/bbOr.
    case: base_or_aux_ko; rewrite ?orbT//orbF.
    elim: l s => //=; clear.
    + move=> []//a l; rewrite /base_or_aux //= base_and_big_and eqxx//.
      case: a => //.
    + by move=> [s r] rs IH r1 /=; rewrite IH base_and_big_and.
  Qed.

  Lemma valid_tree_big_or {pr s t} : valid_tree (big_or u pr s t).
  Proof.
    case: t; rewrite /big_or//=.
    + move=> c; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//.
    + move=> c; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//.
    + move=> ??; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//. 
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_tree B.
  Proof.
    elim: B => //.
    move=> []// HA B0 _ B HB/= /and3P[bB0 /eqP <-] H.
    by rewrite eqxx /bbAnd H orbT orNb.
  Qed.

  Lemma base_and_base_or_aux {A}: base_and A -> base_or_aux A.
  Proof. case: A => //. Qed.

  Lemma base_and_ko_base_or_aux_ko {A}: base_and_ko A -> base_or_aux_ko A.
  Proof. case: A => //. Qed.

  Lemma bbOr_valid {B}:
    bbOr B -> valid_tree B.
  Proof. 
    move=> /orP [].
    elim B => //; clear.
    + move=> A HA s B HB/=/andP[bA bB].
      rewrite HA ?base_and_base_or_aux// /bbOr bB HB// if_same//base_and_is_and//orbT//.
    + move=> s; case: s => //[p t|] Ha B0 HB0 B HB /=/andP[/eqP->]bB; rewrite eqxx bB//orNb//.
    elim: B => //.
    + move=> A HA s B HB /= /andP [bA bB].
      rewrite HB//HA?base_and_ko_base_or_aux_ko// /bbOr bB orbT if_same//base_and_ko_is_and//orbT//.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      rewrite /bbAnd bB0 eqxx // orbT//orNb//.
  Qed.

  Lemma base_and_base_and_ko_cut {B} : base_and B -> base_and_ko (cutr B).
  Proof. 
    elim: B => // A + B + C /=.
    case: A => //=[_ _|] _ HB HC /andP [] /eqP <-bB; rewrite HB//eqxx//.
  Qed.

  Lemma base_and_ko_base_and_ko_cutr {B} : base_and_ko B -> base_and_ko (cutr B).
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
    + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cutr -> /IHB ->//.
    + move=> a; case: a => //=[_ _|] _ B HB C HC /andP [] /eqP /[subst1] hC;
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
    move=> /base_and_ko_base_and_ko_cutr->; rewrite eqxx//.
  Qed.

  Lemma bbAnd_cutl{B0}:
    bbAnd B0 -> (B0 == OK) || base_and_ko (cutl B0).
  Proof. move=> /orP[/base_and_cutl|/base_ko_and_cutl]//->; rewrite orbT//. Qed.

  Lemma bbOr_cutr {B}: bbOr B -> bbOr (cutr B).
  Proof.
    rewrite/bbOr.
    move=>/orP[/base_or_base_or_ko_cutr|/base_or_ko_cutr]->; rewrite orbT//.
  Qed.

  Lemma bbAnd_cutr {A}: bbAnd A -> bbAnd (cutr A).
  Proof.
    rewrite /bbAnd => /orP[].
      move=>/base_and_base_and_ko_cut-->; apply orbT.
    move=> /base_and_ko_base_and_ko_cutr->; apply orbT.
  Qed.

  Lemma has_cut_cutr A: has_cut (cutr A) = false.
  Proof. elim: A => //=A -> B0 -> B ->; rewrite is_ko_cutr andbF//=. Qed.

  Lemma has_cut_dead A: has_cut (dead A) = false.
  Proof. elim: A => //=A -> B0 -> B ->; rewrite is_dead_is_ko // andbF//=. Qed.

  Lemma valid_tree_cutr {A}: valid_tree A -> valid_tree (cutr A).
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      rewrite is_dead_cutr.
      case: ifP => [dA vA|dA/andP[vA bB]]//; auto.
      by rewrite bbOr_cutr//HA//.
    - move=> A HA B0 HB0 B HB/=/and4P[vA ++ C]; rewrite has_cut_cutr/=.
      case: ifP => /=[sA vB bB| sA /eqP -> bB].
        rewrite?has_cut_cutr//=HA//HB//. 
        (* ?bbOr_valid// iscuc. *)
      (* rewrite HA//HB//bbAnd_cutr// success_cutr failed_cutr/=andbT. *)
  Abort.

  Lemma valid_tree_cut {A}: success A -> valid_tree A -> valid_tree (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB => /=.
      case: ifP => //[dA sB vB| dA sA /andP[vA bB]]/=.
        rewrite dA HB//.
      rewrite is_dead_cutl dA HA// bbOr_cutr//.
    move=> A HA B0 HB0 B HB /= /andP[sA sB] /and4P[vA ++ C].
    rewrite sA/= => vB bB.
    by rewrite success_cut sA HA//HB//=bbAnd_cutr// has_cut_cutr.
  Qed.

  Lemma base_and_bbAnd {A}: base_and A -> bbAnd A.
  Proof. rewrite/bbAnd=>->//. Qed.

  Lemma step_keep_cut s A r:
    has_cut A -> step u s A = r -> ~~(is_cutbrothers r) -> has_cut (get_tree r).
  Proof.
    move=> +<-{r}; elim: A s => //=.
    move=> A HA B0 HB0 B HB s H.
    move: (HA s).
    case eA: step => [A'|A'|A'|A']//= /(_ _ isT) {}HA.
    - move: H => /or3P[/HA ->//|/andP[/eqP /next_alt_alt_None_sf[sA|fA]]|->];
      rewrite ?orbT//; rewrite ?(succes_is_solved _ _ sA) ?(failed_expand _ fA)// in eA.
    - by have [? fA] := expand_failed_same _ eA; subst A'.
    - move: (HB (get_substS s A')).
      have [? sA] := expand_solved_same _ eA; subst A'.
      case eB: step => [B'|B'|B'|B']//= /(_ _ isT) {}HB _.
      - move: H => /or3P[->//|/andP[->/HB->]|/andP[->]]; rewrite?orbT//.
        rewrite (step_is_ko _ eB)//==>/HB->; rewrite !orbT//.
      - move: H => /or3P[->//|/andP[->/HB->]|/andP[->]]; rewrite?orbT//.
        move=> /orP[KB|/HB->]; rewrite ?orbT//.
        by move: eB; rewrite is_ko_step// => -[?]; subst; rewrite KB; rewrite !orbT.
      - move: H => /or3P[->//|/andP[->/HB->]|/andP[->]]; rewrite?orbT//.
        rewrite (step_is_ko _ eB)//==>/HB->; rewrite !orbT//.
  Qed.

  Lemma valid_tree_expand {s A r}:
    valid_tree A -> step u s A = r -> valid_tree (get_tree r).
  Proof.
    move=>+<-; clear r.
    elim: A s => //; try by move=> s r // *; subst.
    + by move=> ? ? ?? *;subst => //=; rewrite valid_tree_big_or.
    + move=> A IHA s B IHB s1/=.
      case:ifP => //[dA vB|dA/andP[vA bB]].
        rewrite get_tree_Or/=dA IHB//.
      have /= := IHA s1 vA.
      case X: step => //= H; rewrite (step_not_dead _ dA X) H//bbOr_cutr//.
    + move=> A HA B0 _ B HB s1 /=/and4P[vA ++ CC].
      case: ifP => [sA vB /= bB0 | sA /eqP->]/=.
        rewrite succes_is_solved//=.
        have {HB} := HB (get_substS s1 A) vB.
        case X: step => //[C|C|C|C]/=vC; rewrite ?sA ?vA ?vC ?CC/=?bB0/=;
        try move/orP: CC => [->|]///step_keep_cut/(_ X)->//=; rewrite?orbT//.
        rewrite success_cut sA/= valid_tree_cut// has_cut_cutr//=.
        rewrite bbAnd_cutr//.
      case: ifP => [fA bB|fA bB].
        rewrite failed_expand//=vA sA eqxx bB/=fA//orNb//.
      have:= HA s1 vA.
      case X: step => //[A'|A'|A'|A']/=vA'; last first;
       [|by rewrite //vA' base_and_valid///bbAnd bB eqxx !if_same//orNb//..].
      have [? sA']:= expand_solved_same _ X; subst.
      congruence.
  Qed.

  Lemma valid_tree_big_or_aux {pr s l} : valid_tree (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_tree_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      rewrite valid_tree_big_and bbOr_big_or_aux IH if_same//.
  Qed.

  Lemma next_alt_aux_base_and {A}: base_and A -> next_alt false A = Some (A).
  Proof. elim: A => //; move=>a; case: a => //=[p t|] _ B0 HB0 B HB s/andP[/eqP->bB]/=; rewrite HB//. Qed.

  Lemma base_and_ko_failed {A}: base_and_ko A -> failed A.
  Proof. case: A => // -[]//. Qed.

  Lemma next_alt_aux_base_and_ko {A} b: base_and_ko A -> next_alt b A = None.
  Proof. elim: A => //=; move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=. Qed.

  Lemma base_and_failed {A}: base_and A -> failed A = false.
  Proof. elim: A => //=-[]//=p a _ A HA B HB /andP[]//. Qed.

  Lemma base_and_is_dead {A}: base_and A -> is_dead A = false.
  Proof. move=>/base_and_failed; apply: contraFF is_dead_failed. Qed.

  Lemma base_and_ko_is_ko {A}: base_and_ko A -> is_ko A.
  Proof. elim: A => //=-[]//. Qed.

  Lemma base_and_ko_is_dead {A}: base_and_ko A -> is_dead A = false.
  Proof. case: A => //-[]//. Qed.

  Lemma base_or_failed {A}: base_or_aux A -> failed A = false.
  Proof. elim: A => //=-[]//=[]//. Qed.

  Lemma base_or_is_dead {A}: base_or_aux A -> is_dead A = false.
  Proof. move=>/base_or_failed; apply: contraFF is_dead_failed. Qed.

  Lemma base_or_aux_ko_is_ko {A}: base_or_aux_ko A -> is_ko A.
  Proof.
    elim: A => //=.
    - by move=> A HA _ B HB /andP[]/base_and_ko_is_ko->/HB->.
    - move=> []//.
  Qed.

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
    valid_tree A -> next_alt b A = Some B -> has_cut A -> has_cut B.
  Proof.
    elim: A B b => //=.
    - move=> B []// _ [<-]//.
    - move=> A HA B0 HB0 B HB C b /and4P[vA].
      case: ifP => [sA vB /=bB CC|sA /eqP->{B0 HB0}]/=.
        rewrite success_failed//=.
        case nB: next_alt => [v|]//=.
          move=> [?]; subst => /=.
          have {}HB:= HB _ _ vB nB.
          move => /or3P[->|/andP[->/HB->]|/andP[->]/orP[|/HB->]]//=;rewrite?orbT//.
          by move=> H; rewrite is_ko_next_alt in nB.
        case nA: next_alt => //=[A'].
        case nB0: next_alt => //=[B0'][<-]{C}/=.
        have {}HA:= HA _ _ vA nA.
        have {}HB0:= HB0 _ _ (bbAnd_valid bB) nB0.
        by move=> /orP[/HA->//|/andP[/[dup] H ->] _]; rewrite HB0// !orbT.
      case:ifP => [fA bB|fA bB CC [<-]]//=.
      rewrite orNb => _.
      case nA: next_alt => //=[A'].
      case nB: next_alt => //=[B'][<-]{C}/=.
      have {}HA:= HA _ _ vA nA.
      have {}HB:= HB _ _ (bbAnd_valid bB) nB.
      move=> /or3P[/HA->//||/andP[/[dup] /HB->->]]; rewrite ?orbT//.
      rewrite next_alt_false_true//nA//.
  Qed.

  Lemma valid_tree_next_alt {A B b}: 
    valid_tree A -> next_alt b A = Some (B) 
    -> valid_tree B.
  Proof.
    elim: A  B b => //=.
    + move=> B b _; case: ifP => // _ [<-]//.
    + move=> p c B _ _ [<-]//.
    + move=> B _ _ [<-]//.
    + move=> A HA s B HB  C b/=.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite is_dead_next_alt//.
        case X: next_alt => //[D] [<-]/=.
        rewrite dA (HB _ _ vB X)//.
      case X: next_alt => [D|].
        move=>[<-]/=; rewrite bbOr_valid// bB (HA _ _ vA X) if_same//.
      case Y: next_alt => [D|]//[<-]/=; rewrite is_dead_dead (HB _ _ _ Y)//bbOr_valid//.
    + move=> A HA B0 HB0 B HB  C b /=/and4P[vA ++ CC].
      case: ifP => /=[sA vB bB0|sA /eqP?]; subst.
        rewrite success_failed//.
        case X: next_alt => [D|].
          move=>[<-]/=; rewrite vA sA/= (HB _ _ vB X)//bB0/=;
          move/orP: CC=> [->|]//.
          by move=> /(next_alt_keep_cut vB X)->; rewrite orbT.
        case Y: next_alt => //=[A'].
        move: bB0 => /orPT[]/[dup]bB; last first.
          move=> /(next_alt_aux_base_and_ko false) -> //.
        move=> /next_alt_aux_base_and->[<-]/=.
        by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA Y) !if_same//orNb//.
      case: ifP => fA bB; last first.
        move=> [<-]/=; rewrite vA sA eqxx /bbAnd bB if_same//.
      case X: next_alt => [D|]//.
      move: bB => /orPT[]/[dup]bB; last first.
        move=> /(next_alt_aux_base_and_ko false) -> //.
      move=> /next_alt_aux_base_and->[<-]/=.
      by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA X) //!if_same//.
    Qed.

  Lemma valid_tree_run {s1 A s2 B b}:
    valid_tree A -> runb u s1 A s2 B b -> (B = dead B) + valid_tree B.
  Proof.
    move=> + H; elim: H; clear => //=.
    + move=> s1 s2 A B sA _ <- vA.
      case X: next_alt => [B'|]/=.
        by rewrite (valid_tree_next_alt vA X); auto.
      by rewrite dead2; auto.
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_tree_expand vA eA).
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_tree_expand vA eA).
    + move=> s1 s2 A B r n fA + rB + vA; subst.
      move=> /(valid_tree_next_alt vA) vB /(_ vB)//.
    + by move => *; rewrite dead2; auto.
  Qed.

  Lemma base_and_ko_succes {B}: base_and_ko B -> success B = false.
  Proof. elim: B => // -[]//=. Qed.
End valid_tree.
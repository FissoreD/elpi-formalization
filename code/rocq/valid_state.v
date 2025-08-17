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


  (* Lemma base_or_dead {B}: base_or_aux B || base_or_aux_ko B -> is_dead B = false.
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
  Qed. *)

  Definition bbOr B := base_or_aux B || base_or_aux_ko B. 
  Definition bbAnd B := base_and B||base_and_ko B. 

  (* Fixpoint valid_state s :=
    match s with
    | Goal _ _ | Bot | Top => true
    | Dead => false
    | OK => false
    | Or Dead _ (Or _ _ _ as B) => valid_state B
    | Or A _ B => valid_state A && bbOr B
    | And OK B0 (And _ _ _ as B) => 
       valid_state B && bbAnd B0
    | And A B0 B => 
      [&& valid_state A,
        if success A then valid_state B
        else (B0 == B)
        & (bbAnd B0)]
    end. *)

  Fixpoint is_and A := 
    match A with
    | And _ _ A => is_and A
    | Bot | Top | OK => true
    | _ => false
    end.

  Definition is_or A := 
    match A with
    | OK | Bot | Or _ _ _ | Goal _ _ => true
    | _ => false
    end.

  Lemma base_and_is_or {A}: base_and A -> is_or A = false.
  Proof. case: A => //. Qed.

  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | Bot | Top => true
    | Dead => false
    | Or A _ B => 
      if is_dead A then valid_state B
      else valid_state A && (bbOr B)
    | And A B0 B => 
      [&& is_or A, valid_state A, is_and B,
        if success A then valid_state B 
        else (B0 == B)
        (* We should notice that in (OK \/ KO) /\ OK the reset point is forced to be cut *)
        & (if success A || failed A then bbAnd B0 else base_and B0)]
    end.

    (* TODO: OK /\ p non deve essere valido: la expand nel caso di And va avanti
      a destra e mangerebbe p
    *)

  Lemma valid_state_dead {A} : is_dead A -> valid_state A = false.
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[]dA dB.
      rewrite HA// dA HB//andbF//.
    move=> A HA Bo ? B HB/=dA.
    rewrite HA// andbF//.
  Qed.

  Lemma base_and_is_and {A}: base_and A -> is_and A.
  Proof. elim: A => // -[]// p a _ B0 _ B HB/=/andP[_]//. Qed.

  Lemma base_and_ko_is_and {A}: base_and_ko A -> is_and A.
  Proof. elim: A => //-[]// _ B0 _ B HB/= /and3P[]//. Qed.

  Lemma bbAnd_is_and {A}: bbAnd A -> is_and A.
  Proof. rewrite/bbAnd => /orP[/base_and_is_and|/base_and_ko_is_and]//. Qed.

  Lemma is_and_cutl {A}: is_and A -> is_and (cutl A).
  Proof. elim: A => //. Qed.

  Lemma is_or_cutl {A}: is_or A -> is_or (cutl A).
  Proof. elim: A => //A HA s B HB/=; rewrite fun_if/=if_same//. Qed.

  Lemma is_or_big_or {p s t}: is_or (big_or p s t).
  Proof. rewrite /big_or; case: F => //-[]//. Qed.


  Lemma valid_state_dead1 {A} : valid_state A -> is_dead A = false.
  Proof. apply: contraPF => /valid_state_dead->//. Qed.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //.
    move=> p a _ + A + /andP [] /eqP H ; rewrite H.
    move=> _ HVA HA. rewrite (HVA HA) /=.
    rewrite /bbAnd HA eqxx// base_and_is_and//.
  Qed.

  Lemma valid_state_big_and {pr l} : valid_state (big_and pr l).
  Proof. apply: base_and_valid base_and_big_and. Qed.

  Lemma bbAnd_valid {A} : bbAnd A -> valid_state A.
  Proof.
    move=>/orP[].
      apply: base_and_valid.
    elim: A=> //.
    move=> []// _ B0 HB0 B HB/=/and3P[H/eqP->]bB.
    rewrite eqxx /bbAnd bB orbT//base_and_ko_is_and//.
  Qed.

  Lemma big_or_aux_not_bot {pr l rs}: big_or_aux pr l rs != Bot.
  Proof. case: rs => [|[] xs]//=; case: l => //. Qed.

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
    + move=> c; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//.
    + move=> c; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//.
    + move=> ??; case: F => // -[] //s1 r rs/=; rewrite bbOr_big_or_aux//. 
  Qed.

  Lemma base_and_ko_valid {B}: base_and_ko B -> valid_state B.
  Proof.
    elim: B => //.
    move=> []// HA B0 _ B HB/= /and3P[bB0 /eqP <-] H.
    rewrite eqxx /bbAnd H base_and_ko_is_and//orbT//.
  Qed.

  Lemma base_and_base_or_aux {A}: base_and A -> base_or_aux A.
  Proof. case: A => //. Qed.

  Lemma base_and_ko_base_or_aux_ko {A}: base_and_ko A -> base_or_aux_ko A.
  Proof. case: A => //. Qed.

  Lemma bbOr_valid {B}:
    bbOr B -> valid_state B.
  Proof. 
    move=> /orP [].
    elim B => //; clear.
    + move=> A HA s B HB/=/andP[bA bB].
      rewrite HA ?base_and_base_or_aux// /bbOr bB HB// if_same//base_and_is_and//orbT//.
    + move=> []// p a Ha B0 HB0 B HB /=/andP[/eqP->]bB.
      rewrite eqxx base_and_is_and bB//.
    elim: B => //.
    + move=> A HA s B HB /= /andP [bA bB].
      rewrite HB//HA?base_and_ko_base_or_aux_ko// /bbOr bB orbT if_same//base_and_ko_is_and//orbT//.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      rewrite /bbAnd bB0 eqxx base_and_ko_is_and// orbT//.
  Qed.

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

  (* Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else ((B02 == B2))) ->
      bbAnd B02 ->
        valid_state B2.
  Proof. case: success => //; move=>/eqP->. apply: bbAnd_valid. Qed. *)

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

  Lemma bbAnd_cutr {A}: bbAnd A -> bbAnd (cutr A).
  Proof.
    rewrite /bbAnd => /orP[].
      move=>/base_and_base_and_ko_cut-->; apply orbT.
    move=> /base_and_ko_base_and_ko_cutr->; apply orbT.
  Qed.

  (* Lemma valid_state_cutr {A}: valid_state A -> valid_state (cutr A).
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      case: ifP => //[dA vA|dA/andP[vA bB]].
        rewrite is_dead_cutr//; auto.
      rewrite HA// bbOr_cutr// HB//?bbOr_valid//if_same//.
    - move=> A HA B0 HB0 B HB/=/and3P[vA].
      case: ifP => [sA vB bbB0 | sA /eqP -> bB].
        rewrite HA//HB//bbAnd_cutr//.
      case: (A =P OK) => oA.
        rewrite oA/=.
        case: B HB => //B s' B' H1 /andP[vB bB0].
        rewrite bbAnd_cutr//andbT.
        rewrite bbAnd_cutl
        move=>/H->. *)

  Lemma valid_state_cut {A}: success A -> valid_state A -> valid_state (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB => /=.
      case: ifP => //[dA sB vB| dA sA].
        move=>/=; rewrite dA/=; apply: HB sB vB.
      move=>/=/andP[vA bB]; rewrite HA// bbOr_cutr//is_dead_cutl dA//is_and_cutl//.
    move=> A HA B0 HB0 B HB /=/andP[sA sB].
    rewrite sA/=success_cut//=.
    move=>/and5P[oA vA aB vB bB0].
    rewrite is_or_cutl// HB// bbAnd_cutl//HA// is_and_cutl//.
  Qed.

  (* Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B.
  Proof.
    move=>/= /and3P[]// -> VB bbB0.
    by rewrite (valid_state_compose_and VB bbB0).
  Qed. *)

  Lemma is_or_expand {s A r}: is_or A -> expand s A = r -> is_or (get_state r).
  Proof.
    move=> + <-; clear r. 
    elim: A s => //.
    - move=> p/=[|t]//=s; rewrite is_or_big_or//.
    - move=> A HA s B HB s1/= _; case: ifP => dA; case: expand => //.
  Qed.

  Lemma is_and_expand {s A r}: is_and A -> expand s A = r -> is_and (get_state r).
  Proof.
    move=> + <-; clear r. 
    elim: A s => //.
    move=> A HA B0 _ B HB s1/= aB.
    case eA: expand => //=.
    rewrite get_state_And//=.
    apply: HB aB.
  Qed.

  Lemma base_and_bbAnd {A}: base_and A -> bbAnd A.
  Proof. rewrite/bbAnd=>->//. Qed.

  Lemma valid_state_expand {s A r}:
    valid_state A -> expand s A = r -> valid_state (get_state r).
  Proof.
    move=>+<-; clear r.
    elim: A s => //; try by move=> s r // *; subst.
    + by move=> ? [|?] ?? *;subst => //=; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1/=.
      case:ifP => //[dA vB|dA/andP[vA bB]].
        rewrite get_state_Or/=dA IHB//.
      have /= := IHA s1 vA.
      case X: expand => //= H; rewrite (expand_not_dead dA X) H//bbOr_cutr//.
    + move=> A HA B0 _ B HB s1 /=/and5P[oA vA aB].
      case: ifP => [sA vB /= bB0 | sA /eqP->]/=.
        rewrite succes_is_solved//=.
        have:= HB s1 vB.
        case X: expand => //[s2 C|s2 C|C|s2 C]/=vC; try by rewrite sA (is_and_expand aB X) vA vC oA//.
        rewrite is_or_cutl//valid_state_cut//(is_and_expand aB X) success_cut// vC //= bbAnd_cutl//.
      case: ifP => [fA bB|fA bB].
        rewrite failed_expand//=vA sA eqxx /= bB oA fA aB//.
      have:= HA s1 vA.
      case X: expand => //=[|||s2 C] H; last first; [|rewrite H eqxx /bbAnd bB if_same base_and_valid//if_same (is_or_expand oA X) aB//..].
      have:= HB s2 (base_and_valid bB).
      have /=oC := is_or_expand oA X.
      have [_ sC]:= expand_solved_success X.
      case Y: expand => //= H1; rewrite ?oC?H?H1?bB?sC?(base_and_bbAnd bB) (is_and_expand (base_and_is_and bB) Y)//.
      rewrite is_or_cutl//valid_state_cut//success_cut//=bbAnd_cutl//base_and_bbAnd//.
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

  (* Lemma next_alt_aux_base_and1 {A s}: base_and A -> next_alt s A = None.
  Proof.
    elim: A s => //=. s => //-[]//p a _ B0 _ B HB/= c.
    move=>/andP[]/eqP? bB;subst.
    by rewrite HB.
  Qed.

  Lemma next_alt_aux_bbase_and1 {A s}: bbAnd A -> next_alt s A = None.
  Proof.
    move=>/orP[].
      apply: next_alt_aux_base_and1.
    case: A => //=-[]//.
  Qed.*)

  Lemma next_alt_aux_base_and {A s}: base_and A -> next_alt s A = Some (s, A).
  Proof. elim: A s => //; move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=. rewrite HB//. Qed.

  Lemma base_and_ko_failed {A}: base_and_ko A -> failed A.
  Proof. case: A => // -[]//. Qed.

  Lemma next_alt_aux_base_and_ko {A s}: base_and_ko A -> next_alt s A = None.
  Proof. elim: A s => //=; move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=. Qed.

  Lemma next_alt_aux_bbAnd {A} s: 
    bbAnd A -> next_alt s A = Some (s, A) \/ next_alt s A = None.
  Proof. rewrite/bbAnd => /orP[/next_alt_aux_base_and|/next_alt_aux_base_and_ko]->; auto. Qed.

  Lemma base_and_failed {A}: base_and A -> failed A = false.
  Proof. elim: A => //=-[]//=p a _ A HA B HB /andP[]//. Qed.

  Lemma base_and_is_dead {A}: base_and A -> is_dead A = false.
  Proof. move=>/base_and_failed; apply: contraFF is_dead_failed. Qed.

  Lemma base_and_ko_is_dead {A}: base_and_ko A -> is_dead A = false.
  Proof. case: A => //-[]//. Qed.

  Lemma base_or_failed {A}: base_or_aux A -> failed A = false.
  Proof. elim: A => //=-[]//=[]//. Qed.

  Lemma base_or_is_dead {A}: base_or_aux A -> is_dead A = false.
  Proof. move=>/base_or_failed; apply: contraFF is_dead_failed. Qed.

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

  Lemma next_alt_aux_base_or_ko {A s}: base_or_aux_ko A -> next_alt s A = None.
  Proof. 
    elim: A s => //. 
    - move=> A HA s B HB s1 /= /andP[bA bB].
      rewrite !HB//next_alt_aux_base_and_ko//!if_same//.
    - move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=. 
  Qed.

  Lemma next_alt_aux_base_or_none {A s}: base_or_aux A -> next_alt s A = None -> A = Bot.
  Proof. 
    elim: A s => //. 
    - move=> A HA s B HB s1 /= /andP[bA bB].
      rewrite base_and_dead//next_alt_aux_base_and//.
    - move=>/=[]//p a _ B0 HB0 B HB s/andP[/eqP->bB]/=.
      rewrite next_alt_aux_base_and//. 
  Qed.

  Lemma is_and_or_next_alt {s1 A s2 B}: 
    valid_state A ->
      next_alt s1 A = Some (s2, B) -> ((is_or A = is_or B) * (is_and A = is_and B)).
  Proof.
    elim: A s1 s2 B => //.
    - move=> ????[_<-]//.
    - move=> p /= ?????[_<-]//.
    - move=> A HA s B HB s1 s2 C/=.
      case:ifP => //[dA vB|dA vA].
        case: next_alt => //-[s3 D][_<-]//.
      case: next_alt => // [[s3 D][_<-]|]//.
      case: ifP => //; case: next_alt => //-[s3 D] _ [_<-]//.
    - move=> A HA B0 _ B HB/=s1 s2 C/and5P[oA vA aB].
      case: ifP => //=[sA vB bB0|sA /eqP->].
        rewrite (valid_state_dead1 vA) success_failed//.
        case nB: next_alt => //[[]|].
          move=>[_<-]//=; rewrite (HB _ _ _ vB nB)//.
        case nA: next_alt => //[[]]; case: ifP => // _ [_<-]//=.
        rewrite (bbAnd_is_and bB0) aB//.
      rewrite (valid_state_dead1 vA).
      case: ifP => [fA bB|fA bB].
        case nA: next_alt => //[[]]; case: ifP => // _ [_<-]//=.
      case nB: next_alt => //[[]|].
        move=>[_<-]//=; rewrite (HB _ _ _ (base_and_valid bB) nB)//.
      case nA: next_alt => //[[]]; case: ifP => // _ [_<-]//.
  Qed.

  Lemma valid_state_next_alt {s1 s2 A B}: 
    valid_state A -> next_alt s1 A = Some (s2, B) 
    -> valid_state B.
  Proof.
    elim: A s1 s2 B => //.
    + move=>/=??? _[_<-]//.
    + move=> p a s1 s2 A/= _[_<-]//.
    + move=> A HA s B HB s1 s2 C/=.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        case X: next_alt => //[[s3 D]] [_<-]/=.
        rewrite dA (HB _ _ _ vB X)//.
      case X: next_alt => [[s3 D]|].
        move=>[_<-]/=; rewrite bbOr_valid// bB (HA _ _ _ vA X) if_same//.
      case: ifP => //dB.
      (* case: ifP => //fB. *)
        case Y: next_alt => [[s3 D]|]//.
        move=>[_<-]/=; rewrite is_dead_dead (HB _ _ _ _ Y)//bbOr_valid//.
      (* move=>[_<-]/=; rewrite is_dead_dead bbOr_valid//. *)
    + move=> A HA B0 HB0 B HB s1 s2 C/=/and5P[oA vA aB].
      case: ifP => /=[sA vB bB0|sA /eqP?]; subst.
        rewrite success_is_dead//success_failed//.
        case X: next_alt => [[s3 D]|].
          move=>[_<-]/=; rewrite vA sA oA/= (HB _ _ _ vB X)//-(is_and_or_next_alt vB X)aB//.
        case Y: next_alt=> [[s3 D]|]//.
        case: ifP => //fB0[_<-]/=; rewrite (HA _ _ _ vA Y)bbAnd_valid//eqxx bB0 if_same//=.
        rewrite -(is_and_or_next_alt vA Y) oA bbAnd_is_and//.
        move: bB0; rewrite /bbAnd => /orP[].
          move=>->; rewrite if_same//.
        move=>/base_and_ko_failed; rewrite fB0//.
      case: (ifP (is_dead _)) => //dA.
      move=>/=.
      case: ifP => fA bB.
        case X: next_alt => [[s3 D]|]//.
        case: ifP => fB//[_<-]/=; rewrite (HA _ _ _ vA X)bbAnd_valid//eqxx bB if_same//.
        rewrite -(is_and_or_next_alt vA X) oA bbAnd_is_and//.
        move: bB; rewrite /bbAnd => /orP[].
          move=>->; rewrite if_same//.
        move=>/base_and_ko_failed; rewrite fB//.
      rewrite (next_alt_aux_base_and bB).
      move=>[_<-]/=.
      rewrite vA sA eqxx bB fA oA// bbAnd_is_and///bbAnd bB//.
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

  Lemma is_or_clean_success {A}:
    is_or (clean_success A) = is_or A.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; rewrite fun_if if_same//.
    - move=> A HA B0 _ B HB/=; rewrite fun_if/=if_same//.
  Qed.

  Lemma is_and_clean_success {A}:
    is_and (clean_success A) = is_and A.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; rewrite fun_if if_same//.
    - move=> A HA B0 _ B HB/=; rewrite fun_if/= HB if_same//.
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
    - move=> A HA B0 _ B HB/=/and5P[oA vA aB]; rewrite (fun_if valid_state)/=oA vA.
      case: ifP => /=[sA vB bB0|sA /eqP->].
        rewrite bB0 andbT is_and_clean_success//aB; apply: HB vB.
      rewrite eqxx//aB//.
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

  Fixpoint base_and_expanded_done_state A :=
    match A with
    | And (Goal _ Cut) _ A => base_and_expanded_done_state A
    | Top => true
    | _ => false
    end.

  Lemma base_and_expanded_done {s1 A s2 B b}:
    base_and A -> expandedb s1 A (Done s2 B) b -> base_and_expanded_done_state A /\ s1 = s2.
  Proof.
    elim: A s1 B s2 b => //.
    - move=> s1 B s2 b _; inversion 1; subst => //.
      inversion H1; subst; inversion H2; subst => //; inversion H8; subst => //.
    - move=> []//p a _ B0 _ B HB s1 C s2 b/=/andP[/eqP->] H1 H2.
      have /=:= expandedb_same_structure H2.
      case: C H2 => // A' B0' B' H _.
      have [s3 [A1[B1[b1[b2[H3[H4 ?]]]]]]] := expanded_and_complete H; subst.
      inversion H3; clear H3; subst => //.
      - inversion H8 => //; destruct a => //.
      - inversion H0; clear H0 => //; destruct a => //=.
        move: H5 => [??]; subst.
        inversion H2; clear H2 => //; subst.
        case: H8 => [??]; subst.
        have:= HB _ _ _ _ H1 H4 => -[??]; subst.
        repeat split => //.
      - inversion H0 => // ; destruct a => //; move: H5 => [_ ?]; subst.
        by have:= expandedb_big_or_not_done H2.
  Qed.
End valid_state.
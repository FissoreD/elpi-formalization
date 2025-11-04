From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run.

Section valid_state.
  Variable u : Unif.
  
  Fixpoint base_and s :=
    match s with
    | And (CallS _ _ | CutS) r r1 => (r == r1) && base_and r1 (* should also say something about the program *)
    | Top => true
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

  Fixpoint is_and A := 
    match A with
    | And Top _ _ => false
    | And _ _ A => is_and A
    (* | And A _ B => if success A then is_and B else bbAnd A *)
    | Bot | Top | OK => true
    | _ => false
    end.

  Definition is_or A := 
    match A with
    | OK | Bot | Or _ _ _ | CutS | CallS _ _ => true
    | _ => false
    end.

  Lemma base_and_is_or {A}: base_and A -> is_or A = false.
  Proof. case: A => //. Qed.

  Fixpoint valid_state s :=
    match s with
    | CutS | CallS _ _ | OK | Bot | Top => true
    | Dead => false
    | Or A _ B => 
      if is_dead A then valid_state B
      else valid_state A && (bbOr B)
    | And A B0 B => 
      [&& is_or A, valid_state A, (is_and B && (A != Top)),
        if success A then valid_state B 
        else (B0 == B)
        (* We should notice that in (OK \/ KO) /\ OK the reset point is forced to be cut *)
        (* failed_state_to_list needs this if condition *)
        & (if success A || failed A then bbAnd B0 else base_and B0)]
    end.

  Goal forall x r, (valid_state (And CutS x r)) -> is_ko r = false.
  Proof.
    move=> x r/=/and3P[_ /eqP->].
    elim: r => //-[]//.
  Qed.


  Lemma valid_state_dead {A} : is_dead A -> valid_state A = false.
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[]dA dB.
      rewrite HA// dA HB//andbF//.
    move=> A HA Bo ? B HB/=dA.
    rewrite HA// andbF//.
  Qed.

  Lemma base_and_is_and {A}: base_and A -> is_and A.
  Proof. elim: A => //=[][]//.
    move=> p t _ B0 _ B HB/=/andP[_]//.
    move=> _ B0 _ B HB/=/andP[_]//.
  Qed.

  Lemma base_and_ko_is_and {A}: base_and_ko A -> is_and A.
  Proof. elim: A => //-[]// _ B0 _ B HB/= /and3P[]//. Qed.

  Lemma bbAnd_is_and {A}: bbAnd A -> is_and A.
  Proof. rewrite/bbAnd => /orP[/base_and_is_and|/base_and_ko_is_and]//. Qed.

  Lemma is_and_cutl {A}: is_and A -> is_and (cutl A).
  Proof. elim: A => // -[]// A s B _ C0 _ C HB/= aC; case: ifP => dA; auto. Qed.

  Lemma is_or_cutl {A}: is_or A -> is_or (cutl A).
  Proof. elim: A => //A HA s B HB/=; rewrite fun_if/=if_same//. Qed.

  Lemma is_or_big_or {p s t}: is_or (big_or u p s t).
  Proof. rewrite /big_or; case: F => //-[]//. Qed.


  Lemma valid_state_dead1 {A} : valid_state A -> is_dead A = false.
  Proof. apply: contraPF => /valid_state_dead->//. Qed.

  Lemma base_and_valid {A} : base_and A -> valid_state A.
  Proof.
    elim A => //; clear => A HA B +; rewrite /base_or_aux //=; case: A HA => //=.
      move=> p a _ + A + /andP [] /eqP H ; rewrite H; subst.
      move=> _ H H1; rewrite H1//eqxx base_and_is_and//.
    move=> _ H _ _ /andP[/eqP<-] H1; rewrite H1//eqxx base_and_is_and//.
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
    + move=> []//a l; rewrite /base_or_aux //= base_and_big_and eqxx//.
      case: a => //.
    + by move=> [[s r] rs] IH r1 /=; rewrite IH base_and_big_and.
  Qed.

  Lemma valid_state_big_or {pr s t} : valid_state (big_or u pr s t).
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
    + move=> s; case: s => //[p t|] Ha B0 HB0 B HB /=/andP[/eqP->]bB; rewrite eqxx base_and_is_and bB//.
    elim: B => //.
    + move=> A HA s B HB /= /andP [bA bB].
      rewrite HB//HA?base_and_ko_base_or_aux_ko// /bbOr bB orbT if_same//base_and_ko_is_and//orbT//.
    + move=> [] // HA B0 _ B HB /= /and3P[] bB0 /eqP <-.
      rewrite /bbAnd bB0 eqxx base_and_ko_is_and// orbT//.
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

  (* Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else ((B02 == B2))) ->
      bbAnd B02 ->
        valid_state B2.
  Proof. case: success => //; move=>/eqP->. apply: bbAnd_valid. Qed. *)

  Lemma base_and_cutl {B0}:
    base_and B0-> base_and_ko (cutl B0).
  Proof.
    elim: B0 => //s.
    case: s => //=[_ _|] _ B0 HB0 B HB/=/andP[/eqP<-]bB; rewrite HB0// eqxx//.
  Qed.

  Lemma base_ko_and_cutl {B0}:
    base_and_ko B0-> base_and_ko (cutl B0).
  Proof. elim: B0; move=> //[]// _ B0 _ B HB/=/and3P[_ /eqP->]/HB->; rewrite eqxx//. Qed.

  Lemma bbAnd_cutl{B0}:
    bbAnd B0 -> base_and_ko (cutl B0).
  Proof. by move=>/orP[/base_and_cutl|/base_ko_and_cutl]//. Qed.

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

  Lemma cutl_atop {A}: A != Top -> cutl A != Top.
  Proof. by case: A=> //=*; case: ifP. Qed.

  Lemma valid_state_cut {A}: valid_state A -> valid_state (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB => /=.
      case: ifP => //[dA vB| dA /andP[vA bB]]/=.
        rewrite dA HB//.
      rewrite is_dead_cutl dA HA// bbOr_cutr//.
    move=> A HA B0 HB0 B HB /= /and5P[oA vA /andP[aB aT]].
    rewrite success_cut.
    case: ifP => //=[sA vB bB0|sA/eqP->{B0 HB0}].
      rewrite is_or_cutl// HA// HB// is_and_cutl///bbAnd bbAnd_cutl//orbT cutl_atop//.
    rewrite eqxx is_or_cutl// is_and_cutl// HA//=.
    case: ifP => [fA bB|fA bB].
      by rewrite failed_cut///bbAnd bbAnd_cutl// orbT cutl_atop.
    rewrite failed_success_cut success_cut sA/=.
    by rewrite /bbAnd base_and_cutl//orbT cutl_atop.
  Qed.

  (* Lemma simpl_valid_state_and {A B0 B}: valid_state (And A B0 B) -> 
    valid_state A /\ valid_state B.
  Proof.
    move=>/= /and3P[]// -> VB bbB0.
    by rewrite (valid_state_compose_and VB bbB0).
  Qed. *)

  Lemma is_or_expand {s A r}: is_or A -> expand u s A = r -> is_or (get_state r).
  Proof.
    move=> + <-; clear r. 
    elim: A s => //.
    - move=> p t//=s; rewrite is_or_big_or//.
    - move=> A HA s B HB s1/= _; case: ifP => dA; case: expand => //.
  Qed.

  Lemma expand_top_right {s1 A r}: expand u s1 A = r -> get_state r <> Top.
  Proof. 
    move=><-; clear r; elim: A s1 => //.
    - move=> p t s1; rewrite /=/big_or; case: F=>//[[]]//.
    - move=> A HA s B HB s1/=.
      case: ifP => //.
        rewrite get_state_Or//.
      case: expand => //.
    - move=> A HA B0 _ B HB s1/=.
      case: expand => //?; rewrite get_state_And//.
  Qed.

  Lemma is_and_expand {s A r}: is_and A -> expand u s A = r -> is_and (get_state r).
  Proof.
    move=> + <-; clear r. 
    elim: A s => //.
    move=> A HA B0 _ B HB s1/= aB.
    case eA: expand => //=[ A'| A'|A'|A']; have /=H := (expand_top_right eA); try by destruct A, A'.
    rewrite get_state_And/=.
    have {}aB : is_and B by destruct A.
    rewrite (HB _ aB).
    case: ifP; case hA': A' {eA} H => //=; case: ifP => //.
  Qed.

  Lemma base_and_bbAnd {A}: base_and A -> bbAnd A.
  Proof. rewrite/bbAnd=>->//. Qed.

  Lemma expand_atop {A s1 r}: A != Top -> expand u s1 A = r -> get_state r != Top.
  Proof.
    move=> +<-.
    case: A => //=.
    - move=> p c; rewrite/big_or; case: F => []//[]//.
    - move=> A s2 B _; case: ifP; by case X: expand.
    - move=> A B0 B _; case: expand => //*; by case: expand.
  Qed.

  Lemma valid_state_expand {s A r}:
    valid_state A -> expand u s A = r -> valid_state (get_state r).
  Proof.
    move=>+<-; clear r.
    elim: A s => //; try by move=> s r // *; subst.
    + by move=> ? ? ?? *;subst => //=; rewrite valid_state_big_or.
    + move=> A IHA s B IHB s1/=.
      case:ifP => //[dA vB|dA/andP[vA bB]].
        rewrite get_state_Or/=dA IHB//.
      have /= := IHA s1 vA.
      case X: expand => //= H; rewrite (expand_not_dead _ dA X) H//bbOr_cutr//.
    + move=> A HA B0 _ B HB s1 /=/and5P[oA vA /andP[aB aT]].
      case: ifP => [sA vB /= bB0 | sA /eqP->]/=.
        rewrite succes_is_solved//=.
        have:= HB (get_substS s1 A) vB.
        case X: expand => //[C|C|C|C]/=vC; try by rewrite sA (is_and_expand aB X) vA vC oA//aT.
        rewrite is_or_cutl//valid_state_cut//(is_and_expand aB X) success_cut// vC sA //= /bbAnd bbAnd_cutl//orbT//cutl_atop//.
      case: ifP => [fA bB|fA bB].
        by rewrite failed_expand//=vA sA eqxx /= bB oA fA aB//aT.
      have:= HA s1 vA.
      case X: expand => //[A'|A'|A'|A']/=vA'; last first;
       [|by rewrite (is_or_expand oA X) aB//vA' base_and_valid//eqxx /bbAnd bB !if_same (expand_atop aT X)..].
      have [? sA']:= expand_solved_same _ X; subst.
      congruence.
  Qed.

  Lemma valid_state_big_or_aux {pr s l} : valid_state (big_or_aux pr s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_state_big_and // full_expanded_big_and.
    + move=> _ r l IH s.
      rewrite valid_state_big_and bbOr_big_or_aux IH if_same//.
  Qed.

  (* Lemma valid_state_expanded {s1 A r b}:
    valid_state A ->  expandedb u s1 A r b -> valid_state (get_state_exp r).
  Proof.
    move=> + H.
    elim: H; clear.
    + move=> s1 s2 A B HA VA /=; apply: valid_state_expand VA HA.
    + move=> s A B HA VA; apply: valid_state_expand VA HA.
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
    + move=> s1 s2 r A B b HA _ IH VA; apply (IH (valid_state_expand VA HA)).
  Qed. *)

  Lemma next_alt_aux_base_and {A} b: base_and A -> next_alt b A = Some (A).
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

  Lemma next_alt_top {A B b}:
    next_alt b A = Some (B) -> ((A = Top) * (B = Top)) \/ ((A <> Top) /\ (B <> Top)).
  Proof.
    case: A b => //=.
    - by move=> b; case: ifP => // _[<-]; right.
    - by move=> b // [<-]; left.
    - by move=> p c _ [<-]; right => //.
    - by move=> _ [<-]; right.
    - move=> ????/=.
      case: ifP; case: next_alt => //; try by move=> ? ? [<-]; right.
      by case: ifP => // ??; case: next_alt => //A [<-]; right.
    - move=> ????/=; case: ifP => // _.
      case: ifP => // _.
        do 2 case: next_alt => //[]?.
        by move=> [<-]/=; right.
      case: ifP => // _.
        case: next_alt => //[?[<-]|].
          by right.
        do 2 case: next_alt => //?.
        by move=> [<-]; right.
      by move=> [<-]; right.
  Qed.

  Lemma is_and_or_next_alt {A B b}: 
    valid_state A ->
      next_alt b A = Some (B) -> ((is_or A = is_or B) * (is_and A = is_and B)).
  Proof.
    elim: A  B b => //=.
    - move=> /= B b; case: ifP => // _ _ [<-]//.
    - move=> B b _ [<-]//.
    - move=> p c B _ _ [<-]//.
    - move=> ? _ _ [<-]//.
    - move=> A HA s B HB  C b/=.
      case:ifP => //[dA vB|dA vA].
        case: next_alt => //=D[<-]//.
      case: next_alt => [D [<-]|]//.
      case: ifP => //; case: next_alt => // D _ [<-]//.
    - move=> A HA B0 _ B HB/= C b /and5P[oA vA /andP[aB aT]].
      case: ifP => //=[sA vB bB0|sA /eqP->].
        rewrite (valid_state_dead1 vA) success_failed//.
        case nB: next_alt => //[D|].
          move=>[<-]//=; rewrite (HB _ _ vB nB)//.
        case X: next_alt => //[A'].
        case W: next_alt => //[B0'][<-]//=.
        have:= next_alt_same_structure X.
        destruct A, A' => //=.
        move: bB0 => /orPT[] /[dup] bB.
          move=> /(next_alt_aux_base_and false); rewrite W.
          move=> [->]; rewrite (base_and_is_and bB)//.
        move=> /(next_alt_aux_base_and_ko false); rewrite W//.
      rewrite (valid_state_dead1 vA).
      case: ifP => [fA bB|fA bB].
        case nA: next_alt => //[D].
        case nB: next_alt => //[B'].
        move=> [<-]/=.
        have [H|[H1 H2]]:= next_alt_top nA.
          rewrite !H//.
        move: bB => /orPT[] /[dup] bB.
          move=> /(next_alt_aux_base_and false); rewrite nB => -[?]; subst.
          have:= next_alt_same_structure nA.
          destruct A, D => //.
        move=> /(next_alt_aux_base_and_ko false); rewrite nB//.
      move=> [<-]/=.
      by destruct A => //.
  Qed.

  (* Lemma next_alt_failed {A D}: valid_state A ->
    failed A -> next_alt A = Some D -> failed D = false.
  Proof.
    elim: A D => //=.
    - move=> A HA s B HB D/=.
      case: ifP => dA v f.
        case X: next_alt => //[B'][<-]/=; rewrite dA HB//.
      case X: next_alt => //[A'|].
        move=> [<-]/=; rewrite (next_alt_dead X).
        apply: 
      case : ifP => //dB; case Y: next_alt => //=[B'][<-]/=.
      rewrite is_dead_dead.
      move /andP: v => -[vA] /orP[]bB; last first.
        rewrite next_alt_aux_base_or_ko// in Y.
      admit.
    - move=> A HA B0 HB0 B HB D /and5P[_ vA _].
      case: ifP => /=[sA vB bB0|sA/eqP-> bB0].
        rewrite success_failed//=success_is_dead// => fB.
        case X: next_alt => //[B'|][<-]/=.
          rewrite sA/=success_failed//=.
          apply: HB => //.
        rewrite success_clean_success_failed//=.

        rewrite success_is_dead. *)

  Lemma next_alt_atop {A A' b}: A != Top -> next_alt b A = Some A' -> A' != Top.
  Proof.
    case: A => //=.
    - case: ifP => //= _ _ [<-]//.
    - move=> p c _ []//<-//.
    - move=> _ [<-]//.
    - move=> A s B _.
      case: ifP => dA.
        by case X: next_alt => //-[<-].
      case: next_alt => //.
        move=> ?[<-]//.
      case: ifP => //.
      case: next_alt => // ? _ [<-]//.
    - move=> A B0 B _; case: ifP => //_.
      case: ifP => //_.
        (do 2 case : next_alt) => // ?? [<-]//.
      case: ifP => [|_[<-]]//.
      case: next_alt => [? _ [<-]|]//.
      by (do 2 case: next_alt) => // ?? _ [<-].
  Qed.

  Lemma valid_state_next_alt {A B b}: 
    valid_state A -> next_alt b A = Some (B) 
    -> valid_state B.
  Proof.
    elim: A  B b => //=.
    + move=> B b _; case: ifP => // _ [<-]//.
    + move=> B _ _ [<-]//.
    + move=> p c B _ _ [<-]//.
    + move=> B _ _ [<-]//.
    + move=> A HA s B HB  C b/=.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        case X: next_alt => //[D] [<-]/=.
        rewrite dA (HB _ _ vB X)//.
      case X: next_alt => [D|].
        move=>[<-]/=; rewrite bbOr_valid// bB (HA _ _ vA X) if_same//.
      case: ifP => //dB.
      case Y: next_alt => [D|]//[<-]/=; rewrite is_dead_dead (HB _ _ _ Y)//bbOr_valid//.
    + move=> A HA B0 HB0 B HB  C b /=/and5P[oA vA /andP[aB aT]].
      case: ifP => /=[sA vB bB0|sA /eqP?]; subst.
        rewrite success_is_dead//success_failed//.
        case X: next_alt => [D|].
          move=>[<-]/=; rewrite vA sA oA/= (HB _ _ vB X)//-(is_and_or_next_alt vB X)aB aT//.
        case Y: next_alt => //=[A'].
        move: bB0 => /orPT[]/[dup]bB; last first.
          move=> /(next_alt_aux_base_and_ko false) -> //.
        move=> /next_alt_aux_base_and->[<-]/=.
        by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA Y) -(is_and_or_next_alt vA Y) oA base_and_is_and //!if_same// (next_alt_atop aT Y).
      case: (ifP (is_dead _)) => //dA.
      case: ifP => fA bB; last first.
        move=> [<-]/=; rewrite oA aB vA sA eqxx /bbAnd bB if_same//aT//.
      case X: next_alt => [D|]//.
      move: bB => /orPT[]/[dup]bB; last first.
        move=> /(next_alt_aux_base_and_ko false) -> //.
      move=> /next_alt_aux_base_and->[<-]/=.
      by rewrite (base_and_valid bB) eqxx /bbAnd bB/= (HA _ _ vA X) -(is_and_or_next_alt vA X) oA base_and_is_and //!if_same// (next_alt_atop aT X).
    Qed.

  Lemma valid_state_run {s1 A s2 B b}:
    valid_state A -> runb u s1 A s2 B b -> (B = dead1 B) + valid_state B.
  Proof.
    move=> + H; elim: H; clear => //=.
    + move=> s1 s2 A B sA _ <- vA.
      case X: next_alt => [B'|]/=.
        by rewrite (valid_state_next_alt vA X); auto.
      by rewrite dead2; auto.
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_state_expand vA eA).
    + move=> s1 s2 r A B n eA rB IH vA; subst.
      apply: IH (valid_state_expand vA eA).
    + move=> s1 s2 A B r n fA + rB + vA; subst.
      move=> /(valid_state_next_alt vA) vB /(_ vB)//.
    + by move => *; rewrite dead2; auto.
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
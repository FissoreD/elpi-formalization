From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module B.
  Fixpoint base_and s :=
    match s with
    | And (TA _) r r1 => (big_and r == r1) && base_and r1
    | OK => true
    | _ => false
    end.

  Lemma base_and_dead {A}: base_and A -> is_dead A = false.
  Proof. case: A => // -[]//=. Qed.

  Lemma base_and_big_and A: base_and (big_and A).
  Proof. by elim: A => // -[|t] l /= ->; rewrite eq_refl. Qed.

  Fixpoint base_or_aux s :=
    match s with
    | Or l _ r => base_and l && (base_or_aux r)
    | t => base_and t
    end.

  Definition base_and_ko s :=
    match s with
    | And KO r r1 =>
      [&& (big_and r == r1) & base_and r1]
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
    | Or l _ r => base_and_ko l && (base_or_aux_ko r)
    | t => base_and_ko t
    end.

  Definition bbOr B := base_or_aux B || base_or_aux_ko B. 

  Section specs.
    Lemma spec_base_and A:
      reflect (exists X, big_and X = A) (base_and A).
    Proof.
      case bA: base_and; constructor.
        case: A bA => //=; first by exists [::].
        move=> []//= A l t /andP[/eqP? bB]; subst.
        by exists (A :: l).
      move=> [x ?]; subst.
      by rewrite base_and_big_and in bA.
    Qed.

    Lemma base_or_aux_big_or s l:
      base_or_aux (big_or s l).
    Proof.
      elim: l s => //=; clear.
      + by case => //= _ l; rewrite eqxx base_and_big_and.
      + by move=> [s r] rs IH r1 /=; rewrite IH base_and_big_and.
    Qed.

    Lemma bbOr_big_or s l: bbOr (big_or s l).
    Proof.
      rewrite/bbOr.
      case: base_or_aux_ko; rewrite ?orbT//orbF base_or_aux_big_or//.
    Qed.

    Lemma spec_base_or_aux A:
      reflect (exists X Y, big_or X Y = A) (base_or_aux A).
    Proof.
      case bA: base_or_aux; constructor; last first.
        move=> [X[Y H]]; subst.
        by rewrite base_or_aux_big_or in bA.
      pose head := RCallable_Kp (IKp 1).
      elim: A bA => //=; first by exists [::],[::].
        move=> A _ s B HB /andP[/spec_base_and[L <-]] /HB [X [Y <-]].
        by eexists L, ((s, {|head := head; premises := X|}) :: Y) => //=.
      move=> []//= A _ l t H1 /andP[/eqP?] /spec_base_and[x?]; subst.
      by exists  (A::l), [::].
    Qed.

    Lemma base_and_base_and_ko_cutr {B} : base_and B -> base_and_ko (cutr B).
    Proof. 
      by elim: B => // A; case: A => //[p c|] _ B0 B HB /=/andP[/eqP H1 H2]; rewrite HB// H1 eqxx.
    Qed.
    
    Lemma spec_base_and_ko A:
      reflect (exists X, cutr (big_and X) = A) (base_and_ko A).
    Proof.
      case bA: base_and_ko; constructor.
        case: A bA => //=; first by exists [::].
        by move=> []//= l t /andP[/eqP <-]; exists (cut :: l).
      move=> [x ?]; subst.
      by rewrite base_and_base_and_ko_cutr//base_and_big_and in bA.
    Qed.

    Lemma base_or_base_or_ko_cutr {B}: base_or_aux B -> base_or_aux_ko (cutr B).
    Proof.
      elim: B => //.
      + move=> A IHA s B IHB /= /andP [] /base_and_base_and_ko_cutr -> /IHB ->//.
      + move=> a; case: a => //=[_ _|] _ B C HC /andP [] /eqP /[subst1] hC;
        rewrite base_and_base_and_ko_cutr//eqxx//.
    Qed.

    Lemma spec_base_or_aux_ko A:
      reflect (exists X Y, cutr (big_or X Y) = A) (base_or_aux_ko A).
    Proof.
      case bA: base_or_aux_ko; constructor; last first.
        move=> [X[Y H]]; subst.
        by rewrite base_or_base_or_ko_cutr//base_or_aux_big_or in bA.
      pose head := RCallable_Kp (IKp 1).
      elim: A bA => //=; first by exists [::],[::].
        move=> A _ s B HB /andP[/spec_base_and_ko[X?]] /HB [Y[Z H]]; subst.
        by eexists X, ((s, {|head := head; premises := Y|}) :: Z) => //=.
      move=> []//= _ l t H1 /andP[/eqP?]; subst.
      by exists  (cut::l), [::].
    Qed.

    Lemma base_and_ko_base_and_ko_cutr {B} : base_and_ko B -> base_and_ko (cutr B).
    Proof. by elim: B => // -[]// _ l B HB /=/andP[/eqP<- H]; rewrite cutr2 eqxx//. Qed.

    Lemma base_or_ko_cutr {B}: base_or_aux_ko B -> base_or_aux_ko (cutr B).
    Proof.
      elim: B => //.
        move=> A HA s B HB /= /andP[bA bB].
        rewrite HB//base_and_ko_base_and_ko_cutr//.
      by move=> [] //= _ B0 B HB /andP[/eqP H1 H2]; rewrite base_and_ko_base_and_ko_cutr// -H1 cutr2 eqxx.
    Qed.

    Lemma bbOr_cutr {B}: bbOr B -> bbOr (cutr B).
    Proof.
      rewrite/bbOr.
      move=>/orP[/base_or_base_or_ko_cutr|/base_or_ko_cutr]->; rewrite orbT//.
    Qed.
  End specs.  
End B.

Lemma spec_bbOr A:
  reflect (exists X Y, let x := (big_or X Y) in x = A \/ cutr x = A) (B.bbOr A).
Proof.
  case X: B.bbOr; constructor.
    move/orP: X => [/B.spec_base_or_aux|/B.spec_base_or_aux_ko][?[??]]/=; subst; repeat eexists; eauto.
  move=> [Y [Z]]/=[]?; subst;
  by rewrite !(B.bbOr_cutr,B.bbOr_big_or) in X.
Qed.

(*BEGIN*)
Section valid_tree.
  Variable u : Unif.
  Variable p : program.

(*SNIP: valid_tree*)
  Fixpoint valid_tree s :=
    match s with
    | TA _ | OK | KO => true
    | Dead => false
    | Or A _ B => 
      if is_dead A then valid_tree B
      else valid_tree A && (B.bbOr B)
    | And A B0 B => 
      valid_tree A &&
        if success A then valid_tree B 
        else B == big_and B0
    end.
(*ENDSNIP: valid_tree*)

  Goal forall x r , (valid_tree (And (TA cut) x r)) -> is_ko r = false.
  Proof. move=> x r/= /eqP->; rewrite is_ko_big_and//. Qed.

  Lemma is_dead_valid_tree {A} : is_dead A -> valid_tree A = false.
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[]dA dB.
      rewrite HA// dA HB//andbF//.
    move=> A HA Bo B HB/=dA.
    rewrite HA// andbF//.
  Qed.

  Lemma valid_tree_is_dead {A} : valid_tree A -> is_dead A = false.
  Proof. apply: contraPF => /is_dead_valid_tree->//. Qed.

  Lemma valid_tree_big_and l : valid_tree (big_and l).
  Proof. elim: l => //=. Qed.

  Lemma valid_tree_big_and_cutr l : valid_tree (cutr (big_and l)).
  Proof. elim: l => //=. Qed.

  Lemma valid_tree_big_or s l : valid_tree (big_or s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_tree_big_and//.
    + by move=> _ b l H s; rewrite is_dead_big_and valid_tree_big_and B.bbOr_big_or.
  Qed.

  Lemma valid_tree_big_or_cutr s l : valid_tree (cutr (big_or s l)).
  Proof.
    elim: l s => [|[]] //=.
    + by move=> s; rewrite valid_tree_big_and_cutr.
    + by move=> _ r l IH s; rewrite IH valid_tree_big_and_cutr B.bbOr_cutr (if_same, B.bbOr_big_or).
  Qed.


  Lemma valid_tree_backchain {pr s t} : valid_tree (backchain u pr s t).
  Proof.
    rewrite/backchain; case: F => //[[s1 r1] rs]/=.
    apply: B.bbOr_big_or.
  Qed.

  Lemma bbOr_valid {B}:
    B.bbOr B -> valid_tree B.
  Proof.
    move=> /spec_bbOr[X[Y /=[]<-]].
      apply: valid_tree_big_or.
    apply: valid_tree_big_or_cutr.
  Qed.

  Lemma valid_tree_cut {A}: success A -> valid_tree A -> valid_tree (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB => /=.
      case: ifP => //[dA sB vB| dA sA /andP[vA bB]]/=.
        rewrite dA HB//.
      rewrite is_dead_cutl dA HA// B.bbOr_cutr//.
    move=> A HA B0 B HB /= /andP[sA sB] /andP[vA].
    rewrite sA/= => vB.
    rewrite success_cut sA HA//HB//=.
  Qed.

  Lemma valid_tree_step s A r:
    valid_tree A -> step u p s A = r -> valid_tree r.2.
  Proof.
    move=>+<-; clear r.
    elim: A s => //; try by move=> s r // *; subst.
    + by move=> /= []//=>; rewrite valid_tree_backchain.
    + move=> A IHA s B IHB s1/=.
      case:ifP => //[dA vB|dA/andP[vA bB]]/=.
        by rewrite IHB//dA.
      have /= := IHA s1 vA.
      case X: step => [[]A']//=->; rewrite (step_not_dead dA X)//B.bbOr_cutr//.
    + move=> A HA B0 B HB s1 /=/andP[vA].
      case: ifP => [sA vB /= | sA]/=.
        rewrite success_step//=.
        have {HB} := HB (get_substS s1 A) vB.
        case X: step => //[[]C]/=vC; try by rewrite sA vA vC.
        rewrite success_cut sA/= vC valid_tree_cut//.
      move=> /eqP -> {B HB}.
      have:= HA s1 vA.
      case X: step => //[[]A']/=vA'; only 1-3: by rewrite eqxx vA' valid_tree_big_and if_same.
      have [? sA']:= step_solved_same X; subst.
      congruence.
  Qed.

  Lemma valid_tree_next_alt {A B b}: 
    valid_tree A -> next_alt b A = Some (B) 
    -> valid_tree B.
  Proof.
    elim: A  B b => //=.
    + move=> B b _; case: ifP => // _ [<-]//.
    + move=> c B _ _ [<-]//.
    + move=> A HA s B HB  C b/=.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        case X: next_alt => //[D] [<-]/=.
        rewrite dA (HB _ _ vB X)//.
      case X: next_alt => [D|].
        move=>[<-]/=; rewrite bB ; rewrite bbOr_valid// (HA _ _ vA X) if_same//.
      case Y: next_alt => [D|]//[<-]/=; rewrite is_dead_dead (HB _ _ _ Y)//bbOr_valid//.
    + move=> A HA l B HB  C b /= /andP[vA].
      case: ifP => /=[sA vB|sA]; subst.
        case X: next_alt => [D|].
          move=>[<-]/=; rewrite vA sA/= (HB _ _ vB X)//.
        case Y: next_alt => //=[A'].
        by move=> [<-]/=; rewrite (HA _ true)//= valid_tree_big_and eqxx !if_same.
      move=> /eqP->{B HB}.
      case: ifP => fA; last first.
        by move=> [<-]/=; rewrite vA sA eqxx.
      case X: next_alt => [D|]//=.
      by move=> [<-]/=; rewrite (HA _ false)//= eqxx valid_tree_big_and !if_same.
    Qed.

  Lemma valid_tree_run {s1 A s2 B b}:
    valid_tree A -> run u p s1 A s2 B b -> (B = dead B) + valid_tree B.
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
(*END*)

End valid_tree.
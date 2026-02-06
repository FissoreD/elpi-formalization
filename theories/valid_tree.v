From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Module B.
  Fixpoint base_and s :=
    match s with
    | And (TA _) r r1 => (big_and r == r1) && base_and r1
    | OK => true
    | _ => false
    end.

  Lemma base_and_big_and A: base_and (big_and A).
  Proof. by elim: A => // -[|t] l /= ->; rewrite eq_refl. Qed.

  Fixpoint base_or s :=
    match s with
    | Or (Some l) _ r => base_and l && (base_or r)
    | t => base_and t
    end.

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

    Lemma base_or_big_or s l:
      base_or (big_or s l).
    Proof.
      elim: l s => //=; clear.
      + by case => //= _ l; rewrite eqxx base_and_big_and.
      + by move=> [s r] rs IH r1 /=; rewrite IH base_and_big_and.
    Qed.

    Lemma spec_base_or A:
      reflect (exists X Y, big_or X Y = A) (base_or A).
    Proof.
      case bA: base_or; constructor; last first.
        move=> [X[Y H]]; subst.
        by rewrite base_or_big_or in bA.
      elim: A bA => //=; first by exists [::],[::].
        move=> A _ s B HB /andP[/spec_base_and[L <-]] /HB [X [Y <-]].
        by eexists L, ((s, X) :: Y) => //=.
      move=> []//= A _ l t H1 /andP[/eqP?] /spec_base_and[x?]; subst.
      by exists  (A::l), [::].
    Qed.
  End specs.  
End B.

Notation spec_base_or := B.spec_base_or.

(*BEGIN*)
Section valid_tree.
  Variable u : Unif.
  Variable p : program.

(*SNIP: valid_tree*)
  Fixpoint valid_tree A :=
    match A with
    | TA _ | OK | KO => true
    | Or None _ B => valid_tree B
    | Or (Some A) _ B => valid_tree A && 
          ((B == KO) || B.base_or B)
    | And A B0 B => valid_tree A &&
        if success A then valid_tree B 
        else B == big_and B0
    end.
(*ENDSNIP: valid_tree*)

  Lemma valid_tree_big_and l : valid_tree (big_and l).
  Proof. elim: l => //=. Qed.

  Lemma valid_tree_big_or s l : valid_tree (big_or s l).
  Proof.
    elim: l s => [|[]] //=.
    + move=> s; rewrite valid_tree_big_and//.
    + by move=> _ b l H s; rewrite valid_tree_big_and/= B.base_or_big_or orbT.
  Qed.

  Lemma valid_tree_cut {A}: success A -> valid_tree A -> valid_tree (cutl A).
  Proof.
    elim_tree A.
      move=> /=sA /andP[vA bB]; rewrite HA//.
      by rewrite success_or_None.
    move=>/[!success_and]/= /andP[sA sB] /andP[vA].
    rewrite sA/= => vB.
    rewrite success_cut sA HA//HB//=.
  Qed.

  Lemma valid_tree_step s sv A r:
    valid_tree A -> step u p sv s A = r -> valid_tree r.2.
  Proof.
    move=>+<-; clear r.
    elim_tree A s sv => /=.
    + by case: t => [|t]//=; rewrite push/=; case: bc => [_ []]//=>; rewrite push//= B.base_or_big_or orbT.
    + move=> /andP[vA bB]; rewrite !push/= HA//=; case: ifP => //.
    + by move=> vB; rewrite !push /=; apply: HB.
    + move=> /andP[vA].
      rewrite !push.
      case: ifP => [sA vB /= | sA]/=.
        have {HB} := HB (get_subst s A) sv vB.
        case X: step => //[[?[]]C]/=vC; try by rewrite sA vA vC.
        rewrite success_cut sA/= vC valid_tree_cut//.
      move=> /eqP -> {B HB}.
      have:= HA s sv vA.
      case X: step => //[[sv' []]A']/=vA'; only 1-3: by rewrite eqxx vA' valid_tree_big_and if_same.
      have [? sA']:= step_success X; subst.
      congruence.
  Qed.

  Lemma valid_tree_next_alt A R b: 
    valid_tree A -> next_alt b A = Some R -> valid_tree R.
  Proof.
    elim_tree A R b => /=.
    + by case: R => //=; case: b => //.
    + by case: t => [|c]//= _ [<-]//.
    + move=> /andP[vA bB]; case nA: next_alt => [A'|]//=.
        by move=> [<-]/=; rewrite (HA A' b)//.
      case nB: next_alt => [B'|]//[<-]/=; apply/HB/nB.
      by move: bB => /orP[/eqP->|/spec_base_or[?[?]]]//<-; apply: valid_tree_big_or.
    + by move=> vB; case nB: next_alt => [B'|]//=[<-]/=; apply/HB/nB.
    + move=>/andP[vA].
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

  Lemma valid_tree_run s1 fv A s2 B b fv':
    valid_tree A -> run u p fv s1 A s2 B b fv' -> valid_tree (odflt A B).
  Proof.
    move=> + H.
    elim_run H => vA; only 2, 3: destruct r => //=.
    + case X: next_alt => [B'|]//=.
      by rewrite (valid_tree_next_alt vA X); auto.
    + by apply: IH (valid_tree_step vA eA).
    + by apply: IH (valid_tree_next_alt vA nA).
  Qed.
(*END*)

End valid_tree.
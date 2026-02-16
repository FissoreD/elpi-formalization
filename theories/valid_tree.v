From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Module B.
  Fixpoint base_andA s :=
    match s with
    | And (TA _) (x::xs) r1 => (big_andA x xs == r1) && base_andA r1
    | TA _ => true
    | _ => false
    end.

  Definition base_and s := (s == OK) || base_andA s.

  Lemma base_andA_big_andA x xs: base_andA (big_andA x xs).
  Proof. by elim: xs x => //=x xs->; rewrite eqxx. Qed.


  Lemma base_and_big_and A: base_and (big_and A).
  Proof. by rewrite/base_and/big_and; case: A => >; rewrite//base_andA_big_andA orbT. Qed.

  Fixpoint base_or s :=
    match s with
    | Or (Some l) _ r => base_and l && (base_or r)
    | t => base_and t
    end.

  Section specs.
    Lemma spec_base_and A:
      reflect (exists X, big_and X = A) (base_and A).
    Proof.
      rewrite /base_and/big_and.
      case: eqP => /=.
        by move=> ->; constructor; exists [::].
      move=> H.
      case bA: base_andA; constructor.
        case: A bA H => //=[a|]; first by exists [::a].
        move=> []//= A [|y ys] t//= /andP[/eqP? bB]; subst.
        move=> _.
        by exists (A::y::ys).
      move=> [x]; subst.
      case: x => //=; first by move=> ?; subst.
      move=> x xs ?; subst.
      by rewrite base_andA_big_andA in bA.
    Qed.

    Lemma base_or_big_or s l:
      base_or (big_or s l).
    Proof.
      elim: l s => //=; clear.
      + by move=> []//=a []//=x xs; rewrite/base_and/=eqxx base_andA_big_andA.
      + by move=> [s r] rs IH r1 /=; rewrite IH base_and_big_and.
    Qed.

    Lemma spec_base_or A:
      reflect (exists X Y, big_or X Y = A) (base_or A).
    Proof.
      case bA: base_or; constructor; last first.
        move=> [X[Y H]]; subst.
        by rewrite base_or_big_or in bA.
      elim: A bA => //=. 
        by exists [::],[::].
        by move=> A; eexists [::A],[::] => //.
        move=> l Hl s r Hr /andP[/spec_base_and[x?]]/Hr[y[z ?]]; subst.
        by exists x, ((s,y)::z).
      move=> l Hl s r Hr/spec_base_and[[]]//=x xs H.
      by exists (x::xs),[::] => //.
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
  Proof. case: l => //= + l; case: l => //=. Qed.

  Lemma valid_tree_big_or s l : valid_tree (big_or s l).
  Proof.
    case: l => //=; first by apply/valid_tree_big_and.
    by move=> [/=_ b] x; rewrite valid_tree_big_and B.base_or_big_or orbT.
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
    + by case: t => [|t]//=; rewrite push/=; case: bc => [_ []]//=-[]//= _ >; rewrite valid_tree_big_or.
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

  Lemma valid_tree_prune A R b: 
    valid_tree A -> prune b A = Some R -> valid_tree R.
  Proof.
    elim_tree A R b => /=.
    + by case: R => //=; case: b => //.
    + by case: t => [|c]//= _ [<-]//.
    + move=> /andP[vA bB]; case nA: prune => [A'|]//=.
        by move=> [<-]/=; rewrite (HA A' b)//.
      case nB: prune => [B'|]//[<-]/=; apply/HB/nB.
      by move: bB => /orP[/eqP->|/spec_base_or[?[?]]]//<-; apply: valid_tree_big_or.
    + by move=> vB; case nB: prune => [B'|]//=[<-]/=; apply/HB/nB.
    + move=>/andP[vA].
      case: ifP => /=[sA vB|sA]; subst.
        case X: prune => [D|].
          move=>[<-]/=; rewrite vA sA/= (HB _ _ vB X)//.
        case Y: prune => //=[A'].
        by move=> [<-]/=; rewrite (HA _ true)//= valid_tree_big_and eqxx !if_same.
      move=> /eqP->{B HB}.
      case: ifP => fA; last first.
        by move=> [<-]/=; rewrite vA sA eqxx.
      case X: prune => [D|]//=.
      by move=> [<-]/=; rewrite (HA _ false)//= eqxx valid_tree_big_and !if_same.
    Qed.

  Lemma valid_tree_run s1 fv A x b fv':
    valid_tree A -> runT u p fv s1 A (Some x) b fv' -> valid_tree (odflt A x.2).
  Proof.
    case: x => //= s []//= R.
    remember (Some _) as S eqn:HS.
    move=> + H.
    elim_run H s R HS => vA.
    + by move: HS => [_]; apply: valid_tree_prune.
    + by apply: IH (valid_tree_step vA eA).
    + by apply: IH (valid_tree_prune vA nA).
  Qed.
(*END*)

End valid_tree.
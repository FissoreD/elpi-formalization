From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Fixpoint clean_ca_suffix (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, clean_ca_goals_suffix bt xs) ::: (clean_ca_suffix bt tl)
  end
with clean_ca_goals_suffix bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (clean_ca_G_suffix bt hd) ::: (clean_ca_goals_suffix bt tl)
  end
with clean_ca_G_suffix bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut ((take (size ca - size bt) (clean_ca_suffix bt ca)))
  end.

Lemma clean_ca_suffix_cat {bt L1 L2}:
  clean_ca_suffix bt (L1 ++ L2) = clean_ca_suffix bt (L1) ++ clean_ca_suffix bt L2.
Proof. by elim: L1 bt L2 => //= [[s g] gs] IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_goals_suffix_cat {bt L1 L2}:
  clean_ca_goals_suffix bt (L1 ++ L2) = clean_ca_goals_suffix bt (L1) ++ clean_ca_goals_suffix bt L2.
Proof. by elim: L1 bt L2 => //= g gs IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_add_ca {bt1 L}:
  clean_ca_suffix bt1 (add_ca_deep bt1 L) = L
with clean_ca_goals_add_ca_goal bt1 x:
  clean_ca_goals_suffix bt1 (add_ca_deep_goals bt1 x) = x.
Proof.
  - by case: L => /=//-[s1 x] xs/=; rewrite clean_ca_add_ca clean_ca_goals_add_ca_goal.
  - case: x => /=//g gs; rewrite clean_ca_goals_add_ca_goal.
    case: g => //= a.
    congr ((cut _) ::: _).
    rewrite size_cat addnK clean_ca_suffix_cat clean_ca_add_ca.
    by rewrite take_size_cat// size_add_ca_deep.
    Guarded.
Qed.

Lemma s2l_clean_ca {A s xs bt1}:
  valid_state A ->
  state_to_list A s bt1 = xs ->
     clean_ca_suffix bt1 xs = state_to_list A s nilC.
Proof.
  move=> +<- {xs}.
  elim: A s bt1 => //=.
  - move=> A HA s B HB s1 bt1.
    case: ifP => [dA vB|dA /andP[vA bB]]; rewrite !add_ca_deep_empty1.
      by by rewrite state_to_list_dead//cat0s clean_ca_add_ca.
    by rewrite !add_ca_deep_cat/= !clean_ca_suffix_cat !clean_ca_add_ca.
  - move=> A HA B0 HB0 B HB s bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA /eqP->{B0 HB0}].
      rewrite !(success_state_to_list empty vA)//=.
      move /orPT: bB0 => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=!make_lB01_empty2 HB//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/= !make_lB01_empty2.
      rewrite !clean_ca_suffix_cat cats0.
      set m:= make_lB0 _ _.
      set n:= make_lB0 _ _.

      admit.
    case: ifP => [fA bB|fA bB].
      have:= [elaborate @s2l_size A s bt s nilC].
      case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
      move /orPT: bB => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/=!H/=.
      rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
      rewrite/make_lB0.
      admit.
    have:= [elaborate @s2l_size A s bt s nilC].
    case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
    have [hd H]:= base_and_state_to_list bB.
    rewrite !H/=!H/=.
    rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
    admit.
Admitted.

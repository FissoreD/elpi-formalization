From mathcomp Require Import all_ssreflect.
From det Require Import zify_ssreflect.

Goal forall {T: Type} (L1: list T) L2 N M,
  N <= size L2 ->
  size L2 <= size L1 ->
  take N (take (N - M) L1 ++ drop (N - M) L2) =
  take (size (take N L2) - M) (take N L1) ++
  drop (size (take N L2) - M) (take N L2).
Proof.
  move=> T L1 L2 N M H1 H2.
  rewrite take_cat.
  rewrite !size_take.
  case: ifP.
    by case:ifP; lia.
  case: ifP => H3.
    case:ifP => H4 H5.
      rewrite take_drop.
      have {}H3 : N - M <= N by lia.
      rewrite subnK//; f_equal.
      rewrite -take_min.
      by replace (minn (N - M) N) with (N - M) by lia.
    have H6 : N = size L2 by lia.
    subst.
    rewrite take_size -take_min.
    replace (minn _ _) with (size L2 - M) by lia; f_equal.
    have: (size L2 - (size L2 - M)) = size (drop (size L2 - M) L2).
      rewrite size_drop//.
    move=> ->.
    rewrite take_size//.
  case: ifP => H4 H5; last first; try by lia.
  have ? : N = size L2 by lia.
  subst.
  rewrite -take_min.
  replace (minn (size L2 - M) (size L2)) with (size L2 - M) by lia.
  f_equal.
  rewrite take_size take_oversize // size_drop; lia.
Qed.


    

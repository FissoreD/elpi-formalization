From mathcomp Require Import all_ssreflect.
From det Require Import elpi elpi_equiv.
From det Require Import tree t2l_prop tree_valid_state tree_prop.
From det Require Import check.

Definition is_det g := forall u s s' a',
  nur u s g nilC s' a' -> a' = nilC.

Lemma elpi_is_det {sP p c ign}: 
  check_program sP -> 
    check_callable sP [::] c Func = ty_ok (Func, ign) -> 
    is_det ((call p c):::nilC).
Proof.
  simpl in *.
  move=> H1 H2 u s s' a'.
  move=> /elpi_to_tree /(_ _ (CallS p c))/=.
  move=> /(_ _ isT erefl) [t1'[n [H3 H4]]].
  have := run_is_det H1 .
  move=> /(_ (CallS p c))/=.
  rewrite/det_tree /=.
  rewrite H2/= => /(_ isT).
  rewrite /check.is_det -H4.
  move=> /(_ _ _ _ _ _ H3) H.
  have:= valid_tree_run _ _ H3 => /(_ isT).
  move=> [].
    move=> ->.
    rewrite t2l_dead//is_dead_dead//.
  move=> vt1'.
  have ft1':= next_alt_None_failed H.
  have:= failed_next_alt_none_t2l vt1' ft1' H.
  by move=> ->.
Qed.



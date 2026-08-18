From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang mut_excl check_fo tree tree_prop.

(*SNIP: check_program *)
Definition check_program pr := mut_excl u pr && check_rules pr.
(*ENDSNIP: check_program *)

Lemma det_check_big_or pr c fv fv' r0 rs s1:
  check_program pr -> tm_is_det pr (deref s1 c) -> 
  bc u pr fv c s1 = (fv', r0 :: rs) ->
  det_tree pr (big_or r0.2 rs).
Proof.
  move=> /andP[ME CR] T B.
  apply/det_check_big_or_help.
    by have:= check_rulesP fv CR T; rewrite B//.
  have:= mut_exclP fv ME T; rewrite B//.
Qed.

(*SNIPT: det_tree_step *)
Lemma det_tree_step:
  forall pr v s1 A r, check_program pr -> det_tree pr A -> 
    step u pr v s1 A = r -> det_tree pr r.2.
(*ENDSNIPT: det_tree_step *)
Proof.
  move=> pr sv s1 A r H + <-; clear r.
  elim_tree A s1.
  - case: t => [|c]//=; rewrite !push/=.
    case bc: bc => //=[fv'[|[s0 r0]rs]]//= H1.
    apply: det_check_big_or bc => //.
    by apply: is_det_cder.
  - rewrite/= => /andP[fA]; rewrite !push/= HA//=.
    case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
    rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
    by move=> H1; rewrite (step_keep_cut _ H1).
  - by rewrite /=!push/=; apply/HB.
  - move=> /=/andP[dB].
    rewrite step_and/=.
    set sB:= step _ _ _ _ B.
    set sA:= step _ _ _ _ A.
    rewrite (fun_if (det_tree pr)).
    case SA: success.
      case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
        by rewrite det_tree_cutl//no_alt_cutl//= andbT.
      case n: nilA => // is_cb.
      case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
      by rewrite (step_keep_cut hcB) in hcsB.
    rewrite /= dB /=.
    case fA: (failed A).
      by rewrite /nilA /sA failed_step//= SA.
    case pA: (incomplete A).
      rewrite/nilA incpl_prune//= => /andP[+ ->]/=.
      by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
    by have:= succF_failF_paF SA fA pA.
Qed.

From det Require Import elpi elpi_equiv.

Notation runT' := (runT' u).
Notation runT := (runT u).
Notation runS := (runS u).

(*SNIPT: det_check_tree *)
Lemma det_check_tree: 
  forall s v p t, check_program p -> det_tree p t -> 
    forall r b v', runT p v s t r b v' -> r = Zero \/ exists s, r = (One s).
(*ENDSNIPT: det_check_tree *)
Proof.
  move=> s v p t H1 H2 r b v' R.
  elim_run R H1 H2.
  - eauto.
  - by move: NS; rewrite (det_check_prune_succ H2 sA).
  - by apply: IH (det_tree_step _ _ eA).
  - by apply: IH (det_tree_prune _ nA).
Qed.

(*SNIPT: is_detT *)
Definition is_detT p s t := 
  forall r, runT' p (fresh (vars_atom t `|` vars_sigma s)) s t r -> r = Zero \/ exists s, r = One s.
(*ENDSNIPT: is_detT *)

(*SNIPT: det_check_callT *)
Theorem det_check_callT:
  forall p s t, check_program p -> tm_is_det p t -> is_detT p s (call t).
(*ENDSNIPT: det_check_callT *)
Proof.
  move=> /= p t s cp td r [b[v' R]].
  by apply/det_check_tree/R => //.
Qed.

(*SNIPT: is_detS *)
Definition is_detS p s t := 
  forall r, runS p (fresh (vars_atom t `|` vars_sigma s)) (consA (s, consG (t, [::]) [::]) [::]) r -> r = None \/ exists s, r = Some (s, [::]).
(*ENDSNIPT: is_detS *)

(*SNIPT: det_check_callS *)
Theorem det_check_callS:
  forall p s t, check_program p -> tm_is_det p t -> is_detS p s (call t).
(*ENDSNIPT: det_check_callS *)
Proof.
  move=> /= p s t cp td [[s' [|x xs]]|] R; [by eauto| |by left].
  have [t'[{}R T2L]] := sound_many R.
  have:= det_check_callT cp td.
  rewrite /is_detT/runT'.
  move=> /(_ s (Many s' t'))[| |[sx]]; [eauto| inversion 1..].
Qed.


Print Assumptions  det_check_callT.
Print Assumptions  det_check_callS.

Section tail_cut.

  Definition tail_cut (r : R) :=
  match r.(premises) with List.nil => false | x :: xs => last x xs == cut end.
  
  Definition all_tail_cut p := (all tail_cut (rules p)).

  Lemma tail_cut_has_cut r: tail_cut r -> has_cut_seq (premises r).
  Proof. 
    rewrite/tail_cut; case: r => /= _; elim => //= -[|c] xs IH /eqP H//=.
    by case: xs H IH => //= x xs H ->//; rewrite H.
  Qed.

  Lemma all_tail_cut_all_cut p: all_tail_cut p -> all_cut p.
  Proof. by apply/sub_all => x H; apply/tail_cut_has_cut. Qed.

  Lemma last_has_cut a xs:
    last a xs == cut -> cut == a \/ has_cut_seq xs.
  Proof.
    elim: xs => //=; first by move=> /eqP->; left.
    move=> [|c]/= xs IH; auto.
    by case: a IH; auto => c1 IH H; apply: IH; destruct xs.
  Qed.

  Lemma cut_in_prem_tail_cut p: good_modes p.(sig) -> all_tail_cut p -> check_program p.
  Proof.
    move=> GM.
    rewrite/check_program.
    move=> H; apply/andP; split.
      by apply/all_cut_mut_excl/all_tail_cut_all_cut.
    move: H; apply:sub_all => -[hd bo].
    rewrite/tail_cut/=.
    rewrite/check_rule.
    case: tm_is_det => //=.
    elim: bo => //= x xs IH//=.
    destruct xs => //=[/eqP->|/[dup]{}/IH]//=->.
    destruct x; rewrite (orbT,andbT)//.
    by move=> /last_has_cut[]->; rewrite !orbT.
  Qed.
End tail_cut.

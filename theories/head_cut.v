From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl.
From det Require Import tree_prop_hard.

Definition add_head_cut sig r :=
  let pm := r.(premises) in 
  mkR r.(head) (if tm_is_det sig r.(head) then cut :: pm else pm).

Definition add_head_cuts s p := map (add_head_cut s) p.

Definition add_head_prog p := 
  {|sig:= p.(sig); rules:= add_head_cuts p.(sig) p.(rules) |}.

Lemma step_cut_add_cut u p fv0 s1 A fv1 R:
  step u p fv0 s1 A = (fv1, CutBrothers, R) ->
  step u (add_head_prog p) fv0 s1 A = (fv1, CutBrothers, R).
Proof.
  elim_tree A fv0 s1 fv1 R => /=.
  - by case: t => [|c]//; rewrite push.
  - by rewrite !push; case eA: step => [[fv []]]//=.
  - by rewrite !push; case eA: step => [[fv []]]//=.
  case: ifP => sA; case_step_tag X T => //=-[??]; subst.
    rewrite (HB _ _ _ _ X)//.
  rewrite (HA _ _ _ _ X)//.
Qed.

Lemma fr_add_cut_sf fv s x:
  (fresh_rule fv (add_head_cut s x)).1 = (fresh_rule fv x).1.
Proof.
  rewrite/fresh_rule !push/=; case: x => hd bo/=.
  by case: ifP; rewrite//=!push/=.
Qed.

Lemma frs_add_cut_sf s fv0 p:
  (fresh_rules fv0 (add_head_cuts s p)).1 = (fresh_rules fv0 p).1.
Proof.
  rewrite/add_head_cuts.
  elim: p fv0 => //= x xs IH fv; rewrite !push/=fr_add_cut_sf IH//.
Qed.

Lemma vur_add_cut_sf fv sig x:
  varsU_rule (fresh_rule fv (add_head_cut sig x)).2 =
  varsU_rule (fresh_rule fv x).2.
Proof.
  rewrite/varsU_rule /varsU_rprem/varsU_rhead/add_head_cut.
  case: x => /=hd bo; rewrite !head_fresh_rule/= !premises_fresh_rule/=.
  case: ifP; rewrite //=push//= => _; f_equal.
  by rewrite/vars_atoms/= fset0U.
Qed.

Lemma sel_add_cut_sf u hd m fv p s1 sig:
  (select u hd m (fresh_rules fv (add_head_cuts sig p)).2 s1).1 =
  (select u hd m (fresh_rules fv p).2         s1).1.
Proof.
  elim: p s1 fv => //= x xs IH s1 fv; rewrite /=!push/=.
  rewrite !head_fresh_rule/=frs_add_cut_sf.
  case: H => //=s; rewrite !push/=IH; do 2 f_equal.
  by rewrite vur_add_cut_sf.
Qed.

Lemma bc_add_cut_sf u p fv0 c s1:
  (bc u (add_head_prog p) fv0 c s1).1 = (bc u p fv0 c s1).1.
Proof.
  rewrite/bc. case: callable => [[hd q]|]//.
  rewrite/add_head_prog/=; case: fndP => //=k; rewrite !push/=.
  rewrite frs_add_cut_sf; f_equal.
  rewrite sel_add_cut_sf//.
Qed.

Lemma step_add_cut_sf u p fv0 s1 A:
  let sA := step u p                 fv0 s1 A in
  let sB := step u (add_head_prog p) fv0 s1 A in
  sA.1 = sB.1.
Proof.
  elim_tree A fv0 s1 => /=.
  - case: t => //=[c]; rewrite !push//=bc_add_cut_sf//.
  - rewrite !push HA//=. 
  - rewrite !push HB//=. 
  - by rewrite !push HA HB//=; case: ifP => //.
Qed.

Lemma step_add_cut u p A fv0 s1 R R' xx yy:
  mut_excl u p ->
  step u p                 fv0 s1 A = (xx, R) ->
  step u (add_head_prog p) fv0 s1 A = (yy,R') ->
  forall s2 fs C b, runT u p xx.1 s1 R s2 C b fs ->
  exists b', b' || ~~b /\ exists C', runT u (add_head_prog p) yy.1 s1 R' s2 C' b' fs.
Proof.
  move=> ME.
  elim_tree A fv0 xx yy s1 R R' => //=.
  - move=> [??][??]; subst => >; inversion 1 => //; subst.
    by repeat eexists; only 2: apply: FailT.
  - move=> [??][??]; subst => >; inversion 1 => //; subst.
    by repeat eexists; only 2: apply: StopT.
  - case: t => [|c].
      move=> [<-<-][<-<-]>; inversion 1 => //; subst => /=.
      by repeat eexists; only 2: apply: StopT.
    rewrite !push/= => -[??][??]; subst.
    move=> s2 fs C b.
    admit.
  - rewrite!push/= => -[??][??]; subst => /=.
    case eA1: step => [xx A1].
    case eA2: step => [yy A2]/=.
    have:= step_add_cut_sf u p fv0 s1 A; rewrite eA1 eA2/= =>?; subst.
    case: yy eA1 eA2 => fv1 t eA1 eA2.
    have /= {HB}HA := HA _ _ _ _ _ _ eA1 eA2.
    set CB := if _ then _ else _.
    move=> s2 fs C b H.
    exists false.
    have ? := run_or0 H; subst; split => //.
    have := run_or_complete H.
    destruct s2 => //=; last first.
      move=> [?[b[fv2[H1]]]]; subst.
      have[b' [Hb [C {}HA]]] := HA _ _ _ _ H1.
      have {}HA := run_or_correct_left HA.
      destruct b => //=; first by move => ?; repeat eexists; subst; destruct b'.
      move=> [b2 H2].
      destruct b'.
        have {}HA := HA sm CB.
        admit. (*pb with fv*)
      have /={}HA := HA sm CB None None false fs.
      eexists; apply: HA.
      admit. (*should be ok*)
    move=> [].
      move=> [L'[b [H1 H2]]].
      have[b1 [Hb [C' {}HA]]] := HA _ _ _ _ H1.
      have := run_or_correct_left HA sm CB.
      by eexists; eauto.
    move=> [fv' [H1 [b1 H2]]].
    have[b2 [Hb [C' {}HA]]] := HA _ _ _ _ H1.
    have HA' := run_or_correct_left HA.
    destruct b2.
      (* should be false by mut_excl? eA2 introduces a cut (HA vs H1), then if it is 
         superficial, then CB does not exist
      *)
      admit.
    eexists; apply: HA'.
    admit.
  - rewrite!push/= => -[??][??]; subst => /=.
    case eA1: step => [xx A1].
    case eA2: step => [yy A2]/=.
    have:= step_add_cut_sf u p fv0 sm B; rewrite eA1 eA2/= =>?; subst.
    case: yy eA1 eA2 => fv1 t eA1 eA2/= s2 fs C b R.
    have /= {}HB := HB _ _ _ _ _ _ eA1 eA2.
    have ? := run_or0 R; subst.
    exists false; split => //.
    have/=:= run_same_structure R; case: C R => [[]|]//=.
      move=> L S R H.
        move=> /andP[/eqP?/eqP?]; subst.
      have [b1 RR] := proj2 (run_ko_left2 u p fv1 fs S A1 ((Some R)) s2 s1) H.
      have [b2 [? [C {}HB]]] := HB _ _ _ _ RR.
      simpl in *.
      have {}HB := ex_intro (fun x => runT _ _ _ _ _ _ _ x _) b2 HB.
      have := proj1 (run_ko_left2 u (add_head_prog p) fv1 fs S A2 C s2 s1) HB.
      by eexists; eauto.
    move=> H _.
    have [b1 RR] := proj2 (run_ko_left2 u p fv1 fs sm A1 None s2 s1) H.
    have [b2 [? [C {}HB]]] := HB _ _ _ _ RR.
    have {}HB := ex_intro (fun x => runT _ _ _ _ _ _ _ x _) b2 HB.
    have := proj1 (run_ko_left2 u (add_head_prog p) fv1 fs sm A2 C s2 s1) HB.
    by eexists; eauto.
  - rewrite !push/=; case: ifP => sA [??][??]s2 fs C b; subst; last first.
      case eA1: step => [xx A1].
      case eA2: step => [yy A2]/=.
      have:= step_add_cut_sf u p fv0 s1 A; rewrite eA1 eA2/= =>?; subst.
      case: yy eA1 eA2 => fv1 t eA1 eA2/= H.
      have /= {HB} HA := HA _ _ _ _ _ _ eA1 eA2.
      admit.
    case eA1: step => [xx A1].
    case eA2: step => [yy A2]/=.
    have:= step_add_cut_sf u p fv0 (get_subst s1 A) B; rewrite eA1 eA2/= =>?; subst.
    case: yy eA1 eA2 => fv1 t eA1 eA2/=.
    have /= {HA} HB := HB _ _ _ _ _ _ eA1 eA2.
    admit.
Admitted.

Lemma prog_equiv_head_cut u p fv s A s2 C b fs:
  mut_excl u p ->
  runT u p fv s A s2 C b fs ->
    exists b' C, runT u (add_head_prog p) fv s A s2 C b' fs.
Proof.
  move=> + H; elim_run H => //=ME.
  - repeat eexists; by apply: StopT => //.
  - have [b'[C' {}IH]] := IH ME.
    have /=[?|?] := path_atom_exp_cut pA eA; subst.
      repeat eexists; by apply/StepT/IH/erefl/step_cut_add_cut.
    case eA': (step u (add_head_prog p) fv0 s1 A) => [xx B'].
    have:=step_add_cut_sf u p fv0 s1 A; rewrite/=eA eA'/= => ?; subst.
    have/= [b2 [?[C2 {}IH]]] := step_add_cut ME eA eA' rB; subst.
    by repeat eexists; apply: StepT eA' erefl IH.
  - have [b'[C' {}IH]] := IH ME.
    repeat eexists; by apply: BackT IH.
  - repeat eexists; by apply: FailT.
Qed.
    
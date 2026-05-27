From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.
From det Require Import tree_prop_hard tree_vars mut_excl unif fresh.

From det Require Import check_fo.

Lemma runT_cutl u p fv s t r b fv':
  runT u p fv s (cutl t) r b fv' ->
    [/\ 
      fv' = fv, b = false &
      if success t then
        r = One (next_subst s (cutl t))
      else r = Zero].
Proof.
  remember (cutl _) as t' eqn:Ht => H.
  elim_run H t Ht.
  - rewrite -success_cut sA//.
  - by rewrite prune_cutl in NS.
  - have [] := cut_success_failed t.
      by move=> /success_incomplete; rewrite pA.
    by rewrite (incomplete_failed pA).
  - by rewrite prune_cutl_failed in nA.
  - case: ifP => // sT.
    rewrite failedF_prune// in nA.
    by rewrite failed_success_cut success_cut sT.
Qed.

Lemma is_det_tail_cut p s fv l:
  is_det p s fv (And l [::cut] (TA cut)).
Proof.
  move=> r [s'[r' H]].
  remember (And _ _ _) as t' eqn:Ht'.
  elim_run H l Ht'.
  - by move: sA; rewrite rew_pa => /andP[]//.
  - by move: sA; rewrite rew_pa => /andP[]//.
  - move: pA eA; rewrite rew_pa/= !push.
    case: ifP => sl pA [???]; subst.
    rewrite -success_cut in sl.
    inversion rB; subst; simpl in *; eauto.
    - move: H1; rewrite sl prune_cutl//.
    - by move: H; rewrite rew_pa sl.
    - move: H0; rewrite/=sl => -[?]; subst.
      by move: H; rewrite rew_pa sl success_failed//.
  - by apply: IH erefl.
  - move: fA nA; rewrite rew_pa/=.
    move=> /orP[fl|/andP[]]//.
    rewrite fl failed_success//.
    case nl: prune => //=[l'][?]; subst. 
    apply: IH erefl.
Qed.

Definition same_sub {T1 T2:eqType} (s1 s2: option (T1*T2)) := 
  match s1, s2 with
  | None, None  => true
  | Some s1, Some s2 => s1.1 == s2.1
  | _, _ => false
  end.

Lemma is_det_tail_cut1 p s fv t r r':
  check_program p ->
  det_tree p.(sig) t ->
  runT' p fv s t r -> 
  runT' p fv s (And t [::cut] (TA cut)) r' -> 
  r = r'.
Proof.
  move=> H1 + [b'[c' H2]][+[]].
  elim_run H2 H1 => dA b c.
    {
      inversion 1; subst; only 1,2: by move: H; rewrite rew_pa sA.
      - move: H0 => /=; rewrite sA => -[???]; subst.
        replace (And _ _ _) with (cutl (And A [::cut] OK)) in H3; last by rewrite/=sA.
        by have [??]:= runT_cutl H3; rewrite rew_pa sA// ges_subst_cutl/=rew_pa sA//.
      - move: H0; rewrite/= sA => -[?]; subst.
        by move: H; rewrite rew_pa success_failed sA//.
      - by move: H; rewrite /=sA//.
    }
    {
      by have:= det_check_prune_succ dA sA; rewrite NS.
    }
    {
      have/= DB := det_check_step H1 dA eA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
        by move: H; rewrite rew_pa => /andP[].
        by move: H; rewrite rew_pa => /andP[].
        move: H0 => /=.
        case: ifP => sA; first by rewrite success_incomplete in pA.
        rewrite eA => -[???]; subst.
        by apply: IH H3.
        by move: H; rewrite rew_pa incomplete_failed//= => /andP[].
      by move: H; rewrite/=incomplete_failed//if_same.
    }
    {
      have/= DB := det_check_prune dA nA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
        by move: H; rewrite rew_pa => /andP[].
        by move: H; rewrite rew_pa => /andP[].
        move: H; rewrite rew_pa//= failed_success// => IA.
        by rewrite incomplete_failed in fA.
        move: H0 => /=; rewrite failed_success//=fA nA/= => -[?]; subst.
        by apply: IH H2.
      move: H => /=; rewrite failed_success//fA nA//=.
    }
    {
      have fA:= prune_None nA.
      inversion 1 => //=; subst.
        by move: H; rewrite rew_pa failed_success.
        by move: H; rewrite rew_pa failed_success.
        by move: H; rewrite rew_pa failed_success// => IA; rewrite incomplete_failed in fA.
      by move: H0; rewrite/= failed_success fA// nA.
    }
Qed.

Section once.

  Variable once_sym: P.

  Definition once_impl := 
    let X := Tm_V (IV 0) in
    {| 
      head := Tm_App (Tm_P once_sym) X;
      premises := call (X) :: [::cut]
    |}.

  Definition once_sig := arr input (b (d Pred)) (b (d Func)).

  Definition once_sigS : sigT :=
    [fmap].[once_sym <- once_sig].

  Definition no_once (r: seq R) :=
    forall x, x \in r -> 
      if get_tm_hd (head x) is inl hd then hd <> once_sym
      else true.

  Lemma no_once_cons x xs: no_once (x :: xs) -> no_once xs.
  Proof. by rewrite/no_once/= => H r H1; apply/H; rewrite in_cons H1 orbT. Qed.

  Definition prog_once p :=
    (p.(sig) = p.(sig) + once_sigS) /\ forall r, 
      p.(rules) = once_impl :: r /\ no_once r.

  Notation sig_flat := [::input].

  Lemma once_sigP sig:
    (sig + once_sigS).[? once_sym] = Some once_sig.
  Proof. by rewrite/once_sigS !FmapE.fmapE eqxx/= fsetU0 in_fset1 eqxx. Qed.

  (* Lemma get_modes_rev_once_sym t:
    get_modes (Tm_App (Tm_P once_sym) t) once_sig = sig_flat.
  Proof. by []. Qed. *)

  Lemma no_once_select u l rs s:
    no_once rs ->
    select u once_sym l sig_flat rs s = (fset0, [::]).
  Proof.
    elim: rs l s => //= -[hd bo] xs IH t s/= H1.
    have {}IH := IH _ _ (no_once_cons H1).
    rewrite {}IH/=.
    case: eqP => //= Hx.
    move: H1; rewrite /no_once/=.
    set P := {|head := _; premises := _|}.
    by move=> /(_ P); rewrite in_cons eqxx => /(_ isT)/=; rewrite-Hx.
  Qed.

  Lemma no_once_fresh fv rs: no_once rs -> no_once (fresh_rules fv rs).2.
  Proof.
    rewrite/no_once/=. 
    elim: rs fv => //= x xs IH fv H e; rewrite !push/=.
    rewrite in_cons => /orP[/eqP?|]; subst; last first.
      apply/IH => H1 H2; apply/H.
      by rewrite in_cons H2 orbT.
    rewrite/fresh_rule!push/=.
    case: x H => /= hd bo H.
    rewrite/rename !push/=.
    set X := fresh_tm _ _ _.
    case Y: get_tm_hd => //=[p].
    have:= callable_ren X.2 hd p; rewrite Y => /proj1/(_ erefl) H1.
    have:= H (mkR hd bo); rewrite/= in_cons H1 eqxx; auto.
  Qed.


  Lemma id_det_once p s t fv:
    prog_once p ->
    is_det p s fv (TA (call (Tm_App (Tm_P once_sym) t))).
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    rewrite/is_det HS => r' [b'[fv' Hx]].
    inversion Hx; clear Hx; subst => //.
    move: H1; rewrite/=/bc [get_tm_hd _]/=.
    case (boolP (acyclic_sigma s)) => AS; last first => //=.
      by move=> [???]; subst; inversion H3; auto.
    rewrite !FmapE.fmapE !inE eqxx/=.
    case X: fresh_rules => [fvx' rs'].
    rewrite/fresh_rule/= fset0U codomf0/= fsetU0/rename cat0f.
    rewrite /= !(inE,FmapE.fmapE)/= in_fnd/=?inE// => Hx.
    rewrite no_once_select; last first.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[_ <-].
      by apply: no_once_fresh.
    rewrite eqxx/=.
    case M: obind => [s'|][???]; subst; last by inversion H3 => //; auto.
    set Y := _ `|` _ in H3.
    rewrite ffunE/= in H3.
    have [b'] := runT_Nor_elim H3.
    destruct r'; eauto.
    move=> [B' ? Hz]; subst.
    set P := {| rules := _; sig := _|} in Hz.
    set T := TA _ in Hz.
    have {}Hz : runT' P Y s' (And T [:: cut] (TA cut)) (Many s0 B').
      do 2 eexists; apply: Hz.
    by have [//|[]] := is_det_tail_cut Hz.
  Qed.
End once.

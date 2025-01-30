From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.


Lemma map_cat_deep {T:Type} {R:Type} l gs:
  forall (P:T -> R),
  [seq [seq P x | x <- b] ++ [seq P x | x <- gs] | b <- l] = [seq [seq P x | x <- b ++ gs] | b <- l].
Proof.
  revert gs; induction l; intros; simpl; f_equal; auto.
  now rewrite map_cat.
Qed.

(* Definition functional_prog' p :=
  forall n r g a, run p n g a = r -> r = None \/ r = Some a. *)

Definition functional_prog p :=
  forall n r g, run p n (not_alt_goal g) [::] = r -> r = None \/ r = Some [::].

Definition functional_pred p f :=
  forall n r, run p n [:: Goal (call f) [::]] [::] = r -> r = None \/ r = Some [::].

Definition functional_goal p g :=
  forall n r, run p n (not_alt_goal g) [::] = r -> r = None \/ r = Some [::].

Definition functional_goal' p g :=
  forall n r, run p n (not_alt_goal g) [::] = r -> r = Some [::].

Lemma functional_neck_cut_all:
  forall p, functional_prog (neck_cut_all p).
Proof.
  move=> prog n.
  elim: n => /=.
  - move=> r _ <-; auto.
  - move=> n IH [sol|]; auto.
    move=> [|[|p] gs] /=; auto.
    + apply IH.
    + simpl; unfold neck_cut_all.
      destruct (prog p) as [|s] eqn:?; auto.
      simpl; fold_neck_cut_all prog.
      destruct n; auto.
      move => /= H.
      apply pumping1 in H.
      specialize (IH (Some sol) (s ++ gs)).
      rewrite <-map_cat in H.
      now apply IH.
Qed.

Module Elpi.
  Definition success p g a :=
    exists x, Elpi.nur p g a x.

  Definition functional_goal p g :=
    (exists x, Elpi.nur p g [::] x) -> Elpi.nur p g [::] [::].

  Lemma functional_neck_cut_all:
    forall p g R, Elpi.nur (neck_cut_all p) (not_alt_goal g) [::] R -> R = [::].
  Proof.
    intros.
    apply Elpi.complete in H.
    destruct H.
    apply functional_neck_cut_all in H.
    inversion H; try by [].
    inversion H0; subst; auto.
  Qed.

End Elpi.

Definition all_pred_have_cut :=
  for_all (exists_ (fun x => x = cut)).

Definition all_rules_have_cut (p: bodiesT) :=
  forall f, all_pred_have_cut (p f).

Definition goal_has_cut :=
  (exists_ (fun g => match g with Goal g _ => g = cut end)).

Definition all_goals_have_cut l := for_all (goal_has_cut) l.


Definition build_goals ca gs := [seq Goal g ca | g <- gs].

Arguments suffix {_}.
Arguments prefix {_}.
Fixpoint good_cut (l:list goal) (a: list alt) :=
  match l with
  | [::] => true
  | Goal _ ca :: tl => suffix ca a && good_cut tl a
  end. 

Fixpoint good_levels (l:list alt) :=
  match l with
  | [::] => true
  | x :: xs => good_cut x xs && good_levels xs
  end.

Inductive nur' (p: bodiesT) : list goal -> list alt -> (list alt) -> Prop :=
| Stop a : nur' [::] a a
| Cut a (ca:list alt) r gl : good_cut gl ca -> nur' gl ca r -> nur' [::Goal cut ca & gl] a r
| Fail a g al r : nur' a al r -> nur' g (a :: al) r
| Call {a ca f b bs gl r} : p f = [:: b & bs ] ->
  nur' (save_alt a b gl) (more_alt a bs gl) r -> nur' [::Goal (call f) ca & gl] a r.

Lemma good_lvl_cat {l1 l2} : 
  good_levels (l1++l2) -> good_levels l2.
Proof.   by elim: l1 => //= x xs IH /andP[_ /IH].  Qed.

Lemma good_lvl_suffix {ca} {a}: suffix ca a -> good_levels a -> good_levels ca.
Proof. by move => /suffixP [x] -> /good_lvl_cat /= . Qed.

Lemma save_alt_cons {a g1 gl l}: save_alt a (g1 :: gl) l = Goal g1 a :: save_alt a gl l.
Proof. by []. Qed.

Lemma more_alt_cons {a x xs tl} : more_alt a (x::xs) tl = save_alt a x tl :: more_alt a xs tl.
Proof. by []. Qed.

Lemma good_cut_more_alt {gs tl a tl'}:
  good_cut tl a -> good_cut tl (more_alt a gs tl').
Proof.
  revert gs a tl'.
  unfold more_alt, save_alt.
  elim: tl => //= [[[|F]ca]tl] IH gs a tl'.
    move=> /andP [H H1].
    apply /andP; split.
      now apply suffix_catr.
    eapply IH; auto.
  intros.
  move /andP: H => [] S G.
  apply /andP; constructor.
    apply suffix_catr; auto.
  eapply IH; auto.
Qed.

Lemma good_cut_save_alt {a g1 tl}:
  good_cut tl a -> good_cut (save_alt a g1 tl) a.
Proof.
  elim: g1 => //= _ L + GC.
  move => /(_ GC).
  by rewrite suffix_refl.
Qed.

Lemma good_cut_save_alt_more_alt {a b bs gl}:
  good_cut gl a -> good_cut (save_alt a b gl) (more_alt a bs gl).
Proof. move=> /(fun x => good_cut_more_alt (good_cut_save_alt x)) //. Qed.

Lemma good_cut_cat a: forall {b l}, good_cut a l -> good_cut b l -> good_cut (a ++ b) l.
Proof. 
  elim: a => //= [[[|F]ca]tl] IH b l /andP.
    move=> [S_CA GC_TL] GC_B.
    by apply /andP; auto.
  move=> [S GTL] GB.
  by apply /andP; constructor; auto.
Qed.

Lemma good_lvl_more_alt {a gs tl}:
  good_levels a -> good_cut tl a -> good_levels (more_alt a gs tl).
Proof.
  elim: gs a tl => // gs0 gs IH a tl GL GC.
  rewrite more_alt_cons.
  apply /andP; split; auto.
  by apply good_cut_more_alt, good_cut_save_alt.
Qed.

Lemma weaken_success {prog g a r}:
  nur' prog g a r -> good_levels (g::a) -> forall a1, 
     prefix a a1 -> good_levels (g::a1) ->
      exists r1, nur' prog g a1 r1.
Proof.
  move=> NUR.
  elim: NUR => /=.
  + repeat econstructor.
  + move=> {}a ca {}r gl GC_GL NUR' IH /andP [/andP [SCA GCGL] GLA] aext PREF.
    have : good_cut gl ca && good_levels ca.
      rewrite (good_lvl_suffix SCA GLA).
      by rewrite GC_GL.
    have GG: good_cut gl ca && good_levels ca.
      by rewrite GC_GL (good_lvl_suffix SCA GLA).
    move=> /IH /(_ _ (prefix_refl ca) GG) [sol {IH}].
    by exists sol; repeat constructor.
  + move=> {}a {}g {}al {}r NUR IH /and3P [GC_G GC_A GL_AL] [|aext1 aext] + /andP [GC_G' GC_aext] //.
    rewrite prefix_cons => /andP [/eqP H]; subst aext1.
    have: good_cut a al && good_levels al.
      by rewrite GL_AL GC_A.
    move=> GCAAL PREF.
    move: IH => /(_ GCAAL aext PREF GC_aext) [x IH].
    by exists x; apply Fail.
  + move=> {}a ca f b bs gl {}r PF NUR IH /andP [/andP []] HK1 HK2 HK3.
    have IH1: good_cut (save_alt a b gl) (more_alt a bs gl) && good_levels (more_alt a bs gl).
      by rewrite good_cut_save_alt_more_alt ?good_lvl_more_alt //.
    move: IH => /(_ IH1 (more_alt a bs gl) ) /(_ (prefix_refl _) IH1) [sol HSol] alts PREF _.
    eexists sol; apply: Call PF _.
    admit.
Admitted.

Lemma weaken_success_nil {prog g a r}:
  good_levels (g::a) ->
    nur' prog g [::] r -> good_levels (g::[::]) ->
    exists r1, nur' prog g a r1.
Proof. move=> GLGA + GLG => /weaken_success /(_ GLG a (prefix0s _) GLGA) //. Qed.

Definition make_empty_alts g := match g with Goal g _ => Goal g [::] end.

Lemma good_cut_empty l : good_cut [seq make_empty_alts x | x <- l] [::].
 by elim: l => //= -[f ? gl] IH /=.
Qed.

Lemma save_alt_with_make_empty_alt {a g1 tl}:
  [seq make_empty_alts i  | i <- save_alt a g1 tl] = (save_alt [::] g1 [seq make_empty_alts i  | i <- tl]).
Proof.
  elim: g1 => //= g1 gl IH /=.
  by rewrite save_alt_cons IH.
Qed.

Definition g2a g := match g with Goal _ a => a end.

Definition less l1 l2 :=
  forall p1 p2 s, p1 ++ s = l1 -> p2 ++ s = l2 -> forall e1 e2, e1 \in p1 -> e2 \in p2 -> suffix (g2a e1) (g2a e2).

Lemma less_save_alt {x0 g1 tl f ca a} :
  suffix ca a ->
  less x0 ([seq Goal x a  | x <- g1] ++ tl) ->
    less x0 (Goal (call f) ca :: tl).
Proof.
Abort.

Lemma succeed_more_alts {prog sol g1 g2 alts}:
  nur' prog g1 alts sol ->
    less g1 g2 ->
      nur' prog g2 alts sol.
Abort.

(* THIS IS WRONG: we can have (g::gs) = [[!,fail],[::]] 
  the cut prevent the alternative to be used
*)
Lemma nur_empty_goal {prog g gs}:
  good_levels (g::gs) ->
  [::]  \in (g :: gs) ->
    exists s, nur' prog g gs s.
Proof.
  revert gs.
  elim: g => [|[] gtl] /=.
    move=> gs; exists gs; constructor.
  move=> ca l IH gs /andP [/andP [SIH  GC]] GS.
  rewrite in_cons => /orP [] //= NGS.
  have b': [::] \in l :: gs.
    by rewrite in_cons NGS orbC.
  have GC_GL: good_cut l gs && good_levels gs.
    by apply /andP.
  specialize (IH _ GC_GL b') as [].
  destruct gtl.
Abort.
  
  
(* THIS IS NOT TRUE: if gs = [[!, fail], [true]]
  the hyp is satisfied: there is a goal in gs which succeed (namely the second)
  the conclusion is however wrong: run (!, fail) [true] can't succeed
 *)
Lemma call_success {prog g' a s gs tl f}:
  nur' prog g' [::] s ->
    prog f = gs ->
      g' \in [seq [seq make_empty_alts i  | i <- i]  | i <- [seq save_alt a b tl  | b <- gs]] ->
        exists (s' : seq alt),
          nur' prog (Goal (call f) [::] :: [seq make_empty_alts i  | i <- tl]) [::] s'.
Proof.
Abort.

Definition siblings l1 l2 :=
  match l1, l2 with 
  | [::], _ | _, [::] => True
  | Goal _ a::_, Goal _ b::_ => a = b 
  end.

Definition is_call x := match x with Goal cut _ => false | _ => true end.

Definition all_same_level_before_have_not_cut (g:list goal) (l:list alt) :=
  exists bef, 
    prefix (rcons bef g) l /\
      exists x, 
        x \in bef /\ 
          all is_call x.

Lemma run_with_nil_and_all_is_call {prog g bef alts}:
good_levels (g::alts) ->
  prefix (rcons bef [::]) alts
    -> all is_call g
      -> all (all is_call) (bef)
        -> exists s', nur' prog g alts s'.
Proof.
  revert g bef.
  induction alts.
    destruct bef; try by [].
  destruct g as [|ghd gtl].
    repeat econstructor.
  destruct ghd as [[|F] ca].
    by[].
  destruct (prog F) as [|fhd ftl] eqn:PF.
    (* here prog F has no solution: therefore call Fail *)
    destruct bef as [|befhd bef]; simpl.
      move=> /and3P [/andP [SCA GCCTLA] GCA] GLA /andP [/eqP HA PNil]; subst.
      repeat econstructor.
    move=> /and3P [/andP [SCA GCGTLA] GCA] GLA /andP [/eqP HL PBEF] AGTL /andP [AA AAB]; subst a; simpl in *.
    have IHH: good_cut befhd alts && good_levels alts.
      by apply /andP.
    specialize (IHalts befhd bef IHH PBEF AA AAB) as [].
    repeat econstructor; apply H.

  (* here prog F has solution fhd ftl *)
  move=> bef /= .
Abort.


Lemma run_with_nil_and_all_is_call' {prog alts tl x bef gs}:
  prefix (rcons bef [::])
    [seq [seq make_empty_alts i0  | i0 <- i] | i <- [seq save_alt alts b tl  | b <- gs]] 
    -> x  = [seq make_empty_alts i  | i <- tl]
      -> all is_call x
        -> exists s' : seq alt,
          nur' prog [seq make_empty_alts i  | i <- tl]
          (more_alt [::] gs [seq make_empty_alts i  | i <- tl]) s'.   
Proof. Abort.

Lemma aa {prog g' s g1 gs a tl}:
  good_cut tl a -> good_levels a ->
  nur' prog g' [::] s ->
    all_same_level_before_have_not_cut g' [seq [seq make_empty_alts i  | i <- i] | i <- [seq save_alt a b tl  | b <- g1 :: gs]] ->
    (* g' \in [seq [seq make_empty_alts i  | i <- i] | i <- [seq save_alt a b tl  | b <- g1 :: gs]] -> *)
      exists s',
        nur' prog (save_alt [::] g1 [seq make_empty_alts i  | i <- tl]) (more_alt [::] gs [seq make_empty_alts i  | i <- tl]) s'.
Proof.
  remember [::].
  move=> + + NUR.
  move: Heql tl a g1 gs.
  induction NUR; subst.
  + 1:{
    move=> -> tl alts g1 gs GC GL [bef [+ [x [+ IS_CALL]]]]; simpl in *.
    destruct bef; try by [].
    move=> /= /andP [/eqP H PREF]; subst.
    rewrite in_cons => /orP [/eqP H| ]; subst.

      erewrite save_alt_with_make_empty_alt in IS_CALL.
      destruct g1.
        destruct tl.
          repeat econstructor.
        rewrite <-@save_alt_with_make_empty_alt with (a:=[::]).
        simpl.
        destruct g; destruct g; try by [].
        destruct (prog n) eqn:?.
        destruct gs; simpl; unfold more_alt.
        destruct bef; try by [].
        simpl.
        econstructor. 
        apply Fail.

        repeat econstructor.
Abort.

Lemma cons_cat {T:Type} {a b c}: (a:T)::b++c = ([::a]++b)++c. by []. Qed.

Lemma cut_semantic {prog s g alts}:
    nur' prog g alts s ->
      good_levels (g::alts) ->
        exists g' s', g' \in (map (map make_empty_alts) (g :: alts)) 
          (*e tutti quelli che precedono g' e che sono dello stesso livello non hanno cut 
            o falliscono prima di raggiungere il cut*) 
            /\  nur' prog g' [::] s'.
Proof.
  elim => /=.
  - exists [::], [::]; repeat constructor; auto.

  - move => a ca r gl GC H /= IH /= /andP [/andP [ H1 H2 ] H3].
    have IH_p : good_cut gl ca && good_levels ca.
      by rewrite (good_lvl_suffix H1) ?GC; auto.
    case: (IH IH_p) => g' [s' [+ NUR]].
    rewrite in_cons => /orP; case.
    - move=> /eqP?; subst.
      exists (map make_empty_alts (Goal cut ca :: gl)), s'; constructor; auto.
        by rewrite inE eqxx.
      by simpl; apply: Cut => //; apply: good_cut_empty.
    - move=> g'_ca.
      exists g', s'.
      split; last by [].
      rewrite inE orbC.
      case/suffixP: H1 => a' ->. 
      by rewrite map_cat mem_cat g'_ca orbT.

  - move=> g' gl al solution H + /and3P [] p p0 p1.
    case; first by rewrite p0 p1.
    move=> x [s' [IN NUR]].
    exists x, s'.
    split; last by [].
    by rewrite in_cons IN orbT.

  - move=> a ca f g1 gs tl r PF NUR + /andP [/andP [_ GC] GL].
    rewrite (good_cut_more_alt (good_cut_save_alt GC)) (good_lvl_more_alt GL GC) => /(_ isT).
    case=>[g'[s' [+ NUR']]].
    unfold more_alt.
    rewrite map_cat cons_cat mem_cat => /orP. case.
    2:{ exists g', s'; constructor; auto. by rewrite in_cons b orbC. }
    simpl.
    rewrite <-map_cons.
    replace (save_alt a _ _ :: [seq _ | _ <- _]) with [seq save_alt a b tl | b <- g1 :: gs ] by auto.
    rewrite /= in_cons => /orP GIN.
    exists ((Goal (call f) [::] :: [seq make_empty_alts i  | i <- tl])).
    
    set (empty_tl:= map make_empty_alts tl).

    suffices: exists s, nur' prog (save_alt [::] g1 empty_tl) (more_alt [::] gs empty_tl) s.
      move=> [sol' H'].
      eexists; split; auto.
      by rewrite in_cons eqxx /=.
      apply: Call PF H'.
    
    have {}GIN: (g' = save_alt [::] (g1) (empty_tl) \/ g' \in [seq save_alt [::] b (empty_tl)  | b <- gs]).
      move: GIN => [/eqP |] H.
      rewrite save_alt_with_make_empty_alt in H; auto.
      right.
      congr(g' \in _) : H.
      unfold empty_tl.
      rewrite -map_comp.
      apply: eq_map.
      move=> ? /=.
      by erewrite save_alt_with_make_empty_alt.

    have GL_G' : good_levels [:: g'].
      destruct GIN; subst.
        simpl.
        rewrite -(@save_alt_with_make_empty_alt [::]).
        by rewrite good_cut_empty.
      elim: gs H {PF NUR} => //=.
      move=> x xs IH.
      rewrite in_cons => /orP [/eqP H |]; subst.
        rewrite -(@save_alt_with_make_empty_alt [::]).
        by rewrite good_cut_empty.
      auto.

    have GL_G_TL: good_levels (g' :: more_alt [::] gs empty_tl).
      simpl.
      rewrite /= andbC /= in GL_G'.
      rewrite good_cut_more_alt ?GL_G' //.
      rewrite good_lvl_more_alt //.
      by rewrite good_cut_empty.

    destruct GIN.
     have {} NUR' := @weaken_success_nil _ _ (more_alt [::] gs empty_tl) _ GL_G_TL NUR' GL_G'.
      destruct NUR'. 
      eexists x.
      by subst.
    
    suffices: exists s',  nur' prog (save_alt [::] g1 empty_tl) (more_alt [::] gs empty_tl) s'.
      move=> [sol' H'].
      by eexists sol'.

    elim: gs  (save_alt [::] g1 empty_tl) H NUR' {NUR PF GL_G_TL} => [|x xs IH] //= G.

    rewrite in_cons => /orP [/eqP H | ].
      move=> NUR.
      have GL_G_TL: good_levels (g' :: more_alt [::] xs empty_tl).
        simpl.
        rewrite /= andbC /= in GL_G'.
        rewrite good_cut_more_alt ?GL_G' //.
        rewrite good_lvl_more_alt //.
        by rewrite good_cut_empty.

      have [sol {}NUR] := @weaken_success_nil _ _ (more_alt [::] xs empty_tl) _ GL_G_TL NUR GL_G'.
      exists sol.
      rewrite more_alt_cons.
      by apply Fail; subst.

    move=> /IH IH' /IH' H.
    destruct (H (save_alt [::] x empty_tl)).
    rewrite more_alt_cons.
    by exists x0; apply Fail.
Qed.

Print Assumptions cut_semantic.

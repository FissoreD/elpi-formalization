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
    forall p g, functional_goal (neck_cut_all p) (not_alt_goal g).
  Proof.
    intros ??[x H].
    remember (neck_cut_all p).
    remember (not_alt_goal g).
    remember [::].
    revert g Heqb Heql0 Heql.
    induction H.
    - intros; subst; constructor.
    - intros; subst; constructor.
      destruct g; inversion Heql; subst.
      eapply IHnur; auto.
    - intros; subst.
      destruct g; inversion Heql.
      subst.
      econstructor.
      eapply H.
      simpl in Heql.
      (* econstructor 3. *)
      (* apply H. *)
  Abort.

  Lemma functional_neck_cut_all:
    forall p g R, Elpi.nur (neck_cut_all p) (not_alt_goal g) [::] R -> R = [::].
  Proof.
    intros.
    apply Elpi.complete in H.
    destruct H.
    apply functional_neck_cut_all in H.
    inversion H; try by [].
    inversion H0; subst; auto.
  Abort.

End Elpi.

Definition all_pred_have_cut :=
  for_all (exists_ (fun x => x = cut)).

Definition all_rules_have_cut (p: bodiesT) :=
  forall f, all_pred_have_cut (p f).

Definition goal_has_cut :=
  (exists_ (fun g => match g with Goal g _ => g = cut end)).

Definition all_goals_have_cut l := for_all (goal_has_cut) l.


Definition build_goals ca gs := [seq Goal g ca | g <- gs].

Definition EQ := Datatypes_list__canonical__eqtype_Equality program_goal__canonical__eqtype_Equality.
Arguments suffix {_}.
Arguments prefix {_}.
Fixpoint good_cut (l:list goal) (a: list alt) :=
  match l with
  | [::] => true
  | Goal _ ca :: tl => @suffix EQ ca a && good_cut tl a
  (* | _ :: tl => good_cut tl a *)
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

Lemma good_lvl_suffix {ca:seq EQ} {a}: suffix ca a -> good_levels a -> good_levels ca.
Proof. by move => /suffixP [x] -> /good_lvl_cat /= . Qed.

(* Inductive prefix_alt : _ -> _ -> Prop :=
  | prefix_alt_nil a : prefix_alt [::] a
  | prefix_alt_con {x xs y ys} :
    good_levels [::x;y] -> prefix_alt xs ys -> prefix_alt (x::xs) (y::ys).

Lemma prefix_alt_refl {a}: prefix_alt a a.
Proof. 
  induction a; constructor; auto.
  induction a; auto.
  simpl.
  destruct a; destruct g.
  apply /and3P.
  constructor; auto.
   *)

Lemma weaken_success {prog g a a1 r}:
  nur' prog g a r -> prefix a a1 -> good_levels (g::a) ->
  exists r1, nur' prog g a1 r1.
Proof.
  (* simpl in *.
  intro.
  move: a1.
  elim: H.
  + intros. exists a1; repeat constructor; auto.
  + move=> alts ca res gl.
    intros.
    eelim H1.
    move=> x [RP PR].
    eexists; constructor.
      apply Cut; auto; apply RP.
    auto.
    apply prefix_refl.
    apply /andP.
    constructor; auto.
    apply andb_prop in H3 as [].
    simpl in H3.
    apply andb_prop in H3 as [].
    apply (good_lvl_suffix H3 H4).
  + intros.
    destruct a1; inversion H1.
    simpl in H2.
    move: H2.
    move=> /and3P []; intros.
    apply andb_prop in H4 as [].
    move: H2.
    move=> /eqP; intro; subst.
    specialize (H0 _ H3) as [?[]].
    apply /andP; auto.
    exists x.
    constructor.
    constructor 3.
    apply H0.
    auto.
  + intros.
    eexists.
    constructor.
    eapply Call.
    apply H. *)
Admitted.

Lemma weaken_success_nil {prog g a r}:
  nur' prog g [::] r -> good_levels (g::[::]) ->
  exists r1, nur' prog g a r1.
Proof.
  remember [::].
  induction 1; subst.
  + exists a; repeat constructor.
  + eexists. constructor.
    auto.
    apply H0.
  + discriminate.
  + eexists.
    apply: Call H _.

Admitted.

Definition make_empty_alts g := match g with Goal g _ => Goal g [::] end.

Lemma good_cut_empty l : good_cut [seq make_empty_alts x | x <- l] [::].
by elim: l => //= -[f ? gl] IH /=.
Qed.

Lemma save_alt_cons {a g1 gl l}: save_alt a (g1 :: gl) l = Goal g1 a :: save_alt a gl l.
Proof. by []. Qed.

Lemma save_alt_with_make_empty_alt {a g1 tl}:
  [seq make_empty_alts i  | i <- save_alt a g1 tl] = (save_alt [::] g1 [seq make_empty_alts i  | i <- tl]).
Proof.
  elim: g1 => //= g1 gl IH /=.
  by rewrite save_alt_cons IH.
Qed.

Lemma weaken_success_nil' {prog a g1 tl alts s}:
   nur' prog [seq make_empty_alts i  | i <- save_alt a g1 tl] [::] s ->
    exists s', nur' prog [seq make_empty_alts i  | i <- save_alt a g1 tl] alts s'.
Proof.
  remember ([seq make_empty_alts i  | i <- save_alt a g1 tl]).
  remember [::].
  move=> NUR.
  revert tl Heql.
  induction NUR; subst.
  + exists alts; constructor.
  + move=> tl. 
    destruct g1.
      destruct tl.
        discriminate.
      inversion 1.
      destruct g; inversion H1.
      subst; specialize (IHNUR refl_equal tl refl_equal) as [].
      exists r.
      constructor; auto.
    inversion 1; subst.
Admitted.


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
  unfold save_alt.
  induction g1; auto; simpl.
  destruct a0.
  intros.
  apply /andP; constructor.
  apply suffix_refl.
  auto.
  move=> H.
  apply /andP; constructor; auto.
  apply suffix_refl.
Qed.

Lemma good_cut_cat a: forall {b l}, good_cut a l -> good_cut b l -> good_cut (a ++ b) l.
Proof. 
  elim: a => //= [[[|F]ca]tl] IH.
  move=> b l /andP [S_CA GC_TL] GC_B.
  now apply /andP; auto.
  move=> b l /andP [S GTL] GB.
  apply /andP; constructor; auto.
Qed.

Lemma good_lvl_more_alt {a gs tl}:
  good_levels a -> good_cut tl a -> good_levels (more_alt a gs tl).
Proof.
  unfold more_alt, save_alt.
  revert a tl.
  induction gs; auto.
  simpl.
  intros.
  apply /andP; constructor; auto.
  apply good_cut_more_alt.
  apply good_cut_cat; auto.
  rewrite <-(cats0 [seq Goal x a0  | x <- a]).
  now apply good_cut_save_alt.
Qed.

Definition g2a g := match g with Goal _ a => a end.

(* Fixpoint less l1 l2 :=
  match l1, l2 with
  | Goal _ a1 :: l1, Goal _ a2 :: l2 =>
    suffix a1 a2 && less l1 l2
  | [::], [::] => true
  | _, _ => false
  end. *)

(* Lemma less_refl {a} : less a a.
Proof. elim: a => //= [] [] _ ca l ->. by rewrite suffix_refl. Qed. *)

Definition less l1 l2 :=
  forall p1 p2 s, p1 ++ s = l1 -> p2 ++ s = l2 -> forall e1 e2, e1 \in p1 -> e2 \in p2 -> suffix (g2a e1) (g2a e2).

Lemma same_append {T:Type} {a: list T} : forall p1 p2, p1 ++ a = p2 ++ a -> p1 = p2. Admitted.

(* Lemma less_refl {a} : less a a.
Proof. 
  unfold less.
  elim: a => //=.
  - move=> [] [] s //=.
  - move=> a l IH [|p1h p1] //= [|p2h p2] //= s [] <- <- [] <- /same_append <-.
    move=> e1 e2.
    rewrite /in_cons => /orP.
    case.
      move=> /eqP ->.
      rewrite /in_cons => /orP.
      case.
        move=> /eqP ->.
        apply suffix_refl.
      intro.

    intros.
    eapply IH.
    3:{ apply H. }
    3:{ apply H0. }

    Search (_ ++ _ = _ ++ _ ).


  
   intros. exists [::a], [::a], l; repeat constructor.
    move=> e1 e2.
    rewrite in_cons => /orP.
    case; auto. 
    move=> /eqP?; subst.
    rewrite in_cons => /orP.
    case; auto. 
    move=> /eqP?; subst.
    destruct a.
    apply suffix_refl.
Qed. *)

Lemma less_save_alt {x0 g1 tl f ca a} :
  suffix ca a ->
  less x0 ([seq Goal x a  | x <- g1] ++ tl) ->
    less x0 (Goal (call f) ca :: tl).
Proof.
Admitted.

    
Lemma succeed_more_alts {prog sol g1 g2 alts}:
  nur' prog g1 alts sol ->
    less g1 g2 ->
      nur' prog g2 alts sol.
Admitted.


Lemma blah {prog g' a s' gs tl f}:
  nur' prog g' [::] s' ->
  g' \in [seq [seq make_empty_alts i  | i <- i]  | i <- more_alt a gs tl] ->
  exists (g'0 : seq goal) (s'0 : seq alt),
    g'0 \in (Goal (call f) [::] :: [seq make_empty_alts i  | i <- tl]) :: [seq [seq make_empty_alts i  | i <- i]  | i <- a] /\ 
    nur' prog g'0 [::] s'0.
Admitted.

Lemma cut_semantic {prog s g alts}:
    nur' prog g alts s ->
      good_levels (g::alts) ->
        exists g' s', g' \in (map (map make_empty_alts) (g :: alts)) /\  nur' prog g' [::] s'.
Proof.
  elim=> [ | a ca r gl GC H /= IH /= /andP [/andP [ H1 H2 ] H3] | | ] /=.
  - exists [::], [::]; repeat constructor; auto.

  - have IH_p : good_cut gl ca && good_levels ca.
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

  - move=> g' gl al solution H IH /and3P [] p p0 p1.
    case IH ; first by rewrite p0 p1.
    move=> x [s' [IN NUR]].
    exists x, s'.
    split; last by [].
    by rewrite in_cons IN orbT.

  - move=> a ca f g1 gs tl r PF NUR + /andP [/andP [_ GC] GL].
    rewrite (good_cut_more_alt (good_cut_save_alt GC)) (good_lvl_more_alt GL GC) => /(_ isT).
    case=>[g'[s' [+ NUR']]].
    
    intros.
    epose proof (@blah _ _ a _ (g1::gs) _ f NUR' a0).
    apply H.
    
    apply blah with (a:=g1 :: gs).
    apply NUR'.
    rewrite <-map_cons in a0.
    map_cons
    ayti,
    
     rewrite in_cons => /orP.
    case.
      move => /eqP H; subst.
      exists ((Goal (call f) [::] :: map make_empty_alts tl)).
      eapply weaken_success_nil in NUR' as [].
      eexists.
      split; last apply: Call PF _.
        by rewrite !inE eqxx.
      rewrite -(@save_alt_with_make_empty_alt a).
      apply H.
      simpl.
      by rewrite good_cut_empty.
    move=> G'ALTS.
    destruct gs.
    unfold more_alt in G'ALTS; simpl in G'ALTS.
    exists g', s'.


    ----
    rewrite map_nil in G'ALTS.
    inversion G'ALTS.
    exists ((Goal (call f) [::] :: map make_empty_alts tl)).

  
Admitted.


Lemma cut_semantic {prog s g alts}:
    (* WC g alts -> *)
    nur' prog g alts s ->
      good_levels (g::alts) ->
        exists g' s', g' \in (g :: alts) /\ nur' prog g' [::] s'.
Proof.
  elim=> [ | a ca r gl GC H /= IH /= /andP [/andP [ H1 H2 ] H3] | | ].
  - exists [::], [::]; repeat constructor; auto.
  - case: IH => [| g' [s' ]].
    + rewrite (good_lvl_suffix H1) ?GC; auto.
    + case=> + IH.
      rewrite in_cons => /orP.
      case.
        move=> /eqP?; subst.
        exists (Goal cut ca :: gl), r; constructor; auto.
        by rewrite inE eqxx.
        constructor; auto.
      exists g', s'.
      constructor; auto.
      rewrite inE orbC.

      case/suffixP: H1 => a' ->. 
      by rewrite mem_cat b orbT.
  - simpl.
    move=> g' gl al solution H IH /and3P [] p p0 p1.
    case IH ; first by rewrite p0 p1.
    move=> x [s' [IN NUR]].
    exists x, s'.
    by rewrite inE IN orbT.
  - simpl.
    move=> a ca f g1 gs tl r PF NUR IH /andP [GC GL].
    rewrite (good_cut_more_alt (good_cut_save_alt GC)) (good_lvl_more_alt GL GC) in IH.
    specialize (IH isT) as [?[?[]]].
    move: H; rewrite in_cons => /orP.
    case.
      move => /eqP H; subst.
      exists ((Goal (call f) ca :: tl)); eexists.
      constructor.
        by rewrite !inE eqxx.
      apply: Call PF _.
      unfold save_alt in H0.
      unfold save_alt.
Admitted.

Lemma cut_semantic {prog s n g alts ca}:
  (* all_pred_have_cut (g :: alts) -> *)
    run prog n (build_goals ca g)
      [seq (build_goals ca b) | b <- alts] = Some s ->
        exists g', run prog n (build_goals ca g') [::] = Some s.
Proof.
  revert g alts.
  induction n; try by [].
  destruct g as [|ghd gtl].
    inversion 1; by [].
  destruct ghd as [|p]; simpl.
    exists (cut :: gtl), s, [::]; auto.
  destruct (prog p) eqn:PP.
    unfold more_alt; simpl
    simpl; intros.

    unfold more_alt; simpl.
    destruct alts as [|alt alts].
      inversion 2.
    simpl.
    intros.
    eapply IHn in H0.
    destruct H0 as (?&?&?&?).
    exists (call p :: x), x0; simpl; rewrite PP; simpl.
    exists () (x::x1); simpl.
    rewrite PP; simpl.

Lemma cut_semantic {prog s n g alts ca}:
  all_pred_have_cut (g :: alts) ->
    run prog n (build_goals ca g)
      [seq (build_goals ca b) | b <- alts] = Some s ->
        exists g' s', run prog n (build_goals ca g') [::] = Some s'.
Proof.
  revert g alts.
  induction n; try by [].
  destruct g as [|ghd gtl].
    inversion 1; by [].
  destruct ghd as [|p]; simpl.
    exists (cut :: gtl), s; auto.
  destruct (prog p) eqn:PP.
    unfold more_alt; simpl.
    destruct alts as [|alt alts].
      inversion 2.
    simpl.
    intros.
    eapply IHn in H0.
    destruct H0 as (?&?&?).
    exists (call p :: x); simpl.
    rewrite PP; simpl.


Section CUT_PROG.

  Context {prog : bodiesT}.
  Context (CProg : all_rules_have_cut prog).

  Lemma help {T1 l2 T2 n l1 l3}:
    all_goals_have_cut (T2 :: T1) -> all_pred_have_cut (l2 :: l3) -> 
      run prog n (save_alt T1 l2 T2) ([seq save_alt T1 b T2  | b <- l3] ++ T1) = Some l1 ->
    exists g, run prog n g T1 = Some l1.
  Proof.
    revert T1 l2 T2 l1 l3.
    destruct n; try by [].
    destruct l2 eqn:LL22.
      inversion 2; by [].
    destruct p; simpl.
      intros.
      now exists (Goal cut T1 :: ([seq Goal x T1  | x <- l] ++ T2)); auto.
    unfold more_alt in *; simpl in *.
    destruct (prog n0) eqn:PP.
      simpl.
      destruct l3.
        exists (Goal (call n0) [::] :: T2).
        rewrite PP; auto.
      simpl.
      now exists (Goal cut ([seq save_alt T1 b T2  | b <- l3] ++ T1) :: (save_alt T1 l0 T2)); auto.
    simpl.
    intros T2 l4 l5.
    pose (([seq save_alt T1 b T2  | b <- l5] ++ T1)) as S1; fold S1.
    pose ([seq Goal x T1  | x <- l2] ++ T2) as S2; fold S2.
    intros.
    now exists (Goal cut (([seq save_alt S1 b ([seq Goal x T1  | x <- l] ++ T2)  | b <- l1] ++ S1)) :: (save_alt S1 l0 ([seq Goal x T1  | x <- l] ++ T2))).
  Qed. 

  Lemma all_goals_have_cut_last {ca}:
    all_goals_have_cut ca ->  exists bef aft bef' aft' ca',
      (ca = bef ++ (bef' ++ Goal cut ca' :: aft') :: aft /\
        all_goals_have_cut aft) \/ (ca = [::] /\ ca = ca').
  Proof.
    induction ca.
      exists [::], [::], [::], [::], [::]; auto.
    inversion 1.
    apply IHca in H1 as (?&?&?&?&?&?).
    destruct H1 as [[]|[]].
      exists (a::x), x0, x1, x2, x3.
      constructor; simpl; constructor; f_equal; auto.
    subst.
    assert (all_goals_have_cut [::]) as ALL_NIL by constructor.
    specialize (IHca ALL_NIL) as (?&?&?&?&?&?).
    destruct H1 as [[]|[]].
      destruct x3; inversion H1.
    subst.
    clear H.
    induction a.
      by [].
    inversion H0.
      destruct a; subst.
      exists nil, nil, nil, a0, ca; left; repeat constructor; simpl; auto.
    specialize (IHa H) as (?&?&?&?&?&?).
    destruct H2 as [[]|[]]; try by [].
    destruct x7; inversion H2; subst.
    exists [::], [::], (a::x9), x10, x11; repeat constructor; auto.
    destruct x7; by [].
  Qed.

  Lemma bah1 {n g alts tl solution ca}:
    all_goals_have_cut ca ->
        all_pred_have_cut (g :: alts) ->
          run prog n (save_alt ca g tl)
            ([seq save_alt ca b tl  | b <- alts] ++ ca) = Some solution ->
              exists n' g1 tl ca', n' <= n /\ 
                (exists bef aft bef' aft', (ca = bef ++ (bef' ++ Goal cut ca' :: aft') :: aft /\ not (all_goals_have_cut aft))  \/ (ca = [::] /\ ca' = ca)) 
                /\ run prog n' ([seq Goal g1 ca' | g1 <- g1]++tl) ca' = Some solution.
  Proof.
    revert g alts tl solution ca.
    induction n.
      by [].
    destruct g as [|ghd gtl].
      now inversion 2.
    destruct ghd as [|p].
      simpl.
      intros.
      admit.
      (* destruct ca. *)
      (* exists n, (gtl), tl, [::]; repeat constructor; auto. *)
      (* admit. *)
    simpl.
    destruct (prog p) eqn:PP; unfold more_alt; simpl.
      admit.
      (* destruct alts as [|alt alts]; simpl.
        destruct ca as [|ca cas]; try by [].
        simpl.
        exists (n.+1), (call p :: [::]).
        simpl; rewrite PP; unfold more_alt; simpl.
        exists [::], [::ca&cas]; repeat constructor; simpl; auto. *)
      (* inversion 2.
      intro HR.
      eapply IHn in HR as [n'[g'[tl'[?[?[]]]]]].
      exists n', g', tl'; constructor; auto. *)
    move=> alts tl solution ca HCA.
    pose ([seq save_alt ca b tl  | b <- alts]) as SA; fold SA.
    pose ([seq Goal x ca  | x <- gtl] ++ tl) as SB; fold SB.
    destruct 1 as [[]?]; try by [].
    intro HR.
    eapply IHn in HR as [n'[g'[tl'[?[?[]]]]]].

    exists (n'), g', tl', x; constructor; auto.
    constructor; auto.
    admit.






    




  Lemma bah {n l l0 gs l1}:
    all_pred_have_cut (l :: l0) ->
      run prog n (save_alt [::] l (not_alt_goal gs))
        [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] = Some l1 ->
          exists g, run prog n (not_alt_goal g) [::] = Some l1.
  Proof.
    (* intros.
    assert (all_goals_have_cut [::]).
    constructor.
    epose proof (bah1 H H1 H0) as (?&?&?&?).
    apply (pumping_leq _ _ _ _ _ _ H2) in H3.
    exists x; auto. *)
    revert l l0 gs l1.
    induction n; try by [].
    destruct l; unfold save_alt; simpl.
      inversion 1; by [].
    destruct p; intros l0 gs l1; rewrite <-map_cat.
      exists (cut :: l ++ gs); simpl; auto.
    destruct (prog n0) eqn:PP; simpl.
      unfold more_alt.
      destruct l; inversion 1.
        inversion H0; by [].
      destruct l0; try by [].
      simpl.
      unfold save_alt in IHn.
      intro.
      eapply IHn in H2 as []; auto.
      (* if the goal is (p, !) and p fails then go to the choice point *)
      exists (cut :: x); simpl; auto.
      repeat rewrite map_cat_deep.
      pose ([seq [seq Goal x [::]  | x <- b ++ gs]  | b <- l0]) as T1; fold T1.
      pose ([seq Goal x [::]  | x <- l ++ gs]) as T2; fold T2.

      (*qui è difficile...*)
  Admitted.

  Lemma functional_all_with_cut: functional_prog prog.
  Proof.
    intros n.
    induction n; auto.
    destruct g as [|g gs]; simpl; auto.
    destruct g as [|p].
      apply IHn.
    destruct (prog p) eqn:?; auto.
    simpl; rewrite cats0.
    destruct r; auto.
    pose proof (CProg p) as Hp.
    rewrite Heql in Hp.
    intro.
    epose proof (bah Hp H) as [g HP].
    apply IHn in HP; auto.
  Qed.
End CUT_PROG.

Lemma all_have_cut_tail_cut_all:
  forall p, all_rules_have_cut(tail_cut_all p).
Proof.
  intros ??.
  unfold tail_cut_all.
  destruct (p f); simpl; auto.
  split.
  constructor.
  induction l; simpl; auto.

  induction l0; simpl; auto.
  constructor; auto.
  induction a; simpl; auto.
Qed.

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  intro.
  
  eapply (functional_all_with_cut).
  apply all_have_cut_tail_cut_all.
Qed.
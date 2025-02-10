From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.

Definition g2a g := match g with Goal _ a => a end.

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

Lemma good_cut_catr {a b c}:
  good_cut (a ++ b) c -> good_cut b c.
Proof. by elim: a => //= [] [] _ ca l IH /andP []. Qed.

Lemma good_cut_catl {a b c}:
  good_cut (a ++ b) c -> good_cut a c.
Proof. elim: a => //= [] [] _ ca l IH /andP [] -> B; simpl; auto. Qed.

Lemma good_lvl_more_alt {a gs tl}:
  good_levels a -> good_cut tl a -> good_levels (more_alt a gs tl).
Proof.
  elim: gs a tl => // gs0 gs IH a tl GL GC.
  rewrite more_alt_cons.
  apply /andP; split; auto.
  by apply good_cut_more_alt, good_cut_save_alt.
Qed.

(* prefix (more_alt alts bs0 (Goal (call f) ca :: l1)) (more_alt alts0 bs0 (Goal (call f) ca :: l1)) *)
Lemma more_alt_empty {ys alts l}: more_alt ys alts l = [::] -> ys = [::].
Proof. case: ys alts  => // la' l' alts.
  unfold more_alt.
  move=> H.
  have:= (erefl (@size ((seq goal)) [::])).
  rewrite -{1}H.
  rewrite size_cat /= addnS //.
Qed.

Inductive forall2 {T R:Type} P : list T -> list R -> Prop := 
  | forall2_nil : forall2 [::] [::]
  | forall2_con {x xs y ys} : P x y -> forall2 xs ys -> forall2 (x::xs) (y::ys).

Lemma forall2_refl {T : Type} (P : T -> T -> Prop) l : forall2 P l l.
Proof. elim l. constructor. Abort. 

(* Lemma forall2_cat {T: Type} (P: T->T->Prop) l1 l2: forall2 P l1 _ -> forall2 P l2 -> forall2 P (l1 ++ l2).  *)

Definition g2p g := match g with Goal g _ => g end.
Print all2.

(* Fixpoint my_prefix l1 l2 {struct l1} :=
  match l1, l2 with
  | [::], _ => true
  | x::xs, y::ys =>
    my_prefix xs ys && all2 (fun '(Goal x a1) '(Goal y a2) => (x == y) && my_prefix a1 a2) x y
  | _, _ => false
  end.  *)


Inductive my_prefix : seq alt -> seq alt -> Prop :=
  | my_prefix_nil l : my_prefix [::] l
  | my_prefix_sam {x y xs ys} : 
      forall2 (fun x y => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) x y ->
        my_prefix xs ys -> my_prefix (x :: xs) (y :: ys).



Lemma my_prefix_refl l : my_prefix l l.
Proof. 
  elim l; constructor; auto.
  elim a.
  constructor.
  intros.
  constructor.
  split.
  auto.
Abort.

Lemma my_prefix_nil_ra {l}: my_prefix l [::] -> l = [::].
Proof.
  remember [::].
  induction 1; try by [].
Qed.

Lemma my_prefix_cat {a b c d bs}: my_prefix a b -> forall2 (fun x y => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) c d -> my_prefix (more_alt a bs c) (more_alt b bs d).
Proof.
  Admitted.

Lemma my_prefix_save_alt {gl ys a alts1 b}:
  my_prefix a alts1 -> 
  forall2 (fun x y : goal => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) gl ys ->
  forall2 (fun x y : goal => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) (save_alt a b gl) (save_alt alts1 b ys).
Admitted.


Lemma prefix_cat {T:eqType} (common: seq T) l1 l2: prefix l1 l2 -> prefix (common ++ l1) (common ++ l2).
Proof. elim: common => //= c cs IH H; rewrite eqxx; auto. Qed.

Definition prefix_goal :=
   (fun g1 g2 =>
    match g1, g2 with
    | Goal g ca, Goal g' ca' => 
      g = g' /\ my_prefix ca ca' 
    end).

Lemma weaken_success' {prog alts g1 sol}:
  nur' prog g1 alts sol -> 
  good_cut g1 alts -> good_levels alts -> 

  forall G1 alts1,
    forall2 (fun x y => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) g1 G1 ->
      good_cut G1 alts1 -> good_levels alts1 ->
        my_prefix alts alts1 -> 
          exists sol', nur' prog G1 alts1 sol'.
Proof.
  elim.
  + inversion 3; subst.
    repeat econstructor.
  + move=> a ca r gl GCGL NUR IH GC GL G1 alts1.
    inversion 1; subst; clear H.
    destruct y.
    simpl in H2; destruct H2; subst.
    repeat econstructor; auto.
      admit.
    move: IH => /(_ _ _ _ _ H4 _ _ H0).
    admit.
  + move=> a g al r NUR IH.
    move=> GCG GLAAL G1.
    inversion 4; subst.
    eexists. apply Fail.

    move: IH => /(_ _ _ _ _ H5 _ _ H7).
    admit.
  + move=> a ca f b bs gl r PF NUR IH.
    move=> GC GL G1 alts1.
    inversion 1; subst; clear H.
    destruct y.
    simpl in H2.
    destruct H2; subst.
    move=> GC11 GL11 PREF.
    eexists. apply: Call PF _.
    set (G1:= save_alt alts1 b ys).
    set (alts':= more_alt alts1 bs ys).
    have FF: forall2 (fun x y : goal => g2p x = g2p y /\ my_prefix (g2a x) (g2a y)) (save_alt a b gl) G1.
      unfold G1.
      now apply my_prefix_save_alt.

    have HH: my_prefix (more_alt a bs gl) alts' .
      unfold alts'.
      by apply my_prefix_cat.
    
    move: IH => /(_ _ _ G1 alts' FF _ _ HH).
    admit.
Admitted.

(* Lemma weaken_success' {prog a b bs gl sol}:
  nur' prog (save_alt a b gl) (more_alt a bs gl) sol -> 
  forall alts,
    good_cut gl a -> good_levels a -> good_levels (gl::alts) ->
      my_prefix a alts 
      -> exists sol', nur' prog (save_alt alts b gl) (more_alt alts bs gl) sol'.
Proof.

Lemma weaken_success' {prog a b bs gl sol}:
  nur' prog (save_alt a b gl) (more_alt a bs gl) sol -> 
  forall alts,
    good_cut gl a -> good_levels a -> good_levels (gl::alts) ->
      my_prefix a alts 
      -> exists sol', nur' prog (save_alt alts b gl) (more_alt alts bs gl) sol'.
Proof.
  move=> NUR alts GC GL1 GL2 PREF.
  have: my_prefix (more_alt a bs gl) ((more_alt alts bs gl)).
  by constructor.
  remember (save_alt a b gl).
  remember (more_alt a bs gl).
  move=> NUR.
  elim: NUR a b bs gl Heql Heql0 => /=.
  + move=> aS a [] bs [] //=; repeat econstructor.
  + move=> a ca r gl GCGL NUR IH alts [|bhd btl] // bs.
      move=> [|glhd gls] //= [] H1 H2 H3; subst.
      move=> alts' /andP [SCA GCGLS] GLALTS GLALTS'.
      unfold save_alt; simpl.
      exists r; eapply Cut; auto.
    move=> gl' [] H1 H2 H3 H4; subst.
    move: IH => /(_ alts btl [::] gl' erefl erefl) => IH.
    move=> alts' A B C D.
    move : IH => /(_ _ A B C D) [sol' IH].
    rewrite save_alt_cons.
    exists sol'; eapply Cut, IH.
    apply good_cut_save_alt.
    by move: C => /andP [].
  + move=> a g al r NUR IH alts b.
    move=> [|bshd bstl].
      case: alts => // x xs gl' ? [] ? ?; subst.
      move=> [] // a l1 GC /=.
        move=> /my_prefix_nil_ra //.
      move=> /andP [GCAXS GLXS] /= /andP [] GC_GL' /andP [GC_A GL_L1].
      inversion 1; subst.
        move: IH => /(_ xs [::] [::] a erefl erefl l1 GCAXS GLXS _ H1).
        rewrite GC_A GL_L1 => /(_ isT) [{}sol IH].
        by exists sol; apply Fail.
      rewrite H1.
      unfold more_alt; simpl.
      (* eexists.
      eapply Fail. *)
      admit.
      (* move: IH => /(_ _ [::] [::] a _ _ l1).

      rewrite more_alt_cons.

      move: IH => /(_ _ b [::] gl' _ _ (more_alt ys alts l2)) => /(_ (more_alt xs0 alts l2)). *)
    move=> gl ?; subst.
    rewrite more_alt_cons => [] [] ? ?; subst.
    intros.
    rewrite more_alt_cons.
    move: IH => /(_ alts bshd bstl gl erefl erefl _ H H0 H1 H2) [{}sol IH].
    by exists sol; apply Fail.
  + move=> a ca f b bs gl r PF NUR IH alts [|bshd bstl] bs0.
      move=> [] // a0 l1 [] ? ? ? /= alts0; subst.
      move=> /andP [SCA0 GCL1 GLA] /andP [/andP []] A B C D.
      set (more_alt alts bs0 (Goal (call f) ca :: l1)) as XX.
      have AA: good_cut l1 XX.
        now apply good_cut_more_alt.
      have BB: good_levels XX.
        apply good_lvl_more_alt; auto; simpl.
        by rewrite SCA0 GCL1. 
      set (more_alt alts0 bs0 (Goal (call f) ca :: l1)) as YY.

      have DD: good_cut l1 YY && good_levels YY.
        have DD1: good_cut l1 YY.
          unfold YY.
          apply good_cut_more_alt.
          by rewrite B.
        have DD2: good_levels YY.
          unfold YY.
          apply good_lvl_more_alt; auto.
          simpl.
          by rewrite A B.
        by rewrite DD1 DD2.
      have EE: (my_prefix XX YY).
        unfold XX, YY.
        by constructor.
      move: IH => /(_ _ _ _ _ erefl erefl YY AA BB DD EE) [{}sol IH].
      by exists sol; apply: Call PF _.
    move=> gl0 [] ? ? ? ? //; subst.
    intros.
    rewrite save_alt_cons.

    have AA: (good_cut ([seq Goal x alts  | x <- bstl] ++ gl0) (more_alt alts bs0 gl0)).
      by apply good_cut_save_alt_more_alt.
    have BB: good_levels (more_alt alts bs0 gl0).
      by apply good_lvl_more_alt.

      
  (* exists sol; apply: Call PF _.  *)
    (* DA QUI *)
    have KK : save_alt (more_alt alts bs0 gl0) b ([seq Goal x alts  | x <- bstl] ++ gl0) = save_alt (more_alt alts0 bs0 gl0) b (save_alt alts0 bstl gl0).
      (* f_equal; auto. *)
      (* unfold save_alt at 3. *)
      admit.
    have JJ : more_alt (more_alt alts bs0 gl0) bs ([seq Goal x alts  | x <- bstl] ++ gl0) = more_alt (more_alt alts0 bs0 gl0) bs (save_alt alts0 bstl gl0).
      admit.
    move: IH => /(_ _ b _ (save_alt alts0 bstl gl0) KK JJ (more_alt alts0 bs0 gl0)) .
    move: H1 => /andP [] A B.
    have TT: good_cut (save_alt alts0 bstl gl0) (more_alt alts0 bs0 gl0).
      by apply good_cut_save_alt_more_alt.
    have D: good_levels (more_alt alts0 bs0 gl0).
      apply good_lvl_more_alt; auto.

    rewrite D TT => /(_ isT isT isT (my_prefix_refl _)) [{}sol IH].
    exists sol; apply: Call PF IH.
    (* A QUI *)

    eapply my_prefix_moa in H2.
    move: H1 => /andP [] A B.
    move: IH => /(_ _ _ _ _ erefl erefl _ AA BB) => /(_ (more_alt alts0 bs0 gl0) _ H2).
    have BA: good_cut ([seq Goal x alts  | x <- bstl] ++ gl0) (more_alt alts0 bs0 gl0).
      apply good_cut_cat.
      2:{ by apply good_cut_more_alt. }
      admit.

    rewrite BA (good_lvl_more_alt B A) => /(_ isT) [{}sol IH].
    eexists.
    apply: Call PF _.
    apply IH.

Admitted.


Lemma weaken_success {prog g a r}:
  nur' prog g a r -> good_levels (g::a) -> forall a1, 
     my_prefix a a1 -> good_levels (g::a1) ->
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
    move=> /IH /(_ _ (my_prefix_refl ca) GG) [sol {IH}].
    by exists sol; repeat constructor.
  + move=> {}a {}g {}al {}r NUR IH /and3P [GC_G GC_A GL_AL] [|aext1 aext] + /andP [GC_G' GC_aext] //.
      move=> /my_prefix_nil_r => /(_ (g)) [] [|aa aas] // [] ? ?; subst.
        admit.
      
    have: good_cut (save_alt [::] aa (g)) ([seq save_alt [::] b (g)  | b <- aas] ++ [::]) &&
good_levels ([seq save_alt [::] b (g)  | b <- aas] ++ [::]) by admit.

    move=> GCAAL.
    move: IH => /(_ GCAAL).
    unfold save_alt.
     aext). PREF GC_aext) [x IH].
    by exists x; apply Fail.
  + move=> {}a ca f b bs gl {}r PF NUR IH /andP [/andP []] HK1 HK2 HK3.
    have IH1: good_cut (save_alt a b gl) (more_alt a bs gl) && good_levels (more_alt a bs gl).
      by rewrite good_cut_save_alt_more_alt ?good_lvl_more_alt //.
    move: IH => /(_ IH1 (more_alt a bs gl) ) /(_ (prefix_refl _) IH1) [sol HSol] alts PREF /andP [/andP] [] A B C.

    epose proof (weaken_success' HSol _ HK2 HK3 _ PREF) as [sol'].
    (* epose proof (weaken_success' HSol _ HK2 HK3 PREF) as [sol']. *)
    by eexists sol'; apply: Call PF _.
    Unshelve.
    simpl.
    by rewrite B C.
Qed. *)

Lemma weaken_success_nil {prog g a r}:
  good_levels (g::a) ->
    nur' prog g [::] r -> good_levels (g::[::]) ->
    exists r1, nur' prog g a r1.
Proof. move=> GLGA NUR GLG .

  epose proof (weaken_success' NUR _ isT g a).

 => /weaken_success /(_ GLG a (prefix0s _) GLGA) //. Qed.

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

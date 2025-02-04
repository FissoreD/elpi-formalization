From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.

Definition g2a g := match g with Goal _ a => a end.
Definition g2p g := match g with Goal g _ => g end.

Definition make_empty_alts g := match g with Goal g _ => Goal g [::] end.
Lemma save_alt_cons {a g1 gl l}: save_alt a (g1 :: gl) l = Goal g1 a :: save_alt a gl l.
Proof. by []. Qed.
Lemma more_alt_cons {a x xs tl} : more_alt a (x::xs) tl = save_alt a x tl :: more_alt a xs tl.
Proof. by []. Qed.
Lemma more_alt_empty_alts bs xs: more_alt [::] bs xs = [seq (save_alt [::] b xs) | b <- bs].
Proof. unfold more_alt. by rewrite cats0. Qed.
Lemma more_alt_empty_gl a xs: more_alt a [::] xs = a. auto. Qed.
Lemma more_alt_empty {ys alts l}: more_alt ys alts l = [::] -> ys = [::].
Proof. case: ys alts  => // la' l' alts.
  unfold more_alt.
  move=> H.
  have:= (erefl (@size ((seq goal)) [::])).
  rewrite -{1}H.
  rewrite size_cat /= addnS //.
Qed.

Lemma map_cat_deep {T:Type} {R:Type} l gs:
  forall (P:T -> R),
  [seq [seq P x | x <- b] ++ [seq P x | x <- gs] | b <- l] = [seq [seq P x | x <- b ++ gs] | b <- l].
Proof.
  revert gs; induction l; intros; simpl; f_equal; auto.
  now rewrite map_cat.
Qed.

(* Definition functional_prog' p :=
  forall n r g a, run p n g a = r -> r = None \/ r = Some a. *)
Section Functionality.
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
End Functionality.

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

Section good_cut_and_level.

  Inductive good_cut1 : list goal -> list alt -> Prop :=
    | good_cut_nil a : good_cut1 [::] a
    | good_cut_con g ca tl a : 
      good_levels1 (tl :: ca) -> 
        suffix ca a -> 
          good_cut1 tl a -> 
            good_cut1 (Goal g ca :: tl) a

  with good_levels1 : list alt -> Prop :=
    | good_levels1_nil : good_levels1 [::]
    | good_levels1_con x xs: good_cut1 x xs -> good_levels1 xs -> good_levels1 (x::xs).

  Lemma good_lvl1_cat {l1 l2} : 
    good_levels1 (l1++l2) -> good_levels1 l2.
  Proof.  
    elim: l1 => //= x xs IH.
    inversion 1; subst; auto.
  Qed.

  Lemma good_lvl1_suffix {ca} {a}: suffix ca a -> good_levels1 a -> good_levels1 ca.
  Proof. move => /suffixP [x] -> /good_lvl1_cat //. Qed.

  Lemma good_cut1_more_alt {gs tl a tl'}:
    good_cut1 tl a -> good_cut1 tl (more_alt a gs tl').
  Proof.
    revert gs a tl'.
    unfold more_alt, save_alt.
    elim: tl => //=; try constructor.
    move=> [g ca] tl IH gs a tl'.
    inversion 1; subst.
    apply good_cut_con => //.
      now apply suffix_catr.
    eapply IH; auto.
  Qed.

  Lemma good_cut1_save_alt {a g1 tl}:
    good_cut1 tl a -> good_levels1 a -> good_cut1 (save_alt a g1 tl) a.
  Proof.
    elim: g1 => //= p L + GC GL => /(_ GC GL) IH.
    rewrite save_alt_cons.
    apply: good_cut_con => //; rewrite ?suffix_refl //.
    apply: good_levels1_con => //.
  Qed.

  Lemma good_cut1_save_alt_more_alt {a b bs gl}:
    good_cut1 gl a -> good_levels1 a -> good_cut1 (save_alt a b gl) (more_alt a bs gl).
  Proof. apply: (fun x y => good_cut1_more_alt (good_cut1_save_alt x y)). Qed.

  Lemma good_lvl1_more_alt {a gs tl}:
    good_levels1 a -> good_cut1 tl a -> good_levels1 (more_alt a gs tl).
  Proof.
    elim: gs a tl => // gs0 gs IH a tl GL GC.
    rewrite more_alt_cons.
    constructor; auto.
    by apply good_cut1_save_alt_more_alt.
  Qed.

  Lemma good_lvl1_save_alt_more_alt {a b bs gl}:
    good_levels1 a -> good_cut1 gl a ->
    good_levels1 (save_alt a b gl :: more_alt a bs gl).
  Proof.
    move=> H1 H2.
    constructor.
      by apply good_cut1_save_alt_more_alt.
    by apply good_lvl1_more_alt.
  Qed.

  Lemma good_cut1_empty l : good_cut1 [seq make_empty_alts x | x <- l] [::].
  Proof. by elim: l => /= [|[] a IH]; repeat constructor. Qed.

  Lemma save_alt_with_make_empty_alt {a g1 tl}:
    [seq make_empty_alts i  | i <- save_alt a g1 tl] = (save_alt [::] g1 [seq make_empty_alts i  | i <- tl]).
  Proof. by elim: g1 => //= g1 gl IH /=; rewrite save_alt_cons IH. Qed.

End good_cut_and_level.

Inductive nur' (p: bodiesT) : list goal -> list alt -> (list alt) -> Prop :=
| Stop a : nur' [::] a a
| Cut a (ca:list alt) r gl : good_cut1 gl ca -> nur' gl ca r -> nur' [::Goal cut ca & gl] a r
| Fail a g al r : nur' a al r -> nur' g (a :: al) r
| Call {a ca f b bs gl r} : p f = [:: b & bs ] ->
  nur' (save_alt a b gl) (more_alt a bs gl) r -> nur' [::Goal (call f) ca & gl] a r.


Section my_prefix.

  Inductive forall2 {T R:Type} P : list T -> list R -> Prop := 
    | forall2_nil : forall2 [::] [::]
    | forall2_con {x xs y ys} : P x y -> forall2 xs ys -> forall2 (x::xs) (y::ys).

  Lemma forall2_functor {T R : Type} {P Q : T -> R -> Prop}: 
    (forall x y, P x y -> Q x y) -> forall x y, forall2 P x y -> forall2 Q x y.
  Proof.
    move=> H x y.
    elim.
    constructor.
    intros.
    constructor.
    apply H.
    apply H0.
    apply H2.
  Defined.
  Print forall2_ind.


  (* Elpi derive seq.
  Check  list_induction. *)

  Lemma forall2_refl {T : eqType} (P : T -> T -> Prop) l : (forall x, x \in l -> P x x) -> forall2 P l l.
  Proof. elim l; repeat constructor; auto.
    by apply: H0; rewrite inE eqxx.
    apply: H => x IN.
    by apply: H0; rewrite inE IN orbC.
   Qed.

  (* Definition alt := seq goal. *)
  (* Inductive goal := Goal (g : pred) (ca : list (list goal)). *)
  (*   Definition g2a g := match g with Goal _ a => a end.
     Definition g2p g := match g with Goal g _ => g end. *)
     
  Definition forall2_alts P :=
    forall2 (fun x y : goal => g2p x = g2p y /\ P (g2a x) (g2a y)).

  Lemma forall2_alts_refl {P} (l: seq goal) : (forall x, x \in l -> P (g2a x) (g2a x)) -> forall2  (fun x y : goal => g2p x = g2p y /\ P (g2a x) (g2a y)) l l.
  Proof. intros. eapply forall2_refl. move=> /= x IN; split; auto. Qed.

  Inductive my_prefix : seq alt -> seq alt -> Prop :=
    | my_prefix_nil l : my_prefix [::] l
    | my_prefix_con {x y xs ys} : 
        forall2_alts my_prefix x y ->
          my_prefix xs ys -> my_prefix (x :: xs) (y :: ys).

  Section helper.

    Definition my_prefix_induction : forall P : seq alt -> seq alt -> Prop,
        (forall l : seq alt, P [::] l) ->
        (forall (x y : seq goal) (xs ys : seq alt), 
          forall2 (fun x y : goal => g2p x = g2p y /\ P (g2a x) (g2a y)) x y 
            -> my_prefix xs ys -> P xs ys 
              -> P (x :: xs) (y :: ys)) ->
        forall l1 l2 : seq alt, my_prefix l1 l2 -> P l1 l2.
    Proof.
      refine (
      fun (P : seq alt -> seq alt -> Prop) (f : forall l : seq alt, P [::] l)
  (f0 : forall (x y : seq goal) (xs ys : seq alt),
          forall2 (fun x y : goal => g2p x = g2p y /\ P (g2a x) (g2a y)) x y ->
        my_prefix xs ys -> P xs ys -> P (x :: xs) (y :: ys)) =>
  fix F (l l0 : seq alt) (m : my_prefix l l0) {struct m} : P l l0 :=
    match m in (my_prefix l1 l2) return (P l1 l2) with
    | my_prefix_nil l1 => f l1
    | @my_prefix_con x y xs ys f1 m0 => f0 x y xs ys _ m0 (F xs ys m0)
    end).
      apply: forall2_functor f1.
      intros.
      constructor; auto.
      destruct H.
      auto.
      apply F.
      destruct H.
      auto.
    Qed.
  End helper.

  Fixpoint my_prefix_refl_help (Px : forall x, forall2_alts my_prefix x x) (l : seq alt) : my_prefix l l :=
    match l return my_prefix l l with
    | [::] => my_prefix_nil [::]
    | x :: xs => 
         my_prefix_con (Px x) (my_prefix_refl_help Px xs)
    end.

  Import std.Prelude.

  (* In order to make this proof compositional we use the _induction principle
     as in https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.29
     
     The key is that induction principle are not ending in forall x : T, P x
     but rather forall x, is_T x -> P x
     where is_T is a translation of T into a predicate (param1)
     eg Inductive is_nat : nat -> Prop :=
       | is_zero : is_nat 0
       | is_succ x : is_nat x -> is_nat (S x).

      There induction principles allow to cross containes, eg have the
      induction hypothesis on the sub terms of type goal that are
      not immediate subterms (list the list elements)
        Inductive goal := Goal : .. -> (list (list goal)) -> goal.

      These induction principles don't work with elim, one has to prepare the goal
      and then apply them.
      *)

  Lemma my_prefix_refl l:  my_prefix l l.
  Proof.
    (* The fuel for _induction *)
    have H1 : is_list alt (is_list goal is_goal) l.
      by apply: is_list_inhab _ _ (is_list_inhab _ _ is_goal_inhab) l.
    (* The real property *)
    have {H1} H2:  is_list alt (is_list goal (fun x => my_prefix (g2a x) (g2a x))) l.
      move: l H1.
      (* The real inductive type is goal *)
      apply: is_list_functor=> a; apply: is_list_functor=> g {a}.
      (* induction *)
      move: g; apply: goal_induction => p Hp /=.
      apply: list_induction => [|gl Hgl gll Hgll]; first by apply: my_prefix_nil.
      apply: my_prefix_con Hgll.
      move: gl Hgl; apply: list_induction => [|g Hg gl Hgl]; first by apply: forall2_nil.
      apply: forall2_con; first by split.
      by apply: Hgl.
    (* maybe we can avoid this last part *)
    move: l H2; apply: list_induction => [|a Ha l Hl]; first by apply: my_prefix_nil.
    apply: my_prefix_con; last by apply: Hl.
    move: a Ha {l Hl}; apply: list_induction=> [|g Hg gl Hgl]; first by apply: forall2_nil.
    apply: forall2_con; first by split.
    by apply: Hgl.
    Qed.

  Lemma forall2_my_prefix_refl g: forall2_alts my_prefix g g.
  Proof. apply forall2_refl; split; auto; apply my_prefix_refl. Qed.

  Lemma my_prefix_nilr {l}: my_prefix l [::] -> l = [::].
  Proof. by remember [::]; induction 1. Qed.

  Lemma forall2_alts_my_prefix_save_alt {b gl ys a ALTS}:
    my_prefix a ALTS -> forall2_alts my_prefix gl ys -> 
      forall2_alts my_prefix (save_alt a b gl) (save_alt ALTS b ys).
  Proof.
    elim: b => //.
    move=> p ca + A B  => /(_ A B) IH.
    apply: forall2_con => //.
  Qed.

  Lemma my_prefix_more_alt {a b c d bs}: 
    my_prefix a b -> forall2_alts my_prefix c d -> my_prefix (more_alt a bs c) (more_alt b bs d).
  Proof.
    elim bs => // x xs IH H1 H2.
    move: IH => /(_ H1 H2) IH.
    rewrite !more_alt_cons.
    constructor.
      by apply forall2_alts_my_prefix_save_alt.
    by[].
  Qed.

  Lemma prefix_cat {T:eqType} (common: seq T) l1 l2: prefix l1 l2 -> prefix (common ++ l1) (common ++ l2).
  Proof. elim: common => //= c cs IH H; rewrite eqxx; auto. Qed.

End my_prefix.

Lemma weaken_success' {prog alts g1 sol}:
  nur' prog g1 alts sol -> 
  good_levels1 (g1::alts) -> 

  forall G1 ALTS,
    forall2_alts my_prefix g1 G1 ->
      good_levels1 (G1 :: ALTS) ->
        my_prefix (g1 :: alts) (G1 :: ALTS) ->
          exists sol', nur' prog G1 ALTS sol'.
Proof.
  elim.
  + inversion 2; subst.
    repeat econstructor.
  
  + move=> a ca r gl GCH NUR IH // GL G1 ALTS H.
    inversion H as [|X Y [G1_p G1_ca] G1_gl [MP_g2p MP] F2].
    simpl in MP_g2p, MP; subst; clear H.
    move=> H; inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    move=> PREF_a.
    inversion PREF_a as [|???? F21 MP1]; subst ; clear PREF_a.
    inversion F21 as [|???? [A B] _]; simpl in A; subst; clear F21 A.
    simpl in *.

    have GL_gl_ca: good_levels1 (gl :: ca).
      constructor; auto.
      inversion GL; subst.
      inversion H1; subst.
      by inversion H8; subst.

    have GL_ys_ca: good_levels1 (G1_gl :: G1_ca).
      1:{
        constructor.
        inversion H4; subst; auto.
        by epose proof (good_lvl1_suffix H6 H3).
      }

    have GG: my_prefix (gl :: ca) (G1_gl :: G1_ca) by apply: my_prefix_con.

    move: IH => /(_ GL_gl_ca G1_gl G1_ca F2 GL_ys_ca GG) [{}sol IH].
    inversion GL_ys_ca; subst.
    exists sol; apply: Cut H1 IH.

  + move=> a g al r NUR IH GL G1 ALTS F2 GL_G1.
    inversion 1; subst; inversion H5; subst.
    inversion H; subst; clear H.

    have GL_a_al: good_levels1 (a :: al) by inversion GL; subst.
    have GL_y_ys: good_levels1 (y :: ys) by inversion GL_G1; subst.

    move: IH => /(_ GL_a_al y ys H2 GL_y_ys H5) [{}sol IH].
    by exists sol; apply Fail.
  
  + move=> a ca f b bs gl r PF NUR IH /= GL G1 ALTS F2 GL_G1_ALTS MP.
    inversion MP; subst; clear MP.
    inversion H2; subst; clear H2.
    simpl in H1; destruct H1; simpl in *.
    inversion F2; subst; simpl in *; clear F2.
    clear H5.
    destruct y; simpl in *; subst.
    destruct H6; clear H.
    inversion GL_G1_ALTS; clear GL_G1_ALTS; subst; inversion H3; subst; clear H3.
    inversion GL; clear GL; subst; inversion H3; subst; clear H3.
    have GL_SA_MA: good_levels1 (save_alt a b gl :: more_alt a bs gl).
      by apply good_lvl1_save_alt_more_alt.
    have F2': forall2_alts my_prefix (save_alt a b gl) (save_alt ALTS b ys).
      by apply forall2_alts_my_prefix_save_alt.
    have GL': good_levels1 (save_alt ALTS b ys :: more_alt ALTS bs ys).
      by apply good_lvl1_save_alt_more_alt.
    have MP': my_prefix (save_alt a b gl :: more_alt a bs gl) (save_alt ALTS b ys :: more_alt ALTS bs ys).
      1: {
        constructor; auto.
        apply my_prefix_more_alt; auto.
      }

    move: IH => /(_ GL_SA_MA (save_alt ALTS b ys) (more_alt ALTS bs ys) F2' GL' MP') [{}sol IH].
    eexists sol. apply: Call PF IH.
Qed.

Lemma weaken_success_nil {prog g a r}:
  good_levels1 (g::a) ->
    nur' prog g [::] r -> good_levels1 (g::[::]) ->
    exists r1, nur' prog g a r1.
Proof.
    move=> GLGA NUR GLG .
    have MP: (my_prefix [::g] (g::a)).
      repeat constructor.
      by apply forall2_my_prefix_refl.
    have [sol IH] := weaken_success' NUR GLG g a (forall2_my_prefix_refl _) GLGA MP.
    by exists sol.
Qed.

Lemma cons_cat {T:Type} {a b c}: (a:T)::b++c = ([::a]++b)++c. by []. Qed.

Lemma cut_semantic {prog s g alts}:
    nur' prog g alts s ->
      good_levels1 (g::alts) ->
        exists g' s', g' \in (map (map make_empty_alts) (g :: alts)) 
            /\  nur' prog g' [::] s'.
Proof.
  elim => /=.
  - exists [::], [::]; repeat constructor; auto.

  - move => a ca r gl GC H /= IH /= GL. 
    inversion GL as [|gs alts' GC1 GL1 C]; subst; clear GL.
    inversion GC1 as [| P CA TL ALTS GL2 SUFF GC2]; subst; clear GC1.
    case: (IH GL2) => g' [s' [+ NUR]].
    rewrite in_cons => /orP; case.
    - move=> /eqP?; subst.
      exists (map make_empty_alts (Goal cut ca :: gl)), s'; constructor; auto.
        by rewrite inE eqxx.
      by simpl; apply: Cut => //; apply: good_cut1_empty.
    - move=> g'_ca.
      exists g', s'.
      split; last by [].
      rewrite inE orbC.
      case/suffixP: SUFF => a' ->. 
      by rewrite map_cat mem_cat g'_ca orbT.

  - move=> {}g gl al solution H + GL.
    inversion GL as [|g' a2 GC1 GL1]; subst; clear GL.
    move=> /(_ GL1) [g' [sol ]] [] IN NUR'.
    exists g', sol; auto.
    by rewrite in_cons IN orbC.

  - move=> a ca f g1 gs tl r PF NUR + GL.
    inversion GL as [|gs' alts' GC1 GL1 C]; subst; clear GL.
    inversion GC1 as [| P CA TL ALTS GL2 SUFF GC2]; subst; clear GC1.
    have GL_SA_MA: good_levels1 (save_alt a g1 tl :: more_alt a gs tl) by apply good_lvl1_save_alt_more_alt.
    move=> /(_ (good_lvl1_save_alt_more_alt GL1 GC2)) [g' [s' [+ NUR']]].
    unfold more_alt.
    rewrite map_cat cons_cat mem_cat => /orP.
    move=> [+|INA] //=.
    2:{ exists g', s'; constructor; auto; by rewrite in_cons INA orbC. }
    simpl.
    rewrite <-map_cons.
    replace (save_alt a _ _ :: [seq _ | _ <- _]) with [seq save_alt a b tl | b <- g1 :: gs ] by auto.

    move=> IN_IMPL.
    exists ((Goal (call f) [::] :: [seq make_empty_alts i  | i <- tl])).
    
    set (empty_tl:= map make_empty_alts tl).

    have GR: (g' = save_alt [::] (g1) (empty_tl) \/ g' \in [seq save_alt [::] b (empty_tl)  | b <- gs]).
      move: IN_IMPL.
      rewrite /= in_cons => /orP [/eqP |] H.
      rewrite save_alt_with_make_empty_alt in H; auto.
      right.
      congr(g' \in _) : H.
      unfold empty_tl.
      rewrite -map_comp.
      apply: eq_map.
      move=> ? /=.
      by rewrite save_alt_with_make_empty_alt.
    
    have GL_G' : good_levels1 [:: g'].
      constructor.
      destruct GR; subst.
        simpl.
        rewrite -(@save_alt_with_make_empty_alt [::]).
        apply good_cut1_empty.
      elim: gs H {PF NUR GL_SA_MA IN_IMPL} => //=.
      move=> x xs IH.
      rewrite in_cons => /orP [/eqP H |]; subst.
        rewrite -(@save_alt_with_make_empty_alt [::]).
        apply good_cut1_empty.
      auto.
      constructor.
    rewrite in_cons eqxx /=.

    have GL_G_TL: good_levels1 (g' :: more_alt [::] gs empty_tl).
      constructor.
      inversion GL_G'; subst.
      by apply good_cut1_more_alt.
      apply good_lvl1_more_alt.
        constructor.
      apply good_cut1_empty.

    case: GR => [EQ|IN].
      subst.

      have [sol {}NUR'] := @weaken_success_nil _ _ (more_alt [::] gs empty_tl) _ GL_G_TL NUR' GL_G'. 
      eexists; split; auto.
      apply: Call PF NUR'.

    suffices: exists s',  nur' prog (save_alt [::] g1 empty_tl) (more_alt [::] gs empty_tl) s'.
      move=> [sol' H'].
      eexists; split; auto.
      apply: Call PF H'.

    elim: gs  (save_alt [::] g1 empty_tl) IN NUR' {NUR PF GL_G_TL GL_SA_MA IN_IMPL} => [|x xs IH] //= G.

    rewrite in_cons => /orP [/eqP H | ].
    move=> NUR.
    have GL_G_TL: good_levels1 (g' :: more_alt [::] xs empty_tl).
      1:{
        subst.
        apply good_lvl1_save_alt_more_alt.
          constructor.
        apply good_cut1_empty.
      }

    have [sol {}NUR] := @weaken_success_nil _ _ (more_alt [::] xs empty_tl) _ GL_G_TL NUR GL_G'.
    exists sol.
    rewrite more_alt_cons.
    apply Fail.
    subst; apply NUR.
    move=> /IH IH' /IH' H.
    destruct (H (save_alt [::] x empty_tl)).
    exists x0.
    rewrite more_alt_cons.
    apply Fail.
    auto.
Qed.

Print Assumptions cut_semantic.




(* nur' p s0 (rcons gl (Goal cut ca) ++ d) (a::al) alts' s1 -> 
  good_levels () -> 
    ((nur' p s0 gl _ alts'' s01 -> nur' p s01 d ca s1) \/ (nur' p s0 a al s t'' s1)). *)

Lemma run_cut_middle {gl ca tl a al s}:
good_levels ((rcons gl (Goal cut ca) ++ tl) :: (a::al)) -> 
  nur' p (rcons gl (Goal cut ca) ++ tl) (a::al) s -> (nur' p tl ca s' \/ nur' p a al s).
Proof.
  Admitted.

Lemma run_cut_end:
nur' p (rcons gl (Goal cut ca)) (a::al) s -> good_levels () -> (nur' p d ca s' \/ nur' p a al s).
Proof.
Admitted.

Lemma run_cut_ent_empty_alts:
good_levels (rcons gl (Goal cut ca) :: [::]) ->
nur' p (rcons gl (Goal cut ca)) [::] s -> s = ca.
Proof.
Admitted.

Lemma run_cut_end:
nur' p (rcons gl (Goal cut ca)) a s -> good_levels () -> (s = [::] \/ nur' p a al s).
Proof.
Admitted.



Lemma run_cut_ent_empty_alts:
good_levels (rcons gl (Goal cut ca) :: [::]) ->
nur' p (rcons gl (Goal cut ca)) [::] s -> s = ca.
Proof.
Admitted.

Definition functional_goal'' p :=
  forall g s, nur' p (map make_empty_alts g) [::] s -> s = [::].

Lemma functional_goal_ p:
  functional_goal'' (tail_cut_all p).
Proof.
  move=> g s H1.
  remember (tail_cut_all p) as p'.
  remember [::] as el.
  remember (map make_empty_alts g) as mg.
  elim: H1 g Heqel Heqmg => //=; subst.
  + move=> a ca r gl GC NUR IH [|[gp gca] gs] ? //= [] ???; subst.
    apply: IH erefl erefl.
  + move=> a ca f b bs gl r PF NUR IH [|[gp gca] gs] //= ?[??]?; subst.
    rewrite more_alt_empty_alts in IH.
    erewrite <-save_alt_with_make_empty_alt in IH.
    move: IH => /(_ (save_alt [::] b gs) _ erefl).





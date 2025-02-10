From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.

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


Lemma same_int: forall (a:predname), a == a = true.
Proof. induction a; auto. Qed.

Lemma not_alt_goal_app:
  forall a b, not_alt_goal a ++ not_alt_goal b = not_alt_goal (a++b).
Proof.
  induction a; auto.
  intros; simpl; f_equal; auto.
Qed.

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
      rewrite <-not_alt_goal_app in IH.
      now apply IH.
Qed.

Fixpoint has_cut l :=
  match l with
  | [::] => False
  | (cut :: _) => True
  | _ :: xs => has_cut xs
  end.

Fixpoint all_has_cut (l: seq (seq pred)) :=
  match l with
  | [::] => True
  | [::x&xs] =>
    has_cut x /\ all_has_cut xs
  end.

Definition all_have_cut (p: bodiesT) :=
  forall f, all_has_cut (p f).

  Definition altsT:= ((seq (seq (seq goal)))).


Definition first_empty l :=
  match l with
  | [::] => True
  | [::Goal _ [::] & _] => True
  | _ => False
  end.

Definition had_cut :=
  (exists_ (fun g => match g with Goal g _ => g = cut end)).

Definition all_cut_alts l :=
  for_all (exists_ (fun e => match e with Goal g _ => g = cut end)) l.

Lemma had_cut_cat :
  forall a b, had_cut b -> had_cut (a ++ b).
Proof.
  induction a; auto.
  intros.
  simpl.
  unfold had_cut.
  unfold exists_.
  destruct a.
  destruct g; auto.
  right.
  now apply IHa.
  Qed.

Lemma all_cut_alts_cat:
  forall a b,
    all_cut_alts a -> all_cut_alts b -> all_cut_alts (a ++ b).
Proof.
  induction a; auto.
  inversion 1.
  intro.
  simpl.
  unfold all_cut_alts.
  simpl.
  split; auto.
  apply IHa; auto.
Qed.


Lemma ddd a gs:
  has_cut a -> exists_ (fun e : goal => match e with
| Goal g _ => g = cut
end) [seq Goal x gs  | x <- a].
Proof.
  induction a; auto.
  simpl.
  destruct a; auto.
Qed.

Lemma bbb l0: forall gs g0,
   all_has_cut l0 -> all_cut_alts [seq [seq Goal x gs  | x <- b] ++ g0  | b <- l0].
Proof.
  induction l0; auto.
  inversion 1.
  unfold all_cut_alts.
  simpl.
  split.
  apply exists_split.
  left.
  apply ddd; auto.
  apply IHl0; auto.
Qed.

Lemma split_in {T: Type}: forall (e:T) l1 l2,
  In e l1 \/ In e l2 <-> In e (l1 ++ l2).
Proof.
  split.
  destruct 1.
  induction l1; simpl; try easy.
  destruct H; auto.
  induction l1; simpl; auto.
  induction l1; auto.
  inversion 1; simpl; auto.
  apply or_assoc.
  right.
  auto.
Qed.

Inductive IN_IND (prog: bodiesT) a : list goal -> ( seq (seq goal)) -> Prop :=
  | IN_IND_OK g gs: IN_IND prog a g (g::gs)
  | IN_IND_KO g ign gs: IN_IND prog a g gs -> IN_IND prog a g (ign::gs)
  | IN_IND_RC ca a' p g gs tl :
      IN_IND prog a' g ([seq [seq Goal x a | x <- x] ++ tl | x <- prog p] ++ gs)
      ->
        IN_IND prog a g ((Goal (call p) ca :: tl) :: gs)
  .


Lemma all_goals_with_cut_more_general'' prog n r:
    all_have_cut prog ->
  forall g gs, 
  (* first_empty g -> *)
    had_cut g ->
    all_cut_alts gs ->
      run prog n g gs = r ->
      exists n' g', (exists g'' n'' a'', In g'' (g::gs) /\ run prog n'' g'' a'' =  run prog n' g' a'') /\ n' <= n /\ run prog n' g' [::] = r.
Proof.
  intro.
  induction n.
  + simpl; intros; subst.
    exists 0, g; simpl; constructor; auto.
    exists g, 0, [::]; auto.
  + destruct g.
    solve [intros; subst; inversion H0].

    destruct g.
    destruct g.
    + simpl; intros.

      exists (n.+1), (Goal cut ca :: g0); simpl.
      constructor; auto.
      rewrite H2.
      exists (Goal cut ca :: g0), n.+1, ca; auto.
    + 
      pose proof (H p) as Hp.
      destruct (prog p) eqn:PP.
1:{

      destruct gs as [|alt alts]; simpl; rewrite PP.
        * exists 0, (Goal (call p) ca :: g0); simpl; auto; constructor; auto.
          exists (Goal (call p) ca :: g0),0,[::]; auto.
        * intros.
          inversion H1.
          pose proof (IHn _ _ H3 H4 H2) as (?&?&?&?&?).
          destruct H5 as (?&?&?&?&?).

          exists x, x0; simpl; constructor; auto.
          do 3 eexists.

          constructor.
          2:{
            apply H8.
          }
          auto.
}
      simpl.
      rewrite PP.
      intros.

      unfold had_cut, exists_ in H0; destruct H0; try by []; apply had_cut_cat with (a:=[seq Goal x gs  | x <- l]) in H0.
      destruct Hp as [Hp1 Hp2].
      epose proof (all_cut_alts_cat _ _ (bbb _ gs g0 Hp2) H1) as AC.

      (*REVERT BELOW*)
      epose proof (IHn _ _ H0 AC H2) as (?&?&?&?&?).
      exists x, (x0).
      constructor; auto.
      destruct H3 as (?&?&?&?&?).
      inversion H3.
      subst x1.
      exists (Goal (call p) ca :: g0), (x2.+1).
      simpl.
      rewrite PP.
      
      auto.

      do 3 eexists.
      constructor.
      2:{
        apply H6.
      }
      auto.
    Qed.

Definition all_goals_with_cut_more_general := all_goals_with_cut_more_general''.


(* 

Inductive IN_IND (prog: bodiesT) : list goal -> ( seq (seq goal)) -> Prop :=
  | IN_IND_OK g gs: IN_IND prog g (g::gs)
  | IN_IND_KO g ign gs: IN_IND prog g gs -> IN_IND prog g (ign::gs)
  | IN_IND_RC ca (a:seq (seq goal)) p g gs tl :
      IN_IND prog g ([seq [seq Goal x a | x <- x] ++ tl | x <- prog p] ++ gs)
      ->
        IN_IND prog g ((Goal (call p) ca :: tl) :: gs)
 *)

Lemma all_not_alt_goal_IND_with_cut_prog prog g tl gs x0:
  all_have_cut prog ->
  has_cut g -> all_has_cut gs ->
   IN_IND prog [::] x0 
    (not_alt_goal (g ++ tl) :: [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl  | b <- gs]) -> 
        exists y, not_alt_goal y = x0.
Proof.
Admitted.


Lemma all_goals_with_cut prog n r:
  forall g gs tl, all_have_cut prog ->
    all_has_cut (g :: gs) ->
      (* in all goal (g::gs) we have a bang and each of them has no cut-alternatives,
            therefore, 
              -if a goal g' in (g::gs) succeeds, we have
                the same result as running the goal g' alone (the alternative being rejected)
              -otherwise, if all goals fails, the lemma is trivial
            
       *)
      run prog n (not_alt_goal (g ++ tl)) 
        [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl | b <- gs] = r
        
      (* next_alt (not_alt_goal (g ++ tl) :: [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl | b <- gs])
        (run prog n) *)
        
         ->
      exists g n', n' <= n /\ run prog n' (not_alt_goal g) [::] = r.
Proof.
  intros.


  epose proof (all_goals_with_cut_more_general prog n r H (not_alt_goal (g++tl)) [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl
 | b <- gs] _ _ H1) as (?&?&?&?&?).
  destruct H0.
  destruct H2 as (?&?&?&?&?).
  simpl in H2.

  destruct H2.



  destruct (all_not_alt_goal_IND_with_cut_prog _ _ _ _ _ H H0 H5 H2).
  exists x1, x.
  rewrite H6; auto.
  Unshelve.
  rewrite <-not_alt_goal_app.
  apply exists_split.
  left.
  apply ddd.
  inversion H0; auto.
  inversion H0.
  clear H1 H0 H H2 g.
  induction gs.
  auto.
  simpl.
  unfold  all_cut_alts.
  simpl.
  split.
  apply exists_split.
  left.
    apply ddd.
    simpl in H3.
    easy.
    apply IHgs.
    simpl in H3.
    easy.

Qed.

Lemma functional_all_with_cut:
  forall prog, all_have_cut prog -> functional_prog prog.
Proof.
  unfold all_have_cut.
  intros prog H n.
  induction n; auto.
  simpl.
  destruct g as [|g gs]; simpl; auto.
  destruct g as [|p].
  apply IHn.
  destruct (prog p) eqn:?.
  auto.
  rewrite cats0.
  rewrite not_alt_goal_app.
  intro.
  destruct r; auto.
  pose proof (H p) as Hp.
  rewrite Heql in Hp.
  apply all_goals_with_cut in H0 as [?[?[]]]; auto.
  epose proof (pumping_leq _ _ _ _ _ _ H0 H1).
  eapply IHn.
  apply H2.
Qed.

Lemma all_have_cut_tail_cut_all:
  forall p, all_have_cut(tail_cut_all p).
Proof.
  unfold tail_cut_all.
  intros ??.
  destruct (p f); simpl; auto.
  split.
  induction l; simpl; auto.
  destruct a; auto.
  induction l0; simpl; auto.
  constructor; auto.
  induction a; simpl; auto.
  destruct a; auto.
Qed.

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  intro.
  now pose proof (functional_all_with_cut (tail_cut_all p) (all_have_cut_tail_cut_all p)).
Qed.




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
  | [::] => False
  | [::x] => has_cut x
  | [::x&xs] =>
    has_cut x /\ all_has_cut xs
  end.

Definition all_have_cut (p: bodiesT) :=
  forall f, p f <> [::] /\ all_has_cut (p f).

(* Lemma next_alt_help prog p n:
forall a befs aft l0 r,
prog p = [::] ->
  next_alt
([seq [seq Goal x a  | x <- b] ++
rcons (not_alt_goal befs) (Goal (call p) [::]) ++ aft
 | b <- l0] ++ a) (run prog n) = r ->
  exists n', next_alt a (run prog n') = r.
Proof.
Admitted. *)

Lemma cut_does_cut prog n: forall gs befs aft l0 r,
   run prog n (not_alt_goal (rcons (gs ++ befs) cut ++ aft))
    [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal (rcons befs cut ++ aft) | b <- l0] = r -> 
        exists gs', run prog n (not_alt_goal (rcons (gs' ++ befs) cut ++ aft)) [::] = r.
Proof.
  induction n.
  exists [::]; simpl; auto.
  simpl.
  destruct gs as [|g gs]; simpl.
  1:{
      destruct befs as [|bef befs]; simpl.
      now exists ([::]).
      destruct bef as [|p]; [exists [::]; auto|].
      destruct (prog p) eqn:PP.
      1:{
        move => aft [|G GS]; simpl.
        1:{
          inversion 1; exists (call p :: [::]); simpl; rewrite PP; auto.
        }
        replace  ([seq Goal x [::]  | x <- G] ++ Goal (call p) [::] :: not_alt_goal (rcons befs cut ++ aft)) with
                (not_alt_goal (rcons (rcons G (call p) ++ befs) cut ++ aft)).
        2:{
            rewrite rcons_cat.
            rewrite <-cats1.
            do 2 rewrite <-catA.
            rewrite <-not_alt_goal_app; f_equal.
          }
          intros.

          (* apply failing_goal in H.
          specialize (IHn _ _ _ _ _ H). *)
          admit.
      }
      admit.
  }
  admit.
          
Admitted.

Lemma func_after_bang prog:
  forall bef aft,
    functional_goal prog aft -> 
      functional_goal prog (rcons bef cut ++ aft).
Proof.
  intros.
  intros ?.
  revert bef.
  induction n; auto.
  simpl.
  destruct bef as [|bef befs]; simpl.
  1:{
      intros.
      eapply H.
      apply H0.
   }
   destruct bef.
   1:{
    apply IHn.
   }
   destruct (prog p) eqn:?; auto.
   intros r.
   rewrite cats0.
   rewrite not_alt_goal_app.
   rewrite catA.
   rewrite <-rcons_cat.
   intros.
   eapply cut_does_cut in H0 as[].
   epose proof (IHn _ _ H0); auto.
Qed.

(* Lemma xxxxx gs GS:
  [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal gs  | b <- [seq rcons x cut  | x <- GS]] =
  [seq (not_alt_goal (b++gs)) | b <- [seq rcons x cut  | x <- GS]].
      f_equal.
      apply functional_extensionality; intros. *)

Lemma map_app {T:Type} {S:Type}:
  forall (f: T -> S) l1 l2, [seq f x | x <- l1] ++ [seq f x | x <- l2] = [seq f x | x <- l1 ++ l2].
  Admitted.

(* Lemma pop_goal prog r n:
  forall g1 a,
    forall k, run prog k g1 a = Some r
    -> forall g2, run prog (n+k) (g1 ++ g2) a = Some r.  *)

  (* TODO: if we have bang wherever, then exists one of them
  producing the same result *)

  (* 
  
  run prog n (not_alt_goal (l ++ gs))
[seq [seq Goal x [::]  | x <- b] ++ not_alt_goal gs
 | b <- l0] = r
   *)


Lemma all_have_cut'' prog n: forall l l0 ls gs r l1,
  all_has_cut l1 ->
    all_has_cut (l::l0)->
      let T:=[seq [seq Goal x0 [::]  | x0 <- b] ++ not_alt_goal gs  | b <- l1] in
  run prog n ([seq Goal x T  | x <- l] ++ not_alt_goal (ls ++ gs))
      ([seq [seq Goal x T  | x <- b] ++ not_alt_goal (ls ++ gs)  | b <- l0] ++ T) =
r -> exists n', 
  n' <= n /\
    run prog n' (not_alt_goal (l ++ gs)) 
      [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal gs  | b <- l0] = r.
Proof.
  simpl; intros.
  destruct r.
  2:{ exists 0; auto. }
Admitted.

Lemma all_have_cut_general prog n:
all_have_cut prog ->
    forall gs tl (ll:seq (seq goal)) r, all_has_cut gs ->
      next_alt [seq [seq Goal x ll | x <- b] ++ tl | b <- gs] (run prog n) = Some r ->
        exists g n', n' <= n /\ run prog n' ([seq Goal x ll | x <- g] ++ tl) ll = Some r. (*g ∈ gs*)
Proof.

  (* enough (forall n tl (ll:seq (seq goal)) r, all_has_cut gs ->
      next_alt [seq not_alt_goal (b++tl) | b <- gs] (run prog n) = Some r ->
        exists g n', n' <= n /\ run prog n' ([seq Goal x [::] | x <- g]) [::] = Some r (*g ∈ gs*)) by admit.
  intro. *)
  intros HProg.
  induction n; move=> [] // g gs.
  destruct g.
  intros; simpl in H; destruct gs; try easy.
  destruct p.
  simpl; move=> tl ll r _ H. exists (g), n; constructor; auto.

    
  destruct (prog p) eqn:PP.
  simpl; rewrite PP.
  destruct gs; try by [].
  move=> tl ll r [C1 C2].
  simpl.
  intros.
  specialize (IHn (l::gs) tl ll r C2).

  simpl in IHn.
  apply IHn in H as (?&?&?&?).
  exists x, x0; auto.

  move=> tl ll r H.
  simpl.
  rewrite PP.
  assert (all_has_cut (g::gs)).
  auto.
  pose (
    [seq Goal x [seq [seq Goal x0 ll  | x0 <- b] ++ tl | b <- gs] | x <- l] 
      ++ [seq Goal x ll  | x <- l] ++ tl) as T.
  fold T.

  (* rewrite <-map_app. *)
  (* epose proof (IHn _ ([seq Goal x ll  | x <- l] ++ tl) 
    ([seq [seq Goal x0 ll  | x0 <- b] ++ tl  | b <- gs]) r H0). *)
  epose proof (IHn _ _
    _ r H0).
  simpl in H1.
  Unshelve.
  3:{ apply [seq [seq Goal x0 ll  | x0 <- b] ++ tl  | b <- gs]. }
  Admitted.
  



Lemma all_have_cut' prog n:
    forall gs tl (ll:seq (seq goal)) r, all_has_cut gs ->
      next_alt [seq [seq Goal x [::] | x <- b] ++ not_alt_goal tl | b <- gs] (run prog n) = Some r ->
        exists g n', n' <= n /\ run prog n' ([seq Goal x [::] | x <- g]) [::] = Some r. (*g ∈ gs*)
Proof.

  (* enough (forall n tl (ll:seq (seq goal)) r, all_has_cut gs ->
      next_alt [seq not_alt_goal (b++tl) | b <- gs] (run prog n) = Some r ->
        exists g n', n' <= n /\ run prog n' ([seq Goal x [::] | x <- g]) [::] = Some r (*g ∈ gs*)) by admit.
  intro. *)

  induction n; move=> [] // g gs.
  destruct g.
  intros; simpl in H; destruct gs; try easy.
  destruct p.
  simpl; move=> tl _ r _; rewrite map_app; exists (g++tl), n; auto.
  destruct (prog p) eqn:PP.
  simpl; rewrite PP.
  destruct gs; try by [].
  move=> tl _ r [C1 C2].
  simpl.
  intros.
  specialize (IHn (l::gs) tl [::] r C2).

  simpl in IHn.
  apply IHn in H as (?&?&?&?).
  exists x, x0; auto.

  move=> tl _ r H.
  simpl.
  rewrite PP.
  rewrite map_app.
  simpl.
  epose proof (IHn _ tl _ r H).
  simpl in H0.


  simpl in H0.
  (* apply pumping1 in H0. *)
 


  (* induction eapply IHn; apply H0.
  destruct (prog p) as [|sol sols] eqn:PP; auto.
  rewrite cats0.
  destruct r; auto.
  intro.
  unfold not_alt_goal in IHn.
  specialize (H p) as [? ALL_CUT].
  rewrite PP in ALL_CUT.
  pose proof (all_have_cut' _ _ _ _ [::] _ ALL_CUT H0) as [gg[nn [leq HH]]].
  apply (pumping_leq _ _ _ _ _ _ leq) in HH.
  now pose proof (IHn _ _ HH).
Qed. gs as [|g gs]; [by []|]; simpl in *.
  destruct gs; simpl in *.
  intros.
  exists (g ++ tl); simpl.
  rewrite map_app in H0.
  exists n; auto.
  ------
  destruct H as [CUT_G CUT_GS].
  specialize (IHgs CUT_GS).
  intros.
  repeat rewrite map_app in H.
  specialize (IHgs (g ++ tl) n ll r). *)

Admitted.

Lemma functional_all_with_cut:
  forall prog, all_have_cut prog -> functional_prog prog.
Proof.
  unfold all_have_cut.
  intros prog H n.
  induction n; auto.
  simpl.
  destruct g as [|g gs]; simpl; auto.
  destruct g as [|p].



Admitted.

  (* intros; eapply IHn; apply H0.
  destruct (prog p) as [|sol sols] eqn:PP; auto.
  rewrite cats0.
  destruct r; auto.
  intro.
  unfold not_alt_goal in IHn.
  specialize (H p) as [? ALL_CUT].
  rewrite PP in ALL_CUT.
  pose proof (all_have_cut' _ _ _ _ [::] _ ALL_CUT H0) as [gg[nn [leq HH]]].
  apply (pumping_leq _ _ _ _ _ _ leq) in HH.
  now pose proof (IHn _ _ HH).
Qed. *)

Fixpoint In {A:Type} (a:A) (l:list A) : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.

(* Lemma blah prog n l:
  forall G GS gs,
    run (tail_cut_all prog) n (not_alt_goal (rcons G cut ++ gs))
[seq not_alt_goal (b ++ gs)  | b <- [seq rcons x cut  | x <- GS]] = Some l ->
    exists G', run (tail_cut_all prog) n (not_alt_goal G') [::] = Some l.
Proof.
  elim: n=> // n IH.
  intro.
  destruct (rcons G cut) as [|G' GS'] eqn:RC.
  destruct (rcons_non_empty _ _ RC).
  destruct G'.
  1:{ simpl.
    intros.
    destruct G; inversion RC; subst; clear RC.
    2:{
      specialize (IH G [::] gs).
      simpl in IH.
      specialize (IH H) as [].
      exists (cut :: rcons G cut ++ gs); simpl; auto.
    }
    simpl in H.
    exists (cut :: gs).
    now simpl.
  }
  intros GS gs.
  simpl.
  unfold tail_cut_all.
  destruct (prog p) eqn:?; simpl.
  destruct GS.
  by [].
  simpl.
  fold_tail_cut_all prog.
  
  intros.
  specialize (IH _ _ _ H) as [].
  exists (cut :: x); auto.

  fold_tail_cut_all prog.
  intros.
Admitted. *)


(* Lemma all_have_cut_tail_cut_all:
  forall p, all_have_cut(tail_cut_all p).
Proof.
  unfold tail_cut_all.
  intros ??.
  destruct (p f); simpl; auto.
  2:{ split; auto. destruct l0. inversion 1.
      simpl. }
  split.
  intros ?.
  destruct (p f); simpl in H.
  destruct (rcons_non_empty _ _ H).
  simpl.
  induction f. *)

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  (* intros ??.
  induction n; auto. *)
  intros prog n r.
  elim: n => /=.
  - move => _ ->; auto.
  - move=> n IH; destruct r; auto.
    assert (IH' : forall g : seq pred, run (tail_cut_all prog) n (not_alt_goal g) [::] = Some l ->
      Some l = Some [::]).
    intros; destruct (IH _ H); by[].
    clear IH.

    destruct g as [|g gs]; auto; simpl.
    destruct g as [|p].
    + intros.
      right; eapply IH'.
      apply H.
    + unfold tail_cut_all.
      destruct (prog p) as [|G GS] eqn:?; auto; simpl.
      fold_tail_cut_all prog.
      rewrite not_alt_goal_app.
      intros.
      right.
      rewrite cats0 in H.
      assert (H':[seq [seq Goal x [::]  | x <- b] ++ not_alt_goal gs  | b <- [seq rcons x cut  | x <- GS]] =
        [seq (not_alt_goal (b++gs)) | b <- [seq rcons x cut  | x <- GS]]).
      f_equal.
      apply functional_extensionality; intros.
      now rewrite not_alt_goal_app.
      rewrite H' in H.
      clear H'.

Admitted.




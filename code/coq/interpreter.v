From mathcomp Require Import all_ssreflect.
From det Require Import aux.
From det Require Import program.

Definition next_alt {T:Type} a (k : list goal -> list alt -> option  T) :=
  if a is [:: gl & a] then k gl a
  else None.

Fixpoint run (prog: bodiesT) n gs a : option (list alt) :=
match n, gs with
| O, _ => None
| _, [::] => Some (a)
| S n, [:: Goal p ca & gs] =>
  match p with
  | cut => run prog n gs ca
  | call p =>
    match prog p with
    | [::] => next_alt a (run prog n)
    | [:: b & bs ] => 
      let save_alt b := ([seq Goal x a | x <- b] ++ gs) in
      run prog n (save_alt b) ([seq (save_alt b) | b <- bs] ++  a)
    end
  end
end.

Section prefix.
  (* Context {T : Type}. *)

  Print nat_rect.

  Inductive prefix: (list (list goal)) -> (list (list goal)) -> Prop :=
    | prefEmpty : forall l, prefix [::] l
    | prefCons  :
      forall x xs y ys,
        prefix_goal y x -> prefix xs ys -> prefix (x::xs) (y::ys) with

  prefix_goal : (list goal) -> (list goal) -> Prop :=
    | prefgEmpty  : forall l, prefix_goal [::] l
    (* | prefgCons  :
      forall (x:goal) y xs ys,
        x = y ->
        prefix_goal xs ys -> prefix_goal (x::xs) (y::ys) *)
    | prefgCons g x y xs ys:
        prefix y x ->
        prefix_goal xs ys ->
        prefix_goal (Goal g x :: xs) (Goal g y :: ys)
        .

  Scheme prefix_prefix_goal_rec := Induction for prefix Sort Prop
  with prefix_goal_prefix_rec := Induction for prefix_goal Sort Prop.

  Lemma prefix_id: forall {a}, prefix a a.
  Proof.
    (* induction a; constructor; auto.
    induction a.
    constructor.
    destruct a.
    constructor; auto. *)

  Admitted.

  Lemma prefix_goal_id: forall {a}, prefix_goal a a.
    (* induction a; repeat constructor.
    destruct a; repeat constructor; auto.
    apply prefix_id.
    (* apply prefix_id. *)
  Qed. *)
  Admitted.

  Lemma prefix_goal_app_same_hd:
    forall hd l1 l2,
      prefix_goal l1 l2 -> 
        prefix_goal (hd ++ l1) (hd ++ l2).
  Proof.
    induction hd; intros; try constructor; auto.
    destruct a.
    simpl.
    econstructor.
    apply prefix_id.
    auto.
  Qed.

  Lemma prefix_goal_hard l:
    forall g1s ys a1 a2,
    prefix_goal g1s ys ->
      prefix a2 a1 ->
        prefix_goal ([seq Goal x a1  | x <- l] ++ g1s) ([seq Goal x a2  | x <- l] ++ ys).
  Proof.
    induction l; auto.
    intros.
    simpl.
    constructor 2; auto.
    (* constructor; auto. *)
  Qed.

  Lemma prefix_hard: 
    forall l0 GS ys A A',
      prefix_goal GS ys ->
        prefix A' A ->
          prefix ([seq [seq Goal x0 A'  | x0 <- b] ++ ys  | b <- l0] ++ A')
            ([seq [seq Goal x0 A  | x0 <- b] ++ GS  | b <- l0] ++ A).
    Proof.
    induction l0; intros; auto.
    simpl.
    econstructor; auto.
    eapply prefix_goal_hard; auto.
  Qed.

End prefix.

(* 
  If the interpretation of a list goals [g1,...,gn] with a list of alternatives [a1,...,an]
  fails, then the execution of a list of [g1,...,gn,g(n+1),...,gm] with a list of
  alternatives [a1,...,ak] (with k <= n) also fails.
  Rephrased, let G is a list of goal with a list of alternatives A
    if run N P G A fail for a given depth and program, then
      given G' such that G is a prefix of G' (that is we have more goals to solve)
        and A' such that A' is a prefix of A (that is we have less alternatives) 
          then run N P G' A' also fails
 *)
Lemma run_alternatives_none prog n:
  forall G G', prefix_goal G G' ->
    forall A A', prefix A' A ->
      run prog n G A = None ->
        run prog n G' A' = None.
Proof.
  induction n; auto.
  move=> [|G GS] G' HG; inversion HG; subst; clear HG.
  - (*G is empty*)
    by [].
  - (*G is not empty*)
      destruct g.
      (*the goal is a cut*)
      * simpl.
        intros.
        eapply IHn.
        3:{ apply H0. }
        auto.
        auto.
      * (*the goal is a call*)
        simpl; destruct (prog p).
        + (*no solution for prog p*)
          move=> [|A AS] A' HA; inversion HA; subst; auto.
          intros.
          eapply IHn.
          3:{ apply H . }
          auto.
          auto.
        + intros.
          eapply IHn.
          3:{ apply H0. }
          apply prefix_goal_hard.
          auto.
          auto.
          apply prefix_hard; auto.
Qed.

Fixpoint pop_tl {T:Type} (l1: seq T) (l2: seq T) :=
  match l1, l2 with
  | [::],_ => l2
  | _ :: _, [::] => l2 (*should be unreachable*) 
  | _::x, _ ::y => pop_tl x y
  end.

(* Se lancio con meno goal e più alternative allora ho successo *)
(* le alternative nell'ipotesi vanno aggiunte alla differenza con le nuove alts *)
Lemma run_alternatives_some prog n:
  forall G G', prefix_goal G' G ->
    forall A A', prefix A A' ->
      forall a1, run prog n G A = Some a1 ->
        exists a2, run prog n G' A' = Some a2.
Proof.
  induction n; [by[]|].
  move=> [|G GS] G' HG.
  - (*G is empty*)
    inversion HG; subst; intros.
    exists A'; auto.
  - (*G is not empty*)
      inversion HG; subst; clear HG.
      intros; exists A'; auto.
      simpl in *.
      + (*g is a cut*)
        destruct g.
        intros.
        eapply IHn.
        apply H3.
        apply H2.
        apply H0.
      + (*g is a call*) 
        destruct (prog p).
        * (*no sol for prog p*)
          move=> [|A AS] A' HA; inversion HA; subst; [by[]|].
          intros.
          eapply IHn.
          apply H1.
          apply H5.
          apply H.
        * intros.
          epose proof (IHn _ _ _ _ _ _ _ H0) as [].
          eexists.
          apply H1.
          Unshelve.
          apply prefix_goal_hard; auto.
          apply prefix_hard; auto.
Qed.

(* Lemma run_alternatives_some' prog n:
  forall G G', prefix_goal G' G ->
    forall A A', prefix A A' ->
      forall a1, run prog n G [::] = Some a1 ->
        exists a2, run prog n G' A' = Some a2.
Proof.
  (* intros. *)
  (* epose proof (run_alternatives_some _ _ _ _ _ _ _ _ _ H1) as []. *)


  induction n; [by[]|].
  move=> [|G GS] G' HG; inversion HG; subst.
  - (*G is empty*)
    eexists; reflexivity.
  - (*G is not empty*)
      simpl.
      destruct G.
      destruct g as [|p].
      + (*g is a cut*)
        intros.
        epose proof (IHn _ _ H3 _ _ prefix_id _ H0) as [].
        exists x.
        eapply H1.
      + (*g is a call*) 
        destruct (prog p).
        * (*no sol for prog p*)
          move=> [|A AS] A' HA; inversion HA; subst; [by[]|].
          intros.
          epose proof (IHn _ _ prefix_goal_id _ _ H4 _ H) as [].
          eexists.
          apply H0.
        * admit.
Admitted. *)

Lemma run_alternatives_same_goal prog n G:
  forall A A', prefix A A' ->
    forall a1, run prog n G A = Some a1 ->
      exists a2, run prog n G A' = Some a2.
Proof.
  intros.
  pose proof (run_alternatives_some prog n G _ prefix_goal_id _ _ H _ H0).
  auto.
Qed.


Lemma pumping p1 n:
  forall g a ss,
    run p1 n g a = Some ss ->
      forall k, run p1 (n+k) g a = Some ss.
Proof.
  elim: n => // n IH [] /=.
  + inversion 1; auto; subst.
  + move=> [] [] p; auto.
    destruct (p1 p) eqn:?.
    + move=> _ _ [] // /= [] //.
    + move=> _ l1 a; auto.
Qed.

Lemma pumping1 p1 n:
  forall g a ss,
    run p1 n g a = Some (ss) ->
      run p1 (S n) g a = Some (ss).
Proof.
  intros.
  rewrite <-add_1_r.
  by apply pumping.
Qed.

Lemma pumping_add prog g a r:
  forall n n' n'', n + n' = n'' ->
    run prog n g a = Some r ->
      run prog n'' g a = Some r.
Proof.
  intros.
  apply (pumping) with (k := n') in H0.
  now subst.
Qed.

Lemma pumping_leq prog g a r:
  forall n n', n <= n' ->
    run prog n g a = Some r ->
      run prog n' g a = Some r.
Proof.
  intros.
  apply leq_add in H as [].
  subst.
  eapply pumping_add.
  reflexivity.
  auto.
Qed.


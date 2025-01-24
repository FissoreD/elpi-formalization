From mathcomp Require Import all_ssreflect.
From det Require Import aux.
From det Require Import program.

Definition next_alt {T:Type} a (k : list goal -> list alt -> option  T) :=
  if a is [:: gl & a] then k gl a
  else None.

Definition save_alt a b gs := ([seq Goal x a | x <- b] ++ gs).
Definition more_alt a bs gs := [seq (save_alt a b gs) | b <- bs] ++ a.


Fixpoint run_old (prog: bodiesT) n gs a : option (list alt) :=
match n, gs with
| O, _ => None
| _, [::] => Some (a)
| S n, [:: Goal p ca & gs] =>
  match p with
  | cut => run_old prog n gs ca
  | call p =>
    match prog p with
    | [::] => next_alt a (run_old prog n)
    | [:: b & bs ] => 
      let save_alt b := ([seq Goal x a | x <- b] ++ gs) in
      run_old prog n (save_alt b) ([seq (save_alt b) | b <- bs] ++ a)
    end
  end
end.

Fixpoint run (prog: bodiesT) n gs a : option (list alt) :=
match n, gs with
| O, _ => None
| _, [::] => Some (a)
| S n, [:: Goal p ca & gs] =>
  match p with
  | cut => run prog n gs ca
  | call p => next_alt (more_alt a (prog p) gs) (run prog n)
  end
end.

Lemma run_same_as_run_old: forall p n gs a, run p n gs a = run_old p n gs a.
Proof.
  induction n; auto.
  simpl.
  destruct gs; auto.
  destruct g; auto.
  destruct g; auto.
  destruct (p n0) eqn:?; auto; unfold more_alt, save_alt; simpl; intros; auto.
  destruct a; simpl; auto.
Qed.

Module Ideal.

Inductive nur (p: bodiesT) : list goal -> list alt -> (list alt) -> Prop :=
| Stop a : nur [::] a a
| Cut a ca r gl : nur gl ca r -> nur [::Goal cut ca & gl] a r
| Call a ca f b bs gl r : p f = [:: b & bs ] -> nur (save_alt a b gl) (more_alt a bs gl) r -> nur [::Goal (call f) ca & gl] a r
| Fail a g al r : nur a al r -> nur g (a :: al) r.


Lemma correct p g a r n :
  run p n g a = Some r -> nur p g a r.
Proof.
elim: n g a r => //= n IH g a r.
case: g => [[->]|g gl]; first by apply: Stop.
case: g => -[|f] ca;first by move/IH=> ?; apply: Cut.
case E: (p f) => [|c cl]; first by case: a => [//|a1 an /= /IH ?]; apply: Fail.
by move/IH=> H; apply: Call H.
Qed.

(*

l'implementazione funzionale usa Fail solo quando le altre non si
possono usare, mentrce nur lo può fare quando vuole, quindi run non può
essere completo (e.g. se il programma looppa run non ne esce, nur si).


*)

End Ideal.

Module Elpi.

Inductive nur (p: bodiesT) : list goal -> list alt -> (list alt) -> Prop :=
| Stop a : nur [::] a a
| Cut a ca r gl : nur gl ca r -> nur [::Goal cut ca & gl] a r
| Call a ca f b bs gl r : p f = [:: b & bs ] -> nur (save_alt a b gl) (more_alt a bs gl) r -> nur [::Goal (call f) ca & gl] a r
| Fail a al ca f gl r : p f = [::] -> nur a al r -> nur [::Goal (call f) ca & gl] (a :: al) r.


Lemma correct p g a r n :
  run p n g a = Some r -> nur p g a r.
Proof.
elim: n g a r => //= n IH g a r.
case: g => [[->]|g gl]; first by apply: Stop.
case: g => -[|f] ca;first by move/IH=> ?; apply: Cut.
case E: (p f) => [|c cl]; first by case: a => [//|a1 an /= /IH ?]; apply: Fail.
by move/IH=> H; apply: Call H.
Qed.

Lemma complete p g a r :
  nur p g a r -> exists n, run p n g a = Some r.
elim.
- by exists 1.
- by move=> a' ca r' gl' H [n Hn]; exists n.+1 => /=.
- move=> gl1 gl2 f c cl gl r' Df H [n Hn]; exists n.+1 => /=.
  by rewrite Df.
- move=> gl1 a11 ca1 f gl r' Df H [n Hn]; exists n.+1 => /=.
  by rewrite Df.
Qed.

(* Io proverei a rifare det.v usando Elpi.nur *)


End Elpi.


Section pumping.
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
      + move=> _ l1 a; simpl; auto.
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
End pumping.

(* x
Section prefix.
  (* Context {T : Type}. *)

  Print nat_rect.

  Inductive prefix_alt: (list (list goal)) -> (list (list goal)) -> Prop :=
    | prefEmpty : forall l, prefix_alt [::] l
    | prefCons  :
      forall x xs y ys,
        prefix_goal y x -> prefix_alt xs ys -> prefix_alt (x::xs) (y::ys) with

  prefix_goal : (list goal) -> (list goal) -> Prop :=
    | prefgEmpty  : forall l, prefix_goal [::] l
    (* | prefgCons  :
      forall (x:goal) y xs ys,
        x = y ->
        prefix_goal xs ys -> prefix_goal (x::xs) (y::ys) *)
    | prefgCons g x y xs ys:
        prefix_alt y x ->
        prefix_goal xs ys ->
        prefix_goal (Goal g x :: xs) (Goal g y :: ys)
        .

  Scheme prefix_prefix_goal_rec := Induction for prefix_alt Sort Prop
  with prefix_goal_prefix_rec := Induction for prefix_goal Sort Prop.

  Lemma prefix_id: forall {a}, prefix_alt a a.
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
      prefix_alt a2 a1 ->
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
        prefix_alt A' A ->
          prefix_alt ([seq [seq Goal x0 A'  | x0 <- b] ++ ys  | b <- l0] ++ A')
            ([seq [seq Goal x0 A  | x0 <- b] ++ GS  | b <- l0] ++ A).
    Proof.
    induction l0; intros; auto.
    simpl.
    econstructor; auto.
    eapply prefix_goal_hard; auto.
  Qed.

End prefix_alt.

(* 
  If the interpretation of a list goals [g1,...,gn] with a list of alternatives [a1,...,an]
  fails, then the execution of a list of [g1,...,gn,g(n+1),...,gm] with a list of
  alternatives [a1,...,ak] (with k <= n) also fails.
  Rephrased, let G is a list of goal with a list of alternatives A
    if run N P G A fail for a given depth and program, then
      given G' such that G is a prefix_alt of G' (that is we have more goals to solve)
        and A' such that A' is a prefix_alt of A (that is we have less alternatives) 
          then run N P G' A' also fails
 *)
Lemma run_alternatives_none prog n:
  forall G G', prefix_goal G G' ->
    forall A A', prefix_alt A' A ->
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
        simpl; destruct (prog _).
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
    forall A A', prefix_alt A A' ->
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
        destruct (prog _).
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
    forall A A', prefix_alt A A' ->
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
  forall A A', prefix_alt A A' ->
    forall a1, run prog n G A = Some a1 ->
      exists a2, run prog n G A' = Some a2.
Proof.
  intros.
  pose proof (run_alternatives_some prog n G _ prefix_goal_id _ _ H _ H0).
  auto.
Qed.

Inductive prefix {T:Type} : list T -> list T -> Prop :=
  | prefixNil l1 : prefix [::] l1
  | prefixCon e l1 l2 : prefix l1 l2 -> prefix (e::l1) (e::l2).

Definition fstT {P Q R: Type} (a: (P * Q * R)) :=
  match a with (a,_,_) => a end.
Definition sndT {P Q R: Type} (a: (P * Q * R)) :=
  match a with (_,a,_) => a end.
Definition trdT {P Q R: Type} (a: (P * Q * R)) :=
  match a with (_,_,a) => a end.


Lemma run_alternative_success_more_alternatives {prog n g gs l a1} :
  run prog n (g++gs) a1 = Some l ->
    forall a2, exists l', run prog n g (a1++a2) = Some l'.
Proof.
  revert g l a1 gs.
  induction n.
  by [].
  simpl.
  destruct g.
  + inversion 1; subst. intros.
    now eexists; reflexivity.
  + destruct g.
    destruct g; simpl.
    + intros.
      specialize (IHn _ _ _ _ H [::]).
      rewrite cats0 in IHn.
      auto.
    + destruct (prog p) eqn:?; intros.
      - destruct a1; simpl in *.
        discriminate.
        rewrite <-(cats0 a) in H.
        specialize (IHn _ _ _ _ H); auto.
      -
        (* Search ((_++_)++_). *)
        rewrite catA in H.
        specialize (IHn _ _ _ _ H).


        (* assert (prefix ([seq [seq Goal x a1  | x <- b] ++ g0  | b <- l0] ++ a1) ([seq [seq Goal x a1  | x <- b] ++ g0  | b <- l0] ++ a2)) by admit.
        specialize (IHn _ H1) as [AA IH]. *)
Admitted.
  

Lemma run_alternative_success {prog n g al l} :
  run prog n g al = Some l ->
   (exists g' l',  In g' (g :: al) /\ run prog n g' [::] = Some l').
Proof.
  revert al n l.
  induction g as [|[gl ca] g']; intros.
  + destruct n; [by []|].
    simpl in H.
    inversion H; subst.
    exists [::], [::]; simpl; auto.
  + (*g is now: (Goal gl ca) :: g' *)

    destruct n; [by[]|].
    simpl in H.
    destruct gl as [|p].
    - (*gl is cut*)
      simpl.
      exists (Goal cut ca :: g').
      exists l; auto.
    - (*gl is call p*)
      destruct (prog p) as [|sol sols] eqn:?.
      + (*p has no solution: going into alts*)
        destruct al as [|alt alts]; [by[]|].
        (* 
          alts are non empty: running `prog n alt alts` give Some l
          The solution is found in the alternatives of the program
         *)
        simpl in H.
        (*MH: The IH is useless...*)
        admit.
      + (*p has solution*)
        eapply run_alternative_success_more_alternatives with (a2:=[::]) in H.
        destruct H.
        simpl.
        exists (Goal (call p) ca :: [::] ).
        rewrite Heql0.
        exists x.
        constructor; auto.
        (* apply run_alternative_success_more_alternatives in H. *)
Abort.

Lemma run_alternative_success {prog n g al l} :
  run prog n g al = Some l ->
   (exists g' l',  In g' (g :: al) /\ run prog n g' [::] = Some l').
Proof.
  revert g al l.
  induction n.
  + by [].
  + destruct g as [|g gs].
    - simpl; inversion 1; subst.
      exists [::], [::]; auto.
    - destruct g as [gl ca].
      (*g is now: (Goal gl ca) :: gs *)
      destruct gl as [|p].
      * (*cut case*)
        simpl.
        exists (Goal cut ca :: gs), l; auto.
      * (*call case*)
        simpl.
        destruct (prog p) eqn:PP.
        ++ (*prog p = [::]*)
          destruct al; simpl; [by[]|].
          intros.
          specialize (IHn _ _ _ H) as (?&?&?&?).
          destruct H0; subst.
          assert (l = x0 ++ al) by admit.
          subst.
          (*STUCK...*)
Abort.

 *)

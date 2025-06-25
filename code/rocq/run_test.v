From mathcomp Require Import all_ssreflect.
From det Require Import lang.


Module Test1.

  Module U <: Unif.
    Definition unify    (t1 t2 : Tm) (s : Sigma) :=
      match t1, t2 with
      | Code (v X), _ => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t2 else s.(sigma) x) |} | Some t => if t == t2 then Some s else None end
      | _, Code (v X) => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t1 else s.(sigma) x) |} | Some t => if t == t1 then Some s else None end
      | _, _ => if t1 == t2 then Some s else None
      end.

    Definition matching (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.
  End U.

  Module Run := Run(U).
  Import Run.

  Definition v_X := Code (v 0).
  Definition pred_q x  := Comb (Code (p 1)) x.
  Definition pred_p x  := Comb (Code (p 0)) x.
  Definition pred_r x  := Comb (Code (p 2)) x.
  Definition pred_fail := Code (p 100).

  Definition p_test : program := {|
    modes := (fix rec (t : Tm) := match t with Comb h _ => o :: rec h | Code _ | Data _ => [::] end);
    sig := (fun _ => b (d Pred));
    rules := [:: 
      mkR (pred_p (Data 1)) [::] ;
      mkR (pred_p (Data 2)) [::] ;
      mkR (pred_r (Data 2)) [::] ;
      mkR (pred_q (Data 1)) [:: Call (pred_p v_X) ; Call (pred_r v_X) ] 
    ];
  |}.

  Notation "X &&& Y" := (And X _ Y) (at level 3).
  Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
  Notation "` X" := (Goal _ (Call X)) (at level 3).
  (* Notation "[ x -> _]" := {| sigma := (fun x : V => _) |} (x binder). *)

  Definition s1 := {| sigma := (fun x => if x == 0 then Some (Data 1) else None) |}.
  Definition s2 := {| sigma := (fun x => if x == 0 then Some (Data 2) else None) |}.

  Goal exists r, run empty (Goal p_test (Call (pred_q (Data 1)))) (Done s2 r).
  Proof.
    do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_step => //=.
      rewrite /big_or/F/select/=.
      apply: expanded_fail => //=.
    - apply: next_alt_ok => //=.
    - apply: run_backtrack => //.
      - apply: expanded_step => //=.
        rewrite /big_or/F/select/= -/s1 -/s2.
        apply: expanded_fail => //=.
      - apply: next_alt_ok => //=.
      - apply: run_backtrack => //.
        - apply: expanded_step => //=.
          apply: expanded_step => //=.
          apply: expanded_fail => //=.
        - apply: next_alt_ok => //=.
        - apply: run_backtrack => //.
          - apply: expanded_step => //=.
            apply: expanded_step => //=.
            rewrite /big_or/F//=.
            apply: expanded_fail => //=.
          - apply: next_alt_ok => //=.
          - apply: run_done.
            apply: expanded_step => //=.
            apply: expanded_step => //=.
            apply: expanded_done => //=.
  Qed.
End Test1.

Module Test2.
  Import ARun.
  Goal expand empty (Or OK empty OK) = Solved empty (Or OK empty OK) . by []. Qed.
  Goal forall p, run empty (Or (Goal p Cut) empty OK) (Done empty (Or OK empty KO)).
    move=> pr //=.
    eexists. apply: run_done => //=. 
    apply: expanded_step => //=.
    by apply: expanded_done. 
  Qed.

  Goal forall p, 
    run empty (Or (Goal p Cut) empty (Or OK empty OK)) (Done empty (Or OK empty (cut ((Or OK empty OK))))).
    move=> p; eexists.
    apply: run_done.
    apply: expanded_step => //=.
    apply: expanded_done => //=.
  Qed.

  Goal run empty (Or OK empty (Or OK empty OK)) (Done empty (Or OK empty (((Or OK empty OK))))).
  Proof. eexists; apply: run_done => //=. apply: expanded_done => //=. Qed.
End Test2.

Module Test3.

  Module Run := Run(AxiomUnif).
  Import Run.

  Lemma xxx {s A A' sA}:
    expand s A = Solved sA A' -> expand sA A' = Failure KO ->
      run s A (Done sA A') ->
        forall C SC, run s (And A KO C) (Failed SC) -> next_alt s SC None ->
          forall D SD, run s (And A KO D) (Failed SD) -> next_alt s SD None ->
            forall B CD0 r s', run s (And (Or A s B) CD0 (Or C sA D)) (Done s' r) ->
              exists r', run s (And B CD0 CD0) (Done s' r').
  Proof.
  Abort.
End Test3.

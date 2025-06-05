From mathcomp Require Import all_ssreflect.

Inductive D := Func | Pred.
Inductive B := Exp | d of D.
Inductive mode := i |o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).

Definition P := nat.
Definition K := nat.
Definition V := nat.
Inductive C := p of P | v of V.
Inductive Tm := 
  | Code : C -> Tm
  | Data : K -> Tm
  | Comb : Tm -> Tm -> Tm.
  (* | Lam  : V -> S -> Tm -> S -> Tm. *)
Record R_ {A} := { pred : P; args : list Tm; premises : list A }.
Inductive A :=
  (* | Cut *)
  (* | Call : C -> A *)
  | App : C -> list Tm -> A.
  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).

Definition Sigma := V -> option Tm.
Definition empty : Sigma := fun _ => None.

Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
Axiom matching : Tm -> Tm -> Sigma -> option Sigma.

Definition index := list R.
Definition mode_ctx := P -> list mode.
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx }.

(* Inductive goal := Goal of program & Sigma & A. *)

Axiom H : list mode -> list Tm -> list Tm -> Sigma -> option Sigma.
Fixpoint select argsI (modes:list mode) (rules: list R) sigma :=
  match rules with
  | [::] => [::]
  | rule :: rules =>
    match H modes argsI (rule.(args)) sigma with
    | None => select argsI modes rules sigma
    | Some sigma' => (sigma', rule) :: select argsI modes rules sigma
    end
  end.

Definition F pr pname args s :=
  let rules := pr.(rules) in
  let modes := pr.(modes) pname in
  let rules := select args modes rules s in
  rules.

Inductive state :=
  | KO : state
  | OK : Sigma -> state
  | Goal : program -> Sigma -> A -> state
  | Or  : state -> state -> state
  | And : state -> state -> state. 

Fixpoint big_and pr (s : Sigma) (a : list A) : state :=
  match a with
  | [::] => OK s
  | x :: xs => And (Goal pr s x) (big_and pr s xs)
  end.

Fixpoint big_or pr (s : seq (Sigma * R)) : state :=
  match s with 
  | [::] => KO
  | (s,r) :: xs => Or (big_and pr s r.(premises)) (big_or pr xs)
  end.

Inductive Res :=
  | ResY : Sigma -> state -> Res
  | ResN.

Fixpoint change_subst (st:state) (s:Sigma) :=
  match st with
  | KO => KO
  | OK _ => OK s
  | Goal pr _ a => Goal pr s a
  | Or l r => Or (change_subst l s) (change_subst r s)
  | And l r => And (change_subst l s) (change_subst r s)
end.

Inductive run : state -> Res -> Prop :=
  | run_top s : run (OK s) (ResY s KO)
  | run_fail : run KO ResN
  | run_or_ok S1 S2 s S1' : 
      run S1 (ResY s S1') ->
      (* =========Success or=========> *)
      run (Or S1 S2) (ResY s (Or S1' S2))
  | run_or_ko S1 S2 r : 
      run S1 ResN ->
      run S2 r ->
      (* ========Backtracking========> *)
      run (Or S1 S2) r
  | run_and x xs s st1 res:
      run x (ResY s st1) ->
      run (Or (change_subst xs s) (And st1 xs)) res ->
      (* ======And with success======> *)
      run (And x xs) res
  | run_call_pred pr pn args s res:
      run (big_or pr (F pr pn args s)) res ->
      (* =======Call with pred=======> *)
      run (Goal pr s (App (p pn) args)) res
  | run_call_var pr vn pn args s res:
      s vn = Some (Code (p pn)) -> (* TODO: Comb -> App *)
      run (Goal pr s (App (p pn) args)) res ->
      (* =======Call with var========> *)
      run (Goal pr s (App (v vn) args)) res.

Lemma run_consistent:
  forall {s r1 r2}, run s r1 -> run s r2 -> r1 = r2.
Proof.
  move=> s r1 + H.
  elim: H.
  by inversion 1.
  by inversion 1.
  move=> ???? H IH ? H1.
    inversion H1; subst; auto.
      apply IH in H4.
      inversion H4; subst; repeat f_equal.
    by apply IH in H3.
  move=> ??? H IH H1 H2 ? H3.
    inversion H3; subst; auto.
      by apply IH in H6.
  move=> ????? H IH H1 H2 H3 H4.
    inversion H4; subst.
    apply IH in H6; inversion H6; subst.
    by apply H2 in H8.
  move=> ????? H IH > H1.
    by inversion H1; auto.
  move=> ?????? H H1 IH ? H2.
    inversion H2; subst.
      rewrite H in H7; inversion H7; subst.
      by apply IH in H8.
Qed.

Lemma or_fail {g1 g2}:
  run (Or g1 g2) ResN -> run g2 ResN.
Proof.
  remember (Or _ _).
  remember ResN.
  move=> H.
  move: g1 g2 Heqs Heqr.
  elim H; try by [].
  by move=> ??? H1 IH H2 IH1 ?? [] ???; subst.
Qed.

Lemma or_fail_left {g1 g2 r}:
  run g1 ResN -> run (Or g1 g2) r -> run g2 r.
Proof.
  remember (Or _ _).
  move=> + H.
  move: g1 g2 Heqs.
  elim: H; try by [].
  + move=> ???? H IH ?? [] ?? H1; subst.
    by pose proof (run_consistent H1 H).
  + by move=> ??? H IH H1 IH1 ?? [] ?? H2; subst.
Qed.

Lemma or_assoc g1 g2 g3 r1 r2: 
  run (Or g1 (Or g2 g3)) r1 -> run (Or (Or g1 g2) g3) r2 -> r1 = r2.
Proof.
  remember (Or _ _) as OR eqn:HOR.
  move=> H.
  move: r2 g1 g2 g3 HOR.
  elim: H; try by [].
  move=> ?? s ? H IH ? g1 g2 g3 [] ?? H1; subst.
  {
    inversion H1; subst;clear H1.
    inversion H4; subst; clear H4.
      pose proof (run_consistent H1 H).
    inversion H0; subst; clear H0.
    assert (exists st, run (Or (Or g1 g2) g3) (ResY s st)).
      eexists.
      constructor.
      constructor.
      apply H1.
      
      admit. (*Mh, *)
    by pose proof (run_consistent H2 H).
    inversion H3; subst.
    by pose proof (run_consistent H H2).
  }
  move=> ??? H IH H1 IH2 ???? [] ?? H2; subst.
  inversion H2; subst; clear H2.
    {
      inversion H5; subst; clear H5.
        by pose proof (run_consistent H H2).
      inversion H1; subst; clear H1.
        pose proof (run_consistent H5 H6).
        by injection H0; intros; subst; auto.
      by pose proof (run_consistent H4 H6).
    }
    eapply or_fail in H4.
    apply (or_fail_left H4) in H1.
    apply (run_consistent H1 H6).
Admitted.



Lemma or_fails g1 g2 r:
  run (Or g1 g2) ResN ->
    run g1 r -> r = ResN.
Proof.
  move=> + H.
  move: g2.
  elim: H.
  by inversion 1; subst; inversion H3.
  by [].
  move=> ???? H IH ? H1.
    inversion H1; subst; clear H1.
    by apply IH in H3.
  move=> ??? H IH H1 H2 ? H3.
    eapply H2.
    inversion H3; subst.
    auto.




Lemma run_pref_none g g1 a1 a2 r:
  run (Or g (Or a1 a2)) ResN ->
  run (Or (And g g1) a1) r ->
  r = ResN.
Proof.
  (* move=> H.
  inversion H; subst; clear H.
  inversion H4; subst; clear H4.
  move=> H; inversion H; clear H; subst.
    inversion H5; clear H5; subst. *)

  move=> H.
  remember ResN as resN eqn:HresN.
  remember (Or _ _) as or eqn:Hor.
  move: a1 a2 g HresN g1 r Hor.
  elim: H => //.
  move=> ??? H /(_ _ _ _ erefl) IH H1 + ????; subst.
  move=> /(_ _ _ _ erefl) IH1 ?? [] ??; subst.
  move=> H2.
  inversion H1; subst; clear H1.
  inversion H; clear H.
  {
    (* KO *)
    subst.
    inversion H2; subst; clear H2.
    by inversion H5; subst; inversion H2.
    inversion H3; subst; inversion H2.
  }
  {
    (* OR KO *)
    subst.
    inversion H2; subst; clear H2.
    inversion H8; subst; clear H8.
    {
      exfalso.
      inversion H0; subst; clear H0.
      {
        inversion H5; subst; clear H5.
        inversion H2.
        admit.
     }

      inversion 

    }
    inversion H5; subst; clear H5.
    admit.
    admit.
    admit.
  }
  {
    subst.
    inversion H2; clear H2; subst.
      inversion H8; subst; clear H8.
      inversion H5; subst; clear H5.
      
    exfalso.
    inversion H5; subst; clear H5.
    by inversion H2.
    inversion H1; subst.

  }
    



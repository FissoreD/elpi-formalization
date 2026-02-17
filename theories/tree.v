From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export finmap lang.

Unset Elimination Schemes.

(*BEGIN*)
(*SNIP: tree_def*)
Inductive tree :=
  | KO | OK | TA of Atom
  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
  | Or  of option tree & Sigma & tree 
  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
  | And of tree & seq Atom & tree.
(*ENDSNIP: tree_def*)
  (* | PiImpl : V -> R_ A -> A -> A. *)

Set Elimination Schemes.

Lemma tree_ind : forall P,
  P KO ->
  P OK ->
  (forall a : Atom, P (TA a)) ->
  (forall (l : tree), P l -> forall (s : Sigma) (t : tree), P t -> P (Or (Some l) s t)) ->
  (forall (s : Sigma) (t : tree),
    P t -> P (Or None s t)) ->
  (forall t : tree,
  P t -> forall (l : seq Atom) (t0 : tree), P t0 -> P (And t l t0)) ->
  forall t : tree, P t.
Proof.
  move=> P H1 H2 H3 H4 H5 H6.
  fix IH 1.
  move=> []; only 1,2,3: by clear IH; auto.
    by move=> [l|] s r; [apply: H4|apply: H5].
  by move=> >; apply: H6.
Qed.

Ltac elim_tree T X := revert X; elim: T => [||t|A HA sm B HB|sm B HB|A HA B0 B HB]; intros X => //; auto.
Tactic Notation "elim_tree" hyp(T) hyp_list(X) := elim_tree T X.

#[only(eqbOK)] derive tree.
HB.instance Definition _ := hasDecEq.Build tree tree_eqb_OK.

(*SNIP: tag*)
Inductive tag := Expanded | CutBrothers | Failed | Success.
(*ENDSNIP: tag*)
derive tag.
HB.instance Definition _ := hasDecEq.Build tag tag_eqb_OK.

Definition is_fl := eq_op Failed.
Definition is_cb := eq_op CutBrothers.
Definition is_sc := eq_op Success.

Section tree_op.

  (********************************************************************)
  (* STATE OP DEFINITIONS                                             *)
  (********************************************************************)


  (*SNIP: next*)
  Fixpoint next s t : Sigma * tree:=
    match t with
    | TA _ | KO | OK => (s, t)
    | Or None s' B => next s' B
    | Or (Some A) _ _ => next s A
    | And A _ B => 
      let (s', pA) := next s A in
      if pA == OK then next s' B
      else (s', pA)
    end.
  (*ENDSNIP: next*)


  (*SNIP: next_aux *)
  (*SNIP: next_subst*)
  Definition next_subst s t := (next s t).1.
  (*ENDSNIP: next_subst*)
  (*SNIP: next_tree*)
  Definition next_tree t := (next empty t).2.
  (*ENDSNIP: next_tree*)

  (*SNIP: succ_path*)
  Definition success t := next_tree t == OK.
  (*ENDSNIP: succ_path*)
  (*SNIP: failed_path*)
  Definition failed t := next_tree t == KO.
  (*ENDSNIP: failed_path*)
  (*SNIP: incomplete*)
  Definition incomplete t := 
      if next_tree t is TA _ then true else false.
  (*ENDSNIP: incomplete*)
  (*ENDSNIP: next_aux *)

  (* This cuts away everything except for the only path with success *)
  Fixpoint cutl A :=
    match A with
    | TA _ | KO => KO
    | OK => A
    | And A B0 B =>
      if success A then And (cutl A) B0 (cutl B)
      else KO
    | Or None s B => Or None s (cutl B)
    | Or (Some A) s B => Or (Some (cutl A)) s KO
    end.

  (********************************************************************)
  (* STATE OP PROPERTIES                                              *)
  (********************************************************************)

  Lemma next_treeP A s: (next s A).2 = next_tree A .
  Proof. 
    rewrite/next_tree; elim_tree A s => //=; rewrite !push HA.
    by case: ifP => //=; rewrite !HB.
  Qed.

  Lemma next_tree_or_Some A s B: next_tree (Or (Some A) s B) = next_tree A.
  Proof. by rewrite/next_tree next_treeP. Qed.

  Lemma next_tree_or_None s B: next_tree (Or None s B) = next_tree B.
  Proof. by rewrite/next_tree/= next_treeP. Qed.

  Lemma next_tree_and A B0 B: next_tree (And A B0 B) = if success A then next_tree B else next_tree A.
  Proof. rewrite /success/next_tree/=push !fun_if !next_treeP; case: next => //=; case: next_tree => //. Qed.

  Lemma failed_success A: failed A -> success A = false.
  Proof. by rewrite/failed/success => /eqP->. Qed.

  Lemma success_incomplete A: success A -> incomplete A = false.
  Proof. by rewrite/success/incomplete => /eqP->. Qed.

  Lemma incomplete_failed A: incomplete A -> failed A = false.
  Proof. by rewrite/incomplete/failed; case: next_tree. Qed. 

  Lemma success_failed A: success A -> failed A = false.
  Proof. by apply: contraTF => /failed_success ->. Qed.

  Lemma success_or_None sm B: success (Or None sm B) = success B.
  Proof. by rewrite/success/next_tree/= next_treeP. Qed.

  Lemma success_or_Some A sm B: success (Or (Some A) sm B) = success A.
  Proof. by rewrite/success/next_tree/= !next_treeP. Qed.

  Lemma success_and A sm B: success (And A sm B) = success A && success B.
  Proof. rewrite/success/next_tree/= push !fun_if/= !next_treeP; case:next_tree => //. Qed.

  Lemma failed_or_None sm B: failed (Or None sm B) = failed B.
  Proof. by rewrite/failed/next_tree/= !next_treeP. Qed.

  Lemma failed_or_Some A sm B: failed (Or (Some A) sm B) = failed A.
  Proof. by rewrite/failed/next_tree/= !next_treeP. Qed.

  Lemma failed_and A sm B: failed (And A sm B) = failed A || (success A && failed B).
  Proof. rewrite/failed/success/next_tree/= !push fun_if/= !next_treeP; case p: next_tree => //=. Qed.

  Lemma success_cut {A} : success (cutl A) = success A.
  Proof.
    elim_tree A => //=.
      by rewrite !success_or_None.
    by rewrite fun_if !success_and HA HB; case: success.
  Qed.

  Lemma failed_success_cut {A}: failed (cutl A) = ~~ (success (cutl A)).
  Proof.
    elim_tree A => //=.
      by rewrite failed_or_None success_or_None.
    rewrite 3!fun_if success_and failed_and HA HB; do 2 case: success => //.
  Qed.

  Lemma success_failed_cut {A}: success (cutl A) = ~~ (failed (cutl A)).
  Proof. rewrite failed_success_cut; case: success => //. Qed.

  Lemma failed_cut {A}: failed A -> failed (cutl A).
  Proof. by rewrite failed_success_cut success_cut => /failed_success->. Qed.
End tree_op.

Definition step_res := (tag * tree)%type.

Fixpoint big_andA x xs : tree :=
  match xs with
  | [::] => TA x
  | y :: ys => And (TA x) xs (big_andA y ys)
  end.

Definition big_and (a : list Atom) : tree :=
  match a with
  | [::] => OK
  | x :: xs => big_andA  x xs
  end.

Fixpoint big_or (r : list Atom) (l : seq (Sigma * seq Atom)) : tree :=
  match l with 
  | [::] => big_and r
  | (s,r1) :: xs => Or (Some (big_and r)) s (big_or r1 xs)
  end.

Section main.
  Variable u: Unif.

  (*SNIP: step_sig*)
  Definition step : program -> fvS -> Sigma -> tree -> (fvS * tag * tree) := 
  (*ENDSNIP: step_sig*)
    fix step pr fv s A :=
    let step := step pr in
    match A with
    (* meta *)
    | OK             => (fv, Success, OK)
    | KO             => (fv, Failed, A)
    
    (* lang *)
    | TA cut       => (fv, CutBrothers, OK)
    | TA (call t)  => 
      let: (fv, l) := bc u pr fv t s in
      (fv, Expanded, if l is ((s, r) :: xs) then (Or None s (big_or r xs))
                     else KO)
    (* recursive cases *)
    | Or A sB B =>
        if A is Some A then 
          let: (fv, tA, rA) := step fv s A in
          (fv, if is_cb tA then Expanded else tA, Or (Some rA) sB (if is_cb tA then KO else B))
        else
          let: (fv, tB, rB) := (step fv sB B) in
          (fv, if is_cb tB then Expanded else tB, Or A sB rB)
    | And A B0 B =>
        if success A then 
          let: (fv, tB, rB) := (step fv (next_subst s A) B) in
          (fv, tB, And (if is_cb tB then cutl A else A) B0 rB)
        else let: (fv, tA, rA) := step fv s A in (fv, tA, And rA B0 B)
    end.

    Lemma step_and A B0 B pr fv s: (step pr fv s (And A B0 B)).2 = 
        if success A then 
          And (if is_cb (step pr fv (next_subst s A) B).1.2 then cutl A else A) B0 (step pr fv (next_subst s A) B).2
        else And (step pr fv s A).2 B0 B.
    Proof. by rewrite/=!push; case: ifP => //=. Qed.

  (* prune takes a tree "T" returns a new tree "T'" representing the next
     alternative wrt "T", if no new alternative exists, None is returned.
     prune takes a boolean b to know if a successful path should be erased in
     "T".
  *)
  (*SNIP: prune_code *)
  (*SNIP: prune*)
  Definition prune : bool -> tree -> option tree :=
  (*ENDSNIP: prune*)
    fix prune b A :=
    match A with
    | KO => None
    | OK => if b then None else Some OK
    | TA _ => Some A
    | And A B0 B =>
      let build_B0 A := And A B0 (big_and B0) in
      if success A then
        match prune b B with
        | None => omap build_B0 (prune true A)
        | Some B' => Some (And A B0 B')
        end
      else if failed A then omap build_B0 (prune false A) 
      else Some (And A B0 B)
    | Or None sB B => omap (fun x => Or None sB x) (prune b B)
    | Or (Some A) sB B =>
        match prune b A with
        | None => omap (fun x => Or None sB x) (prune false B)
        | Some A' => Some (Or (Some A') sB B)
       end
  end.
  (*ENDSNIP: prune_code *)

  Goal forall r, prune false (And (Or (Some OK) empty OK) r KO) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, prune false (And (Or (Some OK) empty OK) r KO) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, prune true (And (Or (Some OK) empty OK) r OK) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> []//=. Qed.

  Goal (prune false (Or (Some KO) empty OK)) = Some (Or None empty OK). move=> //=. Qed.

  (* Definition optT := option tree.
  Definition optC t : optT := Some t.
  Coercion optC : tree >-> optT.

  Definition ST : Type := (Sigma * optT).
  Definition optST := option ST.
  Definition opt_ST ST : optST := Some ST.
  Coercion opt_ST: ST >-> optST. *)

  Notation "tg == CutBrothers" := (is_cb tg).
  (*prooftree: runbp*)
  (*SNIP: run_sig *)
  Inductive runT (p : program): fvS -> Sigma -> tree 
            -> option (Sigma * option tree) -> bool -> fvS -> Prop :=
  (*ENDSNIP: run_sig *)
    | StopT s s' t t' v              : success t -> next_subst s t = s' -> prune true t = t' -> runT v s t (Some (s', t')) false v
    | StepT s r t t' b b' v v' v'' tg: incomplete t -> step p v s t = (v', tg, t') -> b' = (tg == CutBrothers) || b -> runT v' s t' r b v'' -> runT v s t r b' v''
    | BackT s t t' r n v v'          : failed t -> prune false t = Some t' -> runT v s t' r n v' -> runT v s t r n v'
    | FailT s t v                   : prune false t = None -> runT v s t None false v.
  (*endprooftree: runbp*)

  Fixpoint vars_tree t : fvS :=
  match t with
  | TA cut | KO | OK => fset0
  | TA (call t) => vars_tm t
  | And A B0 B => vars_tree A `|` vars_tree B `|` vars_atoms B0
  | Or None s B => vars_tree B `|` vars_sigma s
  | Or (Some A) s B => vars_tree A `|` vars_tree B `|` vars_sigma s
  end.

End main.

Ltac elim_run T X := revert X; elim: T; clear; 
  [ move=> s1 s2 A B v0 sA ?? |
    move=> s1 r A B b1 b2 v0 v1 v2 st pA eA ? rB IH|
    move=> s1 A B r n v0 v1 fA nA rB IH |
    move=> s1 A v0 nA ]; intros X; subst => //; auto.
Tactic Notation "elim_run" hyp(T) hyp_list(X) := elim_run T X.

(*END*)

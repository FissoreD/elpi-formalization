From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export finmap lang.

Unset Elimination Schemes.

(*BEGIN*)
(*SNIP: tree_def*)
Inductive tree :=
  | KO | OK | TA of A
  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
  | Or  of option tree & Sigma & tree 
  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
  | And of tree & seq A & tree.
(*ENDSNIP: tree_def*)
  (* | PiImpl : V -> R_ A -> A -> A. *)

Set Elimination Schemes.

Lemma tree_ind : forall P,
  P KO ->
  P OK ->
  (forall a : A, P (TA a)) ->
  (forall (l : tree), P l -> forall (s : Sigma) (t : tree), P t -> P (Or (Some l) s t)) ->
  (forall (s : Sigma) (t : tree),
    P t -> P (Or None s t)) ->
  (forall t : tree,
  P t -> forall (l : seq A) (t0 : tree), P t0 -> P (And t l t0)) ->
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

(*SNIP: step_tag*)
Inductive step_tag := Expanded | CutBrothers | Failed | Success.
(*ENDSNIP: step_tag*)
derive step_tag.
HB.instance Definition _ := hasDecEq.Build step_tag step_tag_eqb_OK.

Definition is_fl := eq_op Failed.
Definition is_cb := eq_op CutBrothers.
Definition is_sc := eq_op Success.

Section tree_op.

  (********************************************************************)
  (* STATE OP DEFINITIONS                                             *)
  (********************************************************************)


  (*SNIP: get_end*)
  Fixpoint get_end s A : Sigma * tree:=
    match A with
    | TA _ | KO | OK => (s, A)
    | Or None s1 B => get_end s1 B
    | Or (Some A) _ _ => get_end s A
    | And A _ B => 
      let (s', pA) := get_end s A in
      if pA == OK then get_end s' B
      else (s', pA)
    end.
  (*ENDSNIP: get_end*)


  (*SNIP: get_subst*)
  Definition get_subst s A := (get_end s A).1.
  (*ENDSNIP: get_subst*)

  (*SNIP: path_end*)
  Definition path_end A := (get_end empty A).2.
  (*ENDSNIP: path_end*)

  (*SNIP: succ_path*)
  Definition success A := path_end A == OK.
  (*ENDSNIP: succ_path*)

  (*SNIP: failed_path*)
  Definition failed A := path_end A == KO.
  (*ENDSNIP: failed_path*)

  (*SNIP: path_atom*)
  Definition path_atom A := 
      if path_end A is TA _ then true 
      else false.
  (*ENDSNIP: path_atom*)

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

  Lemma path_endP A s: (get_end s A).2 = path_end A .
  Proof. 
    rewrite/path_end; elim_tree A s => //=; rewrite !push HA.
    by case: ifP => //=; rewrite !HB.
  Qed.

  Lemma path_end_or_Some A s B: path_end (Or (Some A) s B) = path_end A.
  Proof. by rewrite/path_end path_endP. Qed.

  Lemma path_end_or_None s B: path_end (Or None s B) = path_end B.
  Proof. by rewrite/path_end/= path_endP. Qed.

  Lemma path_end_and A B0 B: path_end (And A B0 B) = if success A then path_end B else path_end A.
  Proof. rewrite /success/path_end/=push !fun_if !path_endP; case: get_end => //=; case: path_end => //. Qed.

  Lemma failed_success A: failed A -> success A = false.
  Proof. by rewrite/failed/success => /eqP->. Qed.

  Lemma success_path_atom A: success A -> path_atom A = false.
  Proof. by rewrite/success/path_atom => /eqP->. Qed.

  Lemma path_atom_failed A: path_atom A -> failed A = false.
  Proof. by rewrite/path_atom/failed; case: path_end. Qed. 

  Lemma success_failed A: success A -> failed A = false.
  Proof. by apply: contraTF => /failed_success ->. Qed.

  Lemma success_or_None sm B: success (Or None sm B) = success B.
  Proof. by rewrite/success/path_end/= path_endP. Qed.

  Lemma success_or_Some A sm B: success (Or (Some A) sm B) = success A.
  Proof. by rewrite/success/path_end/= !path_endP. Qed.

  Lemma success_and A sm B: success (And A sm B) = success A && success B.
  Proof. rewrite/success/path_end/= push !fun_if/= !path_endP; case:path_end => //. Qed.

  Lemma failed_or_None sm B: failed (Or None sm B) = failed B.
  Proof. by rewrite/failed/path_end/= !path_endP. Qed.

  Lemma failed_or_Some A sm B: failed (Or (Some A) sm B) = failed A.
  Proof. by rewrite/failed/path_end/= !path_endP. Qed.

  Lemma failed_and A sm B: failed (And A sm B) = failed A || (success A && failed B).
  Proof. rewrite/failed/success/path_end/= !push fun_if/= !path_endP; case p: path_end => //=. Qed.

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

Definition step_res := (step_tag * tree)%type.

Fixpoint big_andA x xs : tree :=
  match xs with
  | [::] => TA x
  | y :: ys => And (TA x) xs (big_andA y ys)
  end.

Definition big_and (a : list A) : tree :=
  match a with
  | [::] => OK
  | x :: xs => big_andA  x xs
  end.

Fixpoint big_or (r : list A) (l : seq (Sigma * seq A)) : tree :=
  match l with 
  | [::] => big_and r
  | (s,r1) :: xs => Or (Some (big_and r)) s (big_or r1 xs)
  end.

Section main.
  Variable u: Unif.

  (*SNIP: step_sig*)
  Definition step : program -> fvS -> Sigma -> tree -> (fvS * step_tag * tree) := 
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
          let: (fv, tB, rB) := (step fv (get_subst s A) B) in
          (fv, tB, And (if is_cb tB then cutl A else A) B0 rB)
        else let: (fv, tA, rA) := step fv s A in (fv, tA, And rA B0 B)
    end.

    Lemma step_and A B0 B pr fv s: (step pr fv s (And A B0 B)).2 = 
        if success A then 
          And (if is_cb (step pr fv (get_subst s A) B).1.2 then cutl A else A) B0 (step pr fv (get_subst s A) B).2
        else And (step pr fv s A).2 B0 B.
    Proof. by rewrite/=!push; case: ifP => //=. Qed.

  (* Next_alt takes a tree "T" returns a new tree "T'" representing the next
     alternative wrt "T", if no new alternative exists, None is returned.
     Next_alt takes a boolean b to know if a successful path should be erased in
     "T".
  *)
  (*SNIP: next_alt_code *)
  (*SNIP: next_alt*)
  Definition next_alt : bool -> tree -> option tree :=
  (*ENDSNIP: next_alt*)
    fix next_alt b A :=
    match A with
    | KO => None
    | OK => if b then None else Some OK
    | TA _ => Some A
    | And A B0 B =>
      let build_B0 A := And A B0 (big_and B0) in
      if success A then
        match next_alt b B with
        | None => omap build_B0 (next_alt true A)
        | Some B' => Some (And A B0 B')
        end
      else if failed A then omap build_B0 (next_alt false A) 
      else Some (And A B0 B)
    | Or None sB B => omap (fun x => Or None sB x) (next_alt b B)
    | Or (Some A) sB B =>
        match next_alt b A with
        | None => omap (fun x => Or None sB x) (next_alt false B)
        | Some A' => Some (Or (Some A') sB B)
       end
  end.
  (*ENDSNIP: next_alt_code *)

  Goal forall r, next_alt false (And (Or (Some OK) empty OK) r KO) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt false (And (Or (Some OK) empty OK) r KO) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt true (And (Or (Some OK) empty OK) r OK) = Some (And (Or None empty OK) r (big_and r)).
  Proof. move=> []//=. Qed.

  Goal (next_alt false (Or (Some KO) empty OK)) = Some (Or None empty OK). move=> //=. Qed.

  Inductive run (p : program): fvS -> Sigma -> tree -> 
                    option Sigma -> option tree -> bool -> fvS -> Prop :=
    | run_done s1 s2 A B fv       : success A -> get_subst s1 A = s2 -> (next_alt true A) = B -> run fv s1 A (Some s2) B false fv
    | run_step  s1 s2 r A B b1 b2 fv0 fv1 fv2 st: path_atom A -> step p fv0 s1 A = (fv1, st, B) -> b2 = (st == CutBrothers) || b1 -> run fv1 s1 B s2 r b1 fv2 -> run fv0 s1 A s2 r b2 fv2
    | run_fail s1 s2 A B r n fv0 fv1    : 
          failed A -> next_alt false A = Some B ->
              run fv0 s1 B s2 r n fv1 -> run fv0 s1 A s2 r n fv1
    | run_dead s1 A fv : 
          next_alt false A = None ->
            run fv s1 A None None false fv.

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
  [move=> s1 s2 A B fv SA sA sB |
    move=>s1 s2 r A B b1 b2 fv0 fv1 fv2 st pA eA ? rB IH|
    move=>s1 s2 A B r n fv0 fv1 fA nA rB IH |move=> s1 A fv nA ]; intros X; subst => //; auto.
Tactic Notation "elim_run" hyp(T) hyp_list(X) := elim_run T X.

(*END*)

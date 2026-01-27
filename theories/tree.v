From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export finmap lang.

(*BEGIN*)
(*SNIP: tree_def*)
Inductive tree :=
  | KO | OK
  | TA : A -> tree
  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
  | Or  : tree -> Sigma -> tree -> tree 
  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
  | And : tree -> seq A -> tree -> tree.
(*ENDSNIP: tree_def*)
  (* | PiImpl : V -> R_ A -> A -> A. *)

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

    (* Note: "is_dead A || (success A && dead B)" is wrong
      A counter example is: "(OK \/ p) /\ Dead"
      In this case, a valid alternative is "p /\ B0"
    *)
  (*SNIP: is_dead*)
  (* Fixpoint is_dead A :=
    match A with
    | Dead => true
    | OK | KO | TA _ => false
    | And A B0 B => is_dead A
    | Or A s B => is_dead A && is_dead B
    end. *)
  (*ENDSNIP: is_dead*)

  (*SNIP: path_end*)
  Fixpoint path_end A :=
    match A with
    | OK | KO | TA _ => A
    | Or A _ _ => path_end A
    | And A B0 B => 
      match path_end A with
      | OK => path_end B
      | A => A
      end
    end.
  (*ENDSNIP: path_end*)

  Fixpoint is_ko A :=
    match A with
    | KO => true
    | OK | TA _ => false
    | And A B0 B => is_ko A
    | Or A s B => is_ko A && is_ko B
    end.

  Fixpoint success (A : tree) : bool :=
    match A with
    | OK => true
    | TA _ | KO => false
    | And A _ B => success A && success B
    (* We need to keep the if condition to reflect the behavior of step:
      For example, an interesting proprety of step is:
      - success A -> step A = Success B
      - if we replace following branch with:
          "success A || success B" (i.e. we remove the if), then
          KO \/ OK is success but step (KO \/ OK) is not Success but
          rather Expanded
    *)
    | Or A _ B => success A
    end.

  Fixpoint failed (A : tree) : bool :=
    match A with
    (* KO is considered as a failure, so that next_alt can put it
        into Dead. This is because, we want step to transform a KO
        tree into a "Failed KO" (it does not introduce a Dead tree).
    *)
    | KO => true
    | TA _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    (* We keep the if condition to have the right behavior in next_alt *)
    | Or A _ B => failed A
    end.

  (*SNIP: succ_path*)
  Definition successT A := path_end A == OK.
  (*ENDSNIP: succ_path*)

  (*SNIP: failed_path*)
  Definition failedT A := (path_end A == KO).
  (*ENDSNIP: failed_path*)

  Lemma successP A : success A = successT A.
  Proof.
    rewrite/successT; elim: A => //=.
    move=> A HA B0 B HB; rewrite HA HB.
    case: path_end => //.
  Qed.

  Lemma failedP A : failed A = failedT A.
  Proof.
    rewrite/failedT; elim: A => //=.
    move=> A HA B0 B HB; rewrite HA HB.
    rewrite successP /successT.
    case pA: path_end => //=.
  Qed.

  Fixpoint cutr A :=
    match A with
    | TA _| KO => KO
    | OK => KO
    | And A B0 B => And (cutr A) B0 B
    | Or A s B => Or (cutr A) s (cutr B)
    end.

  (* This cuts away everything except for the only path with success *)
  Fixpoint cutl A :=
    match A with
    | TA _ | KO => KO
    | OK => A
    | And A B0 B =>
      if success A then And (cutl A) B0 (cutl B)
      else And (cutr A) B0 (cutr B)
    | Or A s B => 
        (* if A is dead then the success is to be found in B *)
        (* otherwise we cutl A and completely kill B with cutr *)
        Or (cutl A) s (cutr B)
    end.

  (********************************************************************)
  (* STATE OP PROPERTIES                                              *)
  (********************************************************************)
  
  (* IS_DEAD + IS_KO + FAILED + SUCCESS *)
  (* Lemma is_dead_is_ko {A}: is_dead A -> is_ko A.
  Proof. elim: A => // A HA s B HB/=/andP[/HA->/HB]//. Qed. *)

  Lemma is_ko_failed {A}: is_ko A -> failed A.
  Proof.
    elim: A => //.
    - by move=> A HA s B HB/=/andP[/HA->].
    - move=> A HA B0 B HB/=/HA->//.
  Qed.

  Lemma failed_is_ko {A}: failed A = false -> is_ko A = false.
  Proof. by case X: is_ko => //; rewrite is_ko_failed//. Qed.

  Lemma failed_success A: failed A -> success A = false.
  Proof.
    elim: A => //.
    + move=> A HA B0 B HB /= /orP [/HA->|/andP[->/HB->]]//.
  Qed.

  Lemma is_ko_success {A}: is_ko A -> success A = false.
  Proof. move=>/is_ko_failed/failed_success//. Qed.

  (* Lemma is_dead_failed {A} : is_dead A -> failed A.
  Proof. move=>/is_dead_is_ko/is_ko_failed//. Qed. *)

  (* Lemma is_dead_success {A}: is_dead A -> success A = false.
  Proof. move=>/is_dead_is_ko/is_ko_success//. Qed. *)

  (* Lemma failed_dead {A} : failed A = false -> is_dead A = false.
  Proof. apply: contraFF is_dead_failed. Qed. *)

  Lemma success_failed A: success A -> failed A = false.
  Proof.
    move=>H; apply: contraFF _ erefl.
    move=>/failed_success; rewrite H//.
  Qed.

  Lemma success_is_ko {A}: success A -> is_ko A = false.
  Proof.
    move=>H; apply: contraFF _ erefl.
    move=>/is_ko_success; rewrite H//.
  Qed.

  (* Lemma success_is_dead {A}: success A -> is_dead A = false.
  Proof. 
    move=>H; apply: contraFF _ erefl.
    move=>/is_dead_success; rewrite H//.
  Qed. *)

  Lemma cutr2 {a}: cutr (cutr a) = cutr a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 B HB]; rewrite HA//HB//. Qed.
  
  Lemma is_ko_cutr {B}: is_ko (cutr B).
  Proof. elim: B => // A HA s B HB/=; rewrite HA HB//. Qed.

  (* Lemma is_dead_cutr {A}: is_dead (cutr A) = is_dead A.
  Proof. elim: A => //A HA s B HB/=; rewrite HA HB//. Qed. *)

  (* Lemma is_dead_cutl {A}: is_dead (cutl A) = is_dead A.
  Proof. 
    elim: A => //=.
    - move=> A HA s B HB; rewrite fun_if/= HA HB is_dead_cutr if_same//.
    - move=> A HA B0 B HB; rewrite fun_if/= HA is_dead_cutr// if_same//.
  Qed. *)

  Lemma failed_cutr {A}: failed (cutr A).
  Proof. elim: A => //=A->// _ B ->; rewrite if_same//. Qed.

  Lemma success_cutr {A} : success (cutr A) = false.
  Proof. apply: failed_success failed_cutr. Qed.

  (* Lemma dead_cutl A: A <> Dead -> cutl A == Dead = false.
  Proof. case: A => //=>; case: ifP => //. Qed. *)

  Lemma success_cut {A} : success (cutl A) = success A.
  Proof.
    elim: A => //. 
    (* + move=> A HA s B HB /=.
      case: eqP => ?; subst => //=; rewrite HA dead_cutl//. *)
    + move=> A HA B C HC /=.
      rewrite fun_if/= HA HC !success_cutr/=.
      case: ifP => //=->//.
  Qed.

  Lemma is_ko_cutl {B}: is_ko B -> is_ko (cutl B).
  Proof. 
    elim: B => //. 
    - by move=> //=A HA s B HB/andP[kA kB]; rewrite is_ko_cutr HA.
    - move=> A HA B0 B HB/= kA; rewrite fun_if/=; rewrite HA//is_ko_cutr if_same//.
  Qed.

  Lemma failed_success_cut {A}: failed (cutl A) = ~~ (success (cutl A)).
  Proof.
    elim: A => //=.
    - move=> A HA B0 B HB/=. 
      rewrite fun_if/= (fun_if success) /=!failed_cutr success_cutr success_cut/=.
      rewrite HA HB !success_cut; case: ifP => //->//.
  Qed.

  Lemma success_failed_cut {A}: success (cutl A) = ~~ (failed (cutl A)).
  Proof. rewrite failed_success_cut; case: success => //. Qed.


  Lemma failed_cut {A}: failed A -> failed (cutl A).
  Proof.
    elim: A => //.
    move=> A HA B0 B HB /=; rewrite fun_if/=.
    move=>/orP[fA|/andP[sA fB]].
      rewrite failed_success//= failed_cutr//.
    rewrite sA success_cut sA HB// orbT//.
  Qed.
End tree_op.

Definition step_res := (step_tag * tree)%type.

Fixpoint big_and (a : list A) : tree :=
  match a with
  | [::] => OK
  | x :: xs => And (TA x) xs (big_and xs)
  end.

Fixpoint big_or (r : list A) (l : seq (Sigma * R)) : tree :=
  match l with 
  | [::] => big_and r
  | (s,r1) :: xs => Or (big_and r) s (big_or r1.(premises) xs)
  end.

Section main.
  Variable u: Unif.

  Definition backchain pr fv s t :=
    let: (fv, l) := bc u pr fv t s in
    (fv, if l is (s,r) :: xs then (Or KO s (big_or r.(premises) xs))
         else KO).

  (* Lemma dead_big_or p fv s t: (backchain p fv s t).2 == Dead = false.
  Proof.
    by rewrite /backchain; case F: bc => [fv' [//|[s1 r] xs]].
  Qed. *)

  Fixpoint get_substS (s: Sigma) A :=
    match A with
    | TA _ | KO | OK => s
    | Or A _ _ => get_substS s A
    | And A _ B => if success A then get_substS (get_substS s A) B else (get_substS s A)
    end.

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
       let: (fv, t) := backchain pr fv s t in
       (fv, Expanded, t)

    (* recursive cases *)
    | Or A sB B =>
        let: (fv, tA, rA) := step fv s A in
        (fv, if is_cb tA then Expanded else tA, Or rA sB (if is_cb tA then cutr B else B))
    | And A B0 B =>
        let: (fv, tA, rA) := step fv s A in
        if is_sc tA then 
          let: (fv, tB, rB) := (step fv (get_substS s rA) B) in
          (fv, tB, And (if is_cb tB then cutl A else A) B0 rB)
        else (fv, tA, And rA B0 B)
    end.

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
      let build_B0 A := Some (And A B0 (big_and B0)) in
      let reset := obind build_B0 (next_alt (success A) A) in
      if success A then
        match next_alt b B with
        | None => reset
        | Some B => Some (And A B0 B)
        end
      else if failed A then reset 
      else Some (And A B0 B)
    | Or A sB B =>
      match next_alt b A with
        | None => next_alt false B
        | Some nA => Some (Or nA sB B)
      end
  end.
  (*ENDSNIP: next_alt_code *)

  Goal forall r, next_alt false (And (Or OK empty OK) r KO) = Some (And (Or KO empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt false (And (Or OK empty OK) r KO) = Some (And (Or Dead empty OK) r (big_and r)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt true (And (Or OK empty OK) r OK) = Some (And (Or Dead empty OK) r (big_and r)).
  Proof. move=> []//=. Qed.

  Goal (next_alt false (Or KO empty OK)) = Some (Or Dead empty OK). move=> //=. Qed.

  (* build next_alt tree *)
  (* Definition build_na A oA := odflt (dead A) oA. *)
  Definition build_s (s:Sigma) (oA: option tree) := Option.map (fun _ => s)  oA.

  (*SNIP: run_sig*)
  Inductive run (p : program): fvS -> Sigma -> tree -> 
                    option Sigma -> option tree -> bool -> Prop :=
  (*ENDSNIP: run_sig*)
    | run_done s1 s2 A B fv       : success A -> get_substS s1 A = s2 -> (next_alt true A) = B -> run fv s1 A (Some s2) B false
    | run_cut  s1 s2 r A B n fv fv' : step p fv s1 A = (fv', CutBrothers, B) -> run fv' s1 B s2 r n -> run fv s1 A s2 r true
    | run_step s1 s2 r A B n fv fv'   : step p fv s1 A = (fv', Expanded,    B) -> run fv' s1 B s2 r n -> run fv s1 A s2 r n
    | run_fail s1 s2 A B r n fv    : 
          failed A -> next_alt false A = Some B ->
              run fv s1 B s2 r n -> run fv s1 A s2 r n
    | run_dead s1 A fv : 
          failed A -> next_alt false A = None ->
            run fv s1 A None None false.

  Fixpoint vars_tree t : fvS :=
  match t with
  | TA cut | Dead | KO | OK => fset0
  | TA (call t) => vars_tm (Callable2Tm t)
  | And A B0 B => vars_tree A `|` vars_tree B `|` vars_atoms B0
  | Or A s B => vars_tree A `|` vars_tree B `|` vars_sigma s
  end.

End main.

(* Hint Resolve is_dead_dead : core. *)
(*END*)
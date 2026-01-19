From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export lang.


Inductive tree :=
  | Bot
  | OK
  | Dead
  | TA : program  -> A -> tree
  | Or  : tree -> Sigma -> tree -> tree  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
  | And : tree -> (program * seq A) -> tree -> tree  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
  (* | PiImpl : V -> R_ A -> A -> A. *)
  .
derive tree.
HB.instance Definition _ := hasDecEq.Build tree tree_eqb_OK.

Inductive step_tag := Expanded | CutBrothers| Failure | Success.
derive step_tag.
HB.instance Definition _ := hasDecEq.Build step_tag step_tag_eqb_OK.

Definition is_fl := eq_op Failure.
Definition is_cb := eq_op CutBrothers.
Definition is_sc := eq_op Success.

Section tree_op.

  (********************************************************************)
  (* STATE OP DEFINITIONS                                             *)
  (********************************************************************)

  Fixpoint dead A :=
    match A with
    | Dead => Dead
    | OK | Bot | TA _ _ => Dead
    | And A B0 B => And (dead A) B0 B
    | Or A s B => Or (dead A) s (dead B)
    end.

  Fixpoint is_dead A :=
    match A with
    | Dead => true
    | OK | Bot | TA _ _ => false
    (* Note: "is_dead A || (success A && dead B)" is wrong
      A counter example is: "(OK \/ p) /\ Dead"
      In this case, a valid alternative is "p /\ B0"
    *)
    | And A B0 B => is_dead A
    | Or A s B => is_dead A && is_dead B
    end.

  Fixpoint is_ko A :=
    match A with
    | Dead | Bot => true
    | OK | TA _ _ => false
    | And A B0 B => is_ko A
    | Or A s B => is_ko A && is_ko B
    end.

  Fixpoint success (A : tree) : bool :=
    match A with
    | OK => true
    | TA _ _ | Bot | Dead => false
    | And A _ B => success A && success B
    (* We need to keep the if condition to reflect the behavior of step:
      For example, an interesting proprety of step is:
      - success A -> step A = Success B
      - if we replace following branch with:
          "success A || success B" (i.e. we remove the if), then
          Bot \/ OK is success but step (Bot \/ OK) is not Success but
          rather Expanded
    *)
    | Or A _ B => if is_dead A  then success B else success A
    end.

  Fixpoint failed (A : tree) : bool :=
    match A with
    (* Bot is considered as a failure, so that next_alt can put it
        into Dead. This is because, we want step to transform a Bot
        tree into a "Failure Bot" (it does not introduce a Dead tree).
    *)
    | Bot | Dead => true
    | TA _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    (* We keep the if condition to have the right behavior in next_alt *)
    | Or A _ B => if is_dead A then failed B else failed A
    end.


  Fixpoint cutr A :=
    match A with
    | TA _ _| Bot => Bot
    | OK => Bot
    | Dead => Dead
    | And A B0 B => And (cutr A) B0 B
    | Or A s B => Or (cutr A) s (cutr B)
    end.

  (* This cuts away everything except for the only path with success *)
  Fixpoint cutl A :=
    match A with
    | TA _ _ | Bot => Bot
    | Dead | OK => A
    | And A B0 B =>
      if success A then And (cutl A) B0 (cutl B)
      else And (cutr A) B0 (cutr B)
    | Or A s B => 
        (* if A is dead then the success is to be found in B *)
        if is_dead A then Or A s (cutl B)
        (* otherwise we cutl A and completely kill B with cutr *)
        else  Or (cutl A) s (cutr B)
    end.

  (********************************************************************)
  (* STATE OP PROPERTIES                                              *)
  (********************************************************************)
  
  (* IS_DEAD + IS_KO + FAILED + SUCCESS *)
  Lemma is_dead_is_ko {A}: is_dead A -> is_ko A.
  Proof. elim: A => // A HA s B HB/=/andP[/HA->/HB]//. Qed.

  Lemma is_ko_failed {A}: is_ko A -> failed A.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=/andP[/HA->/HB->]; rewrite if_same//.
    - move=> A HA B0 B HB/=/HA->//.
  Qed.

  Lemma failed_is_ko {A}: failed A = false -> is_ko A = false.
  Proof. by case X: is_ko => //; rewrite is_ko_failed//. Qed.

  Lemma failed_success A: failed A -> success A = false.
  Proof.
    elim: A => //.
    + move=> A HA s B HB /=; case: ifP => //.
    + move=> A HA B0 B HB /= /orP [/HA->|/andP[->/HB->]]//.
  Qed.

  Lemma is_ko_success {A}: is_ko A -> success A = false.
  Proof. move=>/is_ko_failed/failed_success//. Qed.

  Lemma is_dead_failed {A} : is_dead A -> failed A.
  Proof. move=>/is_dead_is_ko/is_ko_failed//. Qed.

  Lemma is_dead_success {A}: is_dead A -> success A = false.
  Proof. move=>/is_dead_is_ko/is_ko_success//. Qed.

  Lemma failed_dead {A} : failed A = false -> is_dead A = false.
  Proof. apply: contraFF is_dead_failed. Qed.

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

  Lemma success_is_dead {A}: success A -> is_dead A = false.
  Proof. 
    move=>H; apply: contraFF _ erefl.
    move=>/is_dead_success; rewrite H//.
  Qed.

  (* cutl + cutr + dead *)
  Lemma dead2 {A}: dead (dead A) = dead A.
  Proof. elim: A => //=[A HA s B HB|A HA B0 B HB]; rewrite HA//HB//. Qed.

  Lemma cutr2 {a}: cutr (cutr a) = cutr a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 B HB]; rewrite HA//HB//. Qed.
  
  Lemma cutr_dead {a}: cutr (dead a) = dead a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 B HB]; rewrite HA//HB//. Qed.

  Lemma dead_cutr {a}: dead (cutr a) = dead a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 B HB]; rewrite HA// HB//. Qed.

  (* IS_DEAD + IS_KO + FAILED + SUCCESS with cutr, cutl, dead *)
  Lemma is_dead_dead {A}: is_dead (dead A).
  Proof. elim: A => // A HA s B HB/=; rewrite HA//. Qed.

  Lemma is_ko_cutr {B}: is_ko (cutr B).
  Proof. elim: B => // A HA s B HB/=; rewrite HA HB//. Qed.

  Lemma is_dead_cutr {A}: is_dead (cutr A) = is_dead A.
  Proof. elim: A => //A HA s B HB/=; rewrite HA HB//. Qed.

  Lemma is_dead_cutl {A}: is_dead (cutl A) = is_dead A.
  Proof. 
    elim: A => //=.
    - move=> A HA s B HB; rewrite fun_if/= HA HB is_dead_cutr if_same//.
    - move=> A HA B0 B HB; rewrite fun_if/= HA is_dead_cutr// if_same//.
  Qed.

  Lemma failed_cutr {A}: failed (cutr A).
  Proof. elim: A => //=A->// _ B ->; rewrite if_same//. Qed.

  Lemma success_cutr {A} : success (cutr A) = false.
  Proof. apply: failed_success failed_cutr. Qed.

  Lemma success_cut {A} : success (cutl A) = success A.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      case: ifP => /= dA; rewrite ?is_dead_cutl dA//.
    + move=> A HA B C HC /=.
      rewrite fun_if/= HA HC !success_cutr/=.
      case: ifP => //=->//.
  Qed.

  Lemma is_ko_cutl {B}: is_ko B -> is_ko (cutl B).
  Proof. 
    elim: B => //. 
    - move=> //=A HA s B HB/andP[kA kB].
      by rewrite fun_if/=kA HA//HB///= is_ko_cutr if_same.
    - move=> A HA B0 B HB/= kA; rewrite fun_if/=; rewrite HA//is_ko_cutr if_same//.
  Qed.

  Lemma failed_success_cut {A}: failed (cutl A) = ~~ (success (cutl A)).
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA/=; rewrite?is_dead_cutl dA//.
    - move=> A HA B0 B HB/=. 
      rewrite fun_if/= (fun_if success) /=!failed_cutr success_cutr success_cut/=.
      rewrite HA HB !success_cut; case: ifP => //->//.
  Qed.

  Lemma success_failed_cut {A}: success (cutl A) = ~~ (failed (cutl A)).
  Proof. rewrite failed_success_cut; case: success => //. Qed.


  Lemma failed_cut {A}: failed A -> failed (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB /=.
      rewrite (fun_if failed)/= !failed_cutr.
      by case: ifP => ///eqP dA /HA->; rewrite if_same.
    move=> A HA B0 B HB /=; rewrite fun_if/=.
    move=>/orP[fA|/andP[sA fB]].
      rewrite failed_success//= failed_cutr//.
    rewrite sA success_cut sA HB// orbT//.
  Qed.

  Lemma failed_cutl_is_ko {A}:
    failed (cutl A) -> is_ko (cutl A).
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA/=; rewrite?is_dead_cutl dA/=.
        rewrite is_dead_is_ko//.
      move=> /HA ->; rewrite is_ko_cutr//.
    - move=> A HA B0 B HB; case:ifP => sA/=.
        rewrite success_cut sA failed_success_cut success_cut sA/=.
        move=> /HB.
      (* THIS IS WRONG *)
  Abort.

End tree_op.

Definition step_res := (step_tag * tree)%type.

(*Lemma get_tree_And A B0 B : get_tree (mkAnd A B0 B) = And (if is_cb B then cutl A else A) B0 (get_tree B).
Proof. by case: B. Qed.

Lemma get_tree_Or A s B : get_tree (mkOr A s B) = Or A s (get_tree B).
Proof. by case: B. Qed. *)

Fixpoint big_and pr (a : list A) : tree :=
  match a with
  | [::] => OK
  | x :: xs => And (TA pr x) (pr, xs) (big_and pr xs)
  end.

Fixpoint big_or_aux pr (r : list A) (l : seq (Sigma * R)) : tree :=
  match l with 
  | [::] => big_and pr r
  | (s,r1) :: xs => Or (big_and pr r) s (big_or_aux pr r1.(premises) xs)
  end.

Lemma big_and_dead {p l}: is_dead (big_and p l) = false.
Proof. elim l => //-[]//. Qed.


Section main.
  Variable u: Unif.

  Definition big_or pr s t :=
    let l := F u pr t s in
    if l is (s,r) :: xs then (Or Bot s (big_or_aux pr r.(premises) xs))
    else Bot.

  Lemma dead_big_or p s t: is_dead (big_or p s t) = false.
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
  Qed.

  Fixpoint get_substS s A :=
    match A with
    | TA _ _ | Bot | OK | Dead => s
    | Or A s1 B => if is_dead A then get_substS s1 B else get_substS s A
    | And A _ B => if success A then get_substS (get_substS s A) B else (get_substS s A)
    end.

  Fixpoint step s A : (step_tag * tree) :=
    match A with
    (* meta *)
    | OK             => (Success, OK)
    | Bot | Dead     => (Failure, A)
    
    (* lang *)
    | TA _ cut       => (CutBrothers, OK)
    | TA pr (call t) => (Expanded, (big_or pr s t))

    (* recursive cases *)
    | Or A sB B =>
        if is_dead A then 
          let rB := (step sB B) in
          (if is_cb rB.1 then Expanded else rB.1, Or A sB rB.2)
        else
        let rA := step s A in
        (if is_cb rA.1 then Expanded else rA.1, Or rA.2 sB (if is_cb rA.1 then cutr B else B))
    | And A B0 B =>
        let rA := step s A in
        if is_sc rA.1 then 
          let rB := (step (get_substS s rA.2) B) in
          (rB.1, And (if is_cb rB.1 then cutl A else A) B0 rB.2)
        else (rA.1, And rA.2 B0 B)
    end.

  (* Next_alt takes a tree "T" returns a new tree "T'" representing the next
     alternative wrt "T", if no new alternative exists, None is returned.
     Next_alt takes a boolean b to know if a successful path should be erased in
     "T".
  *)
  Fixpoint next_alt b (A : tree) : option (tree) :=
    match A with
    | Bot | Dead => None
    | OK => if b then None else Some OK
    | TA _ _ => Some A
    | And A (pr, B0) B =>
      let build_B0 A := Some (And A (pr, B0) (big_and pr B0)) in
      let reset := obind build_B0 (next_alt (success A) A) in
      if success A then
        match next_alt b B with
        | None => reset
        | Some B => Some (And A (pr, B0) B)
        end
      else if failed A then reset 
      else Some (And A (pr, B0) B)
    | Or A sB B =>
      if is_dead A then omap (fun x => (Or A sB x)) (next_alt b B)
      else match next_alt b A with
        | None => obind (fun x => Some (Or (dead A) sB x)) (next_alt false B)
        | Some nA => Some (Or nA sB B)
      end
  end.

  Goal forall r, next_alt false (And (Or OK empty OK) r Bot) = Some (And (Or Dead empty OK) r (big_and r.1 r.2)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt false (And (Or OK empty OK) r Bot) = Some (And (Or Dead empty OK) r (big_and r.1 r.2)).
  Proof. move=> [] //=. Qed.

  Goal forall r, next_alt true (And (Or OK empty OK) r OK) = Some (And (Or Dead empty OK) r (big_and r.1 r.2)).
  Proof. move=> []//=. Qed.

  Goal (next_alt false (Or Bot empty OK)) = Some (Or Dead empty OK). move=> //=. Qed.

  (* build next_alt tree *)
  Definition build_na A oA := odflt (dead A) oA.
  Definition build_s (s:Sigma) (oA: option tree) := Option.map (fun _ => s)  oA.


  Inductive runb : Sigma -> tree -> option Sigma -> tree -> bool -> Type :=
    | run_done {s1 s2 A B}        : success A -> get_substS s1 A = s2 -> build_na A (next_alt true A) = B -> runb s1 A (Some s2) B false
    | run_cut  {s1 s2 r A B n}    : step s1 A = (CutBrothers, B) -> runb s1 B s2 r n -> runb s1 A s2 r true
    | run_step {s1 s2 r A B n}    : step s1 A = (Expanded,    B) -> runb s1 B s2 r n -> runb s1 A s2 r n
    | run_fail   {s1 s2 A B r n}     : 
          failed A -> next_alt false A = Some B ->
              runb s1 B s2 r n -> runb s1 A s2 r n
    | run_dead {s1 A} : 
          failed A -> next_alt false A = None ->
              runb s1 A None (dead A) false.

  Definition dead_run s1 A : Type := forall B n, runb s1 A None B n.
End main.

Hint Resolve is_dead_dead : core.

From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export lang.


Elpi derive.eqbOK.register_axiom program is_program is_program_inhab program_eqb program_eqb_correct program_eqb_refl.
Lemma program_eqb_OK : Equality.axiom program_eqb.
apply: iffP2 program_eqb_correct program_eqb_refl.
Qed.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Elpi derive.eqbOK.register_axiom Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
Lemma Sigma_eqb_OK : Equality.axiom Sigma_eqb.
apply: iffP2 Sigma_eqb_correct Sigma_eqb_refl.
Qed.
HB.instance Definition _ : hasDecEq Sigma := hasDecEq.Build Sigma Sigma_eqb_OK.

Inductive tree :=
  | Bot : tree
  | OK : tree
  | Dead : tree
  | CallS : program  -> Callable -> tree
  | CutS : tree
  | Or  : tree -> Sigma -> tree -> tree  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
  | And : tree -> tree -> tree -> tree  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
  .
derive tree.
HB.instance Definition _ := hasDecEq.Build tree tree_eqb_OK.

Inductive expand_res :=
  | Expanded    of tree
  | CutBrothers of tree
  | Failure     of tree
  | Success      of tree.
derive expand_res.
HB.instance Definition _ := hasDecEq.Build expand_res expand_res_eqb_OK.

Definition get_tree r := match r with | Failure A | Success A | CutBrothers A | Expanded A => A end.
Definition is_expanded X := match X with Expanded _ => true | _ => false end.
Definition is_fail A := match A with Failure _ => true | _ => false end.
Definition is_cutbrothers X := match X with CutBrothers _ => true | _ => false end.
Definition is_solved X := match X with Success _ => true | _ => false end.

Section tree_op.

  (********************************************************************)
  (* STATE OP DEFINITIONS                                             *)
  (********************************************************************)

  Fixpoint dead A :=
    match A with
    | Dead => Dead
    | OK | Bot | CutS | CallS _ _ => Dead
    | And A B0 B => And (dead A) (dead B0) (dead B)
    | Or A s B => Or (dead A) s (dead B)
    end.

  Fixpoint is_dead A :=
    match A with
    | Dead => true
    | OK | Bot | CutS | CallS  _ _ => false
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
    | OK | CutS | CallS  _ _ => false
    | And A B0 B => is_ko A
    | Or A s B => is_ko A && is_ko B
    end.

  Fixpoint success (A : tree) : bool :=
    match A with
    | OK => true
    | CutS | CallS _ _ | Bot | Dead => false
    | And A _ B => success A && success B
    (* We need to keep the if condition to reflect the behavior of expand:
      For example, an interesting proprety of expand is:
      - success A -> expand A = Success B
      - if we replace following branch with:
          "success A || success B" (i.e. we remove the if), then
          Bot \/ OK is success but expand (Bot \/ OK) is not Success but
          rather Expanded
    *)
    | Or A _ B => if is_dead A  then success B else success A
    end.

  Fixpoint failed (A : tree) : bool :=
    match A with
    (* Bot is considered as a failure, so that next_alt can put it
        into Dead. This is because, we want expand to transform a Bot
        tree into a "Failure Bot" (it does not introduce a Dead tree).
    *)
    | Bot | Dead => true
    | CutS | CallS _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    (* We keep the if condition to have the right behavior in next_alt *)
    | Or A _ B => if is_dead A then failed B else failed A
    end.


  Fixpoint cutr A :=
    match A with
    | CutS | CallS _ _| Bot => Bot
    | OK => Bot
    | Dead => Dead
    | And A B0 B => And (cutr A) (cutr B0) (cutr B)
    | Or A s B => Or (cutr A) s (cutr B)
    end.

  (* This cuts away everything except for the only path with success *)
  Fixpoint cutl A :=
    match A with
    | CutS | CallS _ _ | Bot => Bot
    | Dead | OK => A
    | And A B0 B =>
      if success A then And (cutl A) (cutr B0) (cutl B)
      else And (cutr A) (cutr B0) (cutr B)
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
    - move=> A HA B0 _ B HB/=/HA->//.
  Qed.

  Lemma failed_is_ko {A}: failed A = false -> is_ko A = false.
  Proof. by case X: is_ko => //; rewrite is_ko_failed//. Qed.

  Lemma failed_success A: failed A -> success A = false.
  Proof.
    elim: A => //.
    + move=> A HA s B HB /=; case: ifP => //.
    + move=> A HA B0 _ B HB /= /orP [/HA->|/andP[->/HB->]]//.
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
  Proof. elim: A => //=[A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.

  Lemma cutr2 {a}: cutr (cutr a) = cutr a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.
  
  Lemma cutr_dead {a}: cutr (dead a) = dead a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.

  Lemma dead_cutr {a}: dead (cutr a) = dead a.
  Proof. elim: a => //= [A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.

  Lemma dead_cutl {a}: dead (cutl a) = dead a.
  Proof. 
    elim: a => //= [A HA s B HB|A HA B0 HB0 B HB].
      by rewrite fun_if/=HA HB dead_cutr if_same.
    rewrite fun_if/= HA HB !dead_cutr if_same//.
  Qed.

  (* IS_DEAD + IS_KO + FAILED + SUCCESS with cutr, cutl, dead *)
  Lemma is_dead_dead {A}: is_dead (dead A).
  Proof. elim: A => // A HA s B HB/=; rewrite HA//. Qed.

  Lemma is_ko_cutr {B}: is_ko (cutr B).
  Proof. elim: B => // A HA s B HB/=; rewrite HA HB//. Qed.

  Lemma cutlr {A}: cutl (cutr A) = cutr A.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      rewrite HA HB cutr2 if_same//.
    - move=> A HA B0 HB0 B HB/=.
      rewrite !cutr2 is_ko_success//is_ko_cutr//.
  Qed.

  Lemma cutrl {A}: cutr (cutl A) = cutr A.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=.
      rewrite fun_if/= HA HB cutr2 if_same//.
    - move=> A HA B0 HB0 B HB/=.
      rewrite fun_if/= HA HB !cutr2 if_same//.
  Qed.

  Lemma is_dead_cutr {A}: is_dead (cutr A) = is_dead A.
  Proof. elim: A => //A HA s B HB/=; rewrite HA HB//. Qed.

  Lemma is_dead_cutl {A}: is_dead (cutl A) = is_dead A.
  Proof. 
    elim: A => //=.
    - move=> A HA s B HB; rewrite fun_if/= HA HB is_dead_cutr if_same//.
    - move=> A HA B0 HB0 B HB; rewrite fun_if/= HA is_dead_cutr// if_same//.
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
    + move=> A HA B HB C HC /=.
      rewrite fun_if/= HA HC !success_cutr/=.
      case: ifP => //=->//.
  Qed.

  Lemma cutl2 {a}: cutl (cutl a) = cutl a.
  Proof.
    elim: a => //=.
    + move=> A HA s B HB.
      rewrite (fun_if cutl)/= HA HB cutrl cutlr cutr2 if_same.
      case: ifP => //->//.
    + move=> A HA B0 HB0 B HB.
      case: ifP => //= sA.
        rewrite success_cut sA HA HB cutr2//.
      rewrite success_cutr !cutr2//.
  Qed.

  Lemma is_ko_cutl {B}: is_ko B -> is_ko (cutl B).
  Proof. 
    elim: B => //. 
    - move=> //=A HA s B HB/andP[kA kB].
      by rewrite fun_if/=kA HA//HB///= is_ko_cutr if_same.
    - move=> A HA B0 _ B HB/= kA; rewrite fun_if/=; rewrite HA//is_ko_cutr if_same//.
  Qed.

  Lemma failed_success_cut {A}: failed (cutl A) = ~~ (success (cutl A)).
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA/=; rewrite?is_dead_cutl dA//.
    - move=> A HA B0 _ B HB/=. 
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
    move=> A HA B0 _ B HB /=; rewrite fun_if/=.
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
    - move=> A HA B0 _ B HB; case:ifP => sA/=.
        rewrite success_cut sA failed_success_cut success_cut sA/=.
        move=> /HB.
      (* THIS IS WRONG *)
  Abort.

End tree_op.

Definition mkOr A sB r :=
  match r with
  | Failure B       => Failure     (Or A sB B)
  | Expanded B    => Expanded  (Or A sB B)
  | CutBrothers B => Expanded  (Or A sB B)
  | Success B      => Success    (Or A sB B)
  end.

Definition mkAnd A B0 r :=
  match r with
  | Failure B       => Failure       (And A B0 B)
  | Expanded B    => Expanded    (And A B0 B)
  | CutBrothers B => CutBrothers (And (cutl A) (cutr B0) B)
  | Success B      => Success      (And A B0 B)
  end.

Lemma get_tree_And A B0 B : get_tree (mkAnd A B0 B) = And (if is_cutbrothers B then cutl A else A) ((if is_cutbrothers B then cutr B0 else B0)) (get_tree B).
Proof. by case: B. Qed.

Lemma get_tree_Or A s B : get_tree (mkOr A s B) = Or A s (get_tree B).
Proof. by case: B. Qed.

Definition A2CallCut pr (A:A) : tree :=
  match A with
  | ACut => CutS
  | ACall tm => CallS pr tm
  end.

Fixpoint big_and pr (a : list A) : tree :=
  match a with
  | [::] => OK
  | x :: xs => And (A2CallCut pr x)  (big_and pr xs) (big_and pr xs)
  end.

Fixpoint big_or_aux pr (r : list A) (l : seq (Sigma * R)) : tree :=
  match l with 
  | [::] => big_and pr r
  | (s,r1) :: xs => Or (big_and pr r) s (big_or_aux pr r1.(premises) xs)
  end.

Lemma big_and_dead {p l}: is_dead (big_and p l) = false.
Proof. elim l => //-[]//. Qed.

Record Unif := {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  


Section main.
  Variable u: Unif.


  Fixpoint H (ml : list mode) (q : RCallable) (h: RCallable) s : option Sigma :=
    match ml,q,h with
    | [::], RCallable_Kp c, RCallable_Kp c1 => if c == c1 then Some s else None
    | [:: i & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(matching) a1 a2) (H ml q h s)
    | [:: o & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(unify) a1 a2) (H ml q h s)
    | _, _, _ => None
    end.

  (* TODO: deref is too easy? Yes if sigma is a mapping from vars to lambdas in a future version *)
  Fixpoint deref (s: Sigma) (tm:Tm) :=
    match tm with
    | Tm_V V => Option.default tm (s.(sigma) V)
    | Tm_Kp _ | Tm_Kd _ => tm
    | Tm_Comb h ag => Tm_Comb (deref s h) ag
    end.

  Fixpoint select (query : RCallable) (modes:list mode) (rules: list R) sigma : seq (Sigma * R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      match H modes query rule.(head) sigma with
      | None => select query modes rules sigma
      | Some sigma' => (sigma', rule) :: select query modes rules sigma
      end
    end.

  Fixpoint tm2RC (t : Tm) : option RCallable :=
    match t with
    | Tm_Kd _ => None
    | Tm_V _ => None
    | Tm_Kp p => Some (RCallable_Kp p)
    | Tm_Comb t1 t2 => omap (fun x => RCallable_Comb x t2) (tm2RC t1)
    end.

  Fixpoint Callable2Tm (c : Callable) : Tm :=
    match c with
    | Callable_Kp p => Tm_Kp p
    | Callable_V v => Tm_V v
    | Callable_Comb h t => Tm_Comb (Callable2Tm h) t
    end.

  Definition F pr (query:Callable) s : seq (Sigma * R) :=
    let rules := pr.(rules) in
    match tm2RC (deref s (Callable2Tm query)) with
    | None => [::] (*this is a call with flex head, in elpi it is an error! *)
    | Some query =>
      let modes := pr.(modes) query in
      let rules := select query modes rules s in
      rules
      end.

  Definition big_or pr s t :=
    let l := F pr t s in
    if l is (s,r) :: xs then (Or Bot s (big_or_aux pr r.(premises) xs))
    else Bot.

  Lemma dead_big_or p s t: is_dead (big_or p s t) = false.
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
  Qed.

  Fixpoint get_substS s A :=
    match A with
    | CutS | CallS _ _ | Bot | OK | Dead => s
    | Or A s1 B => if is_dead A then get_substS s1 B else get_substS s A
    | And A _ B => if success A then get_substS (get_substS s A) B else (get_substS s A)
    end.

  Fixpoint expand s A : expand_res :=
    match A with
    (* meta *)
    | OK => Success OK
    | Bot => Failure Bot
    | Dead => Failure Dead
    
    (* lang *)
    | CutS       => CutBrothers OK
    | CallS pr t => Expanded (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        if is_dead A then mkOr A sB (expand sB B)
        else
        match expand s A with
        | Success A    => Success      (Or A sB B)
        | Expanded A    => Expanded  (Or A sB B)
        | CutBrothers A => Expanded (Or A sB (cutr B))
        | Failure A     => Failure       (Or A sB B)
        end
    | And A B0 B =>
        match expand s A with
        | Success A     => mkAnd    A B0  (expand (get_substS s A) B)
        | Expanded A    => Expanded     (And A B0 B)
        | CutBrothers A => CutBrothers (And A B0 B)
        | Failure A       => Failure        (And A B0 B)
        end
    end.

  (* Next_alt takes a tree "T" returns a new tree "T'" representing the next
     alternative wrt "T", if no new alternative exists, None is returned.
     Next_alt takes a boolean b to know if a successful path should be erased in
     "T".
  *)
  Fixpoint next_alt b (A : tree) : option (tree) :=
    match A with
    | Bot => None
    | Dead => None
    | OK => if b then None else Some OK
    | CutS | CallS _ _ => Some A
    | And A B0 B =>
      if failed A then 
      (* If A is a failing state, then we look for the next alternative in A,
         the boolean is set to false since no success path exists *)
        match next_alt false A with
        | None => None
        | Some (A) =>
          (* since a new alternative in A exists, then we look attach the reset
             point as its continuation, the reset point is cleaned: next_alt false B0
             is used to kill in advance potential dead subtrees in B0. *)
          match next_alt false B0 with
          | None => None (*if B0 as no alternatives then the full tree collapses*)
          | Some B0' => Some (And A B0 B0')
          end
        end
      else
      if success A then
        (* if A is successfull, we need, at first, to seek for alternatives in B
           For example, in (OK \/ (Call f)) /\ (OK \/ (Call g)), we need to
           give priority to the call to g instead of the call to f
        *)
        match next_alt b B with
        | None => 
          (* if B has no alternatives, it means that we need to find a new alternative
             in A removing its successfull path *)
          match next_alt true A with
          | None => None
          | Some A =>
            (* similarly to the branch before, we clean the reset point *)
            match next_alt false B0 with
            | None => None
            | Some B0' => Some (And A B0 B0')
            end
          end
        (* If the alternative in B exists, then we return on the RHS of the And node *)
        | Some (B) => Some (And A B0 B)
        end
      else Some (And A B0 B)
    | Or A sB B =>
       (* we look for alternatives in A, which have higher priority then the one in B *)
        match next_alt b A with
        | None =>
            (* if no alternative exists in A, then we look in B. Moreover, the boolean
               should be carefully be set.
               There are two interesting scenarios:
               1: "next_alt tree (OK \/ (OK \/ Call f))"
                  In the first case we want to erase a success, we go left,
                  we see that the "OK" is not dead, therefore, we kill it.
                  Then we understand that no alternative exists in the LHS of the OR,
                  therefore wee look for the next alternative in "OK \/ Call f"
                  without erasing the success, the boolean we pass is false
               2: "next_alt tree (Dead \/ (OK \/ Call f))"
                  Here we want to erase, again, to erase a success, this success
                  is not on the LHS of the OR node, therefore we erase it on the RHS
               *)
            match next_alt (if is_dead A then b else false) B with
            | None => None
                      (* we want to preserve at most the structure of the tree, if LHS is dead 
                         we keep it as it is, this is helpful for lemmas like "next_alt_not_failed"*)
            | Some B => Some (Or (if is_dead A then A else dead A) sB B)
            end
        | Some (A) => Some (Or A sB B)
        end
  end.

  Goal next_alt false (And (Or OK empty OK) OK Bot) = Some (And (Or Dead empty OK) OK OK).
  Proof. move=> //=. Qed.

  Goal next_alt false (And (Or OK empty OK) OK Bot) = Some (And (Or Dead empty OK) OK OK).
  Proof. move=> //=. Qed.

  Goal next_alt true (And (Or OK empty OK) OK OK) = Some (And (Or Dead empty OK) OK OK).
  Proof. move=> //=. Qed.

  Goal (next_alt false (Or Bot empty OK)) = Some (Or Dead empty OK). move=> //=. Qed.

  (* build next_alt tree *)
  Definition build_na A oA := odflt (dead A) oA.
  Definition build_s (s:Sigma) (oA: option tree) := Option.map (fun _ => s)  oA.


  Inductive runb : Sigma -> tree -> option Sigma -> tree -> nat -> Type :=
    | run_done {s1 s2 A B}         : success A -> get_substS s1 A = s2 -> build_na A (next_alt true A) = B -> runb s1 A (Some s2) B 0
    | run_cut  {s1 s2 r A B n}    : expand s1 A = CutBrothers B -> runb s1 B s2 r n -> runb s1 A s2 r n.+1
    | run_step {s1 s2 r A B n}    : expand s1 A = Expanded    B -> runb s1 B s2 r n -> runb s1 A s2 r n
    | run_fail   {s1 s2 A B r n}     : 
          failed A -> next_alt false A = Some B ->
              runb s1 B s2 r n -> runb s1 A s2 r n
    | run_dead {s1 A} : 
          failed A -> next_alt false A = None ->
              runb s1 A None (dead A) 0.

  Definition dead_run s1 A : Type := forall B n, runb s1 A None B n.
End main.
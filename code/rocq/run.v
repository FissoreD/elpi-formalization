From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Export lang.

Module Run (U : Unif).

  Import U.
  Import Language.

  Fixpoint H (ml : list mode) (q : Tm) (h: Tm) s : option Sigma :=
    match ml,q,h with
    | [::], Code c, Code c1 => if c == c1 then Some s else None
    | [:: i & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (U.matching a1 a2 s) 
    | [:: o & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (U.unify a1 a2 s) 
    | _, _, _ => None
    end.

  Fixpoint select (query : Tm) (modes:list mode) (rules: list R) sigma : seq (Sigma * R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      match H modes query rule.(head) sigma with
      | None => select query modes rules sigma
      | Some sigma' => (sigma', rule) :: select query modes rules sigma
      end
    end.

  Definition F pr query s : seq (Sigma * R) :=
    let rules := pr.(rules) in
    let modes := pr.(modes) query in
    let rules := select query modes rules s in
    rules.

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

  Inductive state :=
    | Bot : state
    | OK : state
    | Top : state
    | Dead : state
    | Goal : program  -> A -> state
    | Or  : state -> Sigma -> state -> state  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
    | And : state -> state -> state -> state  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
    .
  derive state.
  HB.instance Definition _ := hasDecEq.Build state state_eqb_OK.

  Inductive expand_res :=
    | Expanded    of Sigma & state
    | CutBrothers of Sigma & state
    | Failure     of state
    | Success      of Sigma & state.
  derive expand_res.
  HB.instance Definition _ := hasDecEq.Build expand_res expand_res_eqb_OK.

  Definition get_state r := match r with | Failure A | Success _ A | CutBrothers _ A | Expanded _ A => A end.
  Definition is_expanded X := match X with Expanded _ _ => true | _ => false end.
  Definition is_fail A := match A with Failure _ => true | _ => false end.
  Definition is_cutbrothers X := match X with CutBrothers _ _ => true | _ => false end.
  Definition is_solved X := match X with Success _ _ => true | _ => false end.
  Definition is_cut X := match X with Goal _ Cut => true | _ => false end.


  Inductive exp_res := Done of Sigma & state | Failed of state.
  derive exp_res.
  HB.instance Definition _ := hasDecEq.Build exp_res exp_res_eqb_OK.

  Definition get_state_exp r := match r with Done _ s => s | Failed s => s end.
  Definition is_failed A := match A with Failed _ => true | _ => false end.
  Definition is_done A := match A with Done _ _ => true | _ => false end.

  Section state_op.

    (********************************************************************)
    (* STATE OP DEFINITIONS                                             *)
    (********************************************************************)

    Fixpoint dead1 A :=
      match A with
      | Dead => Dead
      | OK | Bot | Goal _ _ | Top => Dead
      | And A B0 B => And (dead1 A) (dead1 B0) (dead1 B)
      | Or A s B => Or (dead1 A) s (dead1 B)
      end.

    Fixpoint is_dead A :=
      match A with
      | Dead => true
      | OK | Bot | Goal _ _ | Top => false
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
      | OK | Goal _ _ | Top => false
      | And A B0 B => is_ko A
      | Or A s B => is_ko A && is_ko B
      end.

    Fixpoint success (A : state) : bool :=
      match A with
      | OK => true
      | Top | Goal _ _ | Bot | Dead => false
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

    Fixpoint failed (A : state) : bool :=
      match A with
      (* Bot is considered as a failure, so that the next_alt can put it
         into Dead. This is because, we want expand to transform a Bot
         state into a "Failure Bot" (it does not introduce a Dead state).
      *)
      | Bot | Dead => true
      | Top | Goal _ _ | OK => false
      | And A _ B => failed A || (success A && failed B)
      (* We keep the if condition to have the right behavior in next_alt *)
      | Or A _ B => if is_dead A then failed B else failed A (*&& failed B*)
      end.


    Fixpoint cutr A :=
      match A with
      | Goal _ _ | Top | Bot => Bot
      | OK => Bot
      | Dead => Dead
      | And A B0 B => And (cutr A) (cutr B0) (cutr B)
      | Or A s B => Or (cutr A) s (cutr B)
      end.

    Fixpoint cutl A :=
      (* if A == dead A then Dead else *)
      match A with
      | Goal _ _ | Top | Bot => Bot
      | Dead | OK => A
      | And A B0 B => And (cutl A) (cutl B0) (cutl B)
      | Or A s B => 
          if is_dead A then Or A s (cutl B)
          else  Or (cutl A) s (cutr B)
      end.

    (********************************************************************)
    (* STATE OP PROPERTIES                                              *)
    (********************************************************************)
    
    (* IS_DEAD + IS_KO + FAILED + SUCCESS *)
    Lemma is_dead_is_ko {A}: is_dead A -> is_ko A.                  (*1*)
    Proof. elim: A => // A HA s B HB/=/andP[/HA->/HB]//. Qed.

    Lemma is_ko_failed {A}: is_ko A -> failed A.                    (*2*)
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=/andP[/HA->/HB->]; rewrite if_same//.
      - move=> A HA B0 _ B HB/=/HA->//.
    Qed.

    Lemma failed_success A: failed A -> success A = false.          (*3*)
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

    (* cutl + cutr + dead1 *)
    Lemma dead2 {A}: dead1 (dead1 A) = dead1 A.
    Proof. elim: A => //=[A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.

    Lemma cutr2 {a}: cutr (cutr a) = cutr a.
    Proof. elim: a => //= [A HA s B HB|A HA B0 HB0 B HB]; rewrite HA HB//HB0//. Qed.

    Lemma cutlr {A}: cutl (cutr A) = cutr A.
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=.
        rewrite HA HB cutr2 if_same//.
      - move=> A HA B0 HB0 B HB/=.
          rewrite HA HB0 HB//.
    Qed.

    Lemma cutrl {A}: cutr (cutl A) = cutr A.
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=.
        rewrite fun_if/= HA HB cutr2 if_same//.
      - move=> A HA B0 HB0 B HB/=.
        rewrite HA HB0 HB//.
    Qed.


    Lemma cutl2 {a}: cutl (cutl a) = cutl a.
    Proof.
      elim: a => //=.
      + move=> A HA s B HB.
        rewrite (fun_if cutl)/= HA HB cutrl cutlr cutr2 if_same.
        case: ifP => //->//.
      + move=> A -> B0 -> B ->//.
    Qed.

    (* Lemma cutr_dead {A}: cutr A = dead1 A -> dead1 A = A.
    Proof.
      elim: A=> //=. [A HA s B HB|A HA B0 HB0 B HB]. []*; rewrite HA// HB//HB0//. Qed. *)

    (* Lemma cutl_dead {A}: cutl A = dead1 A -> A = dead1 A.
    Proof. 
      elim: A=> //.
        move=> A HA s B HB/=.
        case: ifP => dA[].
          move=><-/HB<-//.
        move=> H H1; rewrite -HA//. cutr_dead//.
      move=> A HA B0 HB0 B HB/=[/HA<-]/HB0<-/HB<-//.
    Qed. *)

    (* IS_DEAD + IS_KO + FAILED + SUCCESS with cutr, cutl, dead1 *)
    Lemma is_dead_dead {A}: is_dead (dead1 A).
    Proof. elim: A => // A HA s B HB/=; rewrite HA//. Qed.

    Lemma is_ko_cutr {B}: is_ko (cutr B).
    Proof. elim: B => // A HA s B HB/=; rewrite HA HB//. Qed.

    (* Lemma dead_cutr_is_dead {A}: is_dead (cutr A) = is_dead A.
    Proof. elim: A => //. ; by move=> A HA s B HB /=; rewrite HA HB. Qed.   *)

    Lemma is_ko_cutl {B}: is_ko B -> is_ko (cutl B).
    Proof. elim: B => //=A HA s B HB/andP[kA kB]; rewrite fun_if/=kA HA//HB// is_ko_cutr if_same//. Qed.

    Lemma failed_cutr {A}: failed (cutr A).
    Proof. elim: A => //=A->// _ B ->; rewrite if_same//. Qed.

    Lemma success_cutr {A} : success (cutr A) = false.
    Proof. apply: failed_success failed_cutr. Qed.

    Lemma success_cut {A} : success A -> success (cutl A).
    Proof.
      elim: A => //. 
      + move=> A HA s B HB /=.
        rewrite (fun_if success)/=.
        case: ifP => /= dA//.
        move=> sA.
        rewrite success_is_dead HA//.
      + move=> A HA B HB C HC /=/andP[sA sC].
        rewrite HA// HC//.
    Qed.

    Lemma failed_cut {A}: failed A -> failed (cutl A).
    Proof.
      elim: A => //.
        move=> A HA s B HB /=.
        rewrite (fun_if failed)/= !failed_cutr.
        by case: ifP => ///eqP dA /HA->; rewrite if_same.
      move=> A HA B0 _ B HB /=.
      move=>/orP[].
        by move=>/HA ->.
      move=>/andP[sA fB].
      rewrite success_cut// HB//orbT//.
    Qed.

    Lemma is_dead_cutr {A}: is_dead (cutr A) = is_dead A.
    Proof. elim: A => //A HA s B HB/=; rewrite HA HB//. Qed.

    Lemma is_dead_cutl {A}: is_dead (cutl A) = is_dead A.
    Proof. elim: A => //A HA s B HB/=; rewrite fun_if/=HB HA is_dead_cutr if_same//. Qed.
    
  End state_op.

  Definition mkOr A sB r :=
    match r with
    | Failure B       => Failure     (Or A sB B)
    | Expanded s B    => Expanded s  (Or A sB B)
    | CutBrothers s B => Expanded s  (Or A sB B)
    | Success s B      => Success   s  (Or A sB B)
    end.

  Definition mkAnd A B0 r :=
    match r with
    | Failure B       => Failure       (And A B0 B)
    | Expanded s B    => Expanded    s (And A B0 B)
    | CutBrothers s B => CutBrothers s (And (cutl A) (cutl B0) B)
    | Success s B      => Success      s (And A B0 B)
    end.

  Lemma get_state_And A B0 B : get_state (mkAnd A B0 B) = And (if is_cutbrothers B then cutl A else A) ((if is_cutbrothers B then cutl B0 else B0)) (get_state B).
  Proof. by case: B. Qed.

  Lemma get_state_Or A s B : get_state (mkOr A s B) = Or A s (get_state B).
  Proof. by case: B. Qed.

  Fixpoint big_and pr (a : list A) : state :=
    match a with
    | [::] => Top
    | x :: xs => And (Goal pr x)  (big_and pr xs) (big_and pr xs)
    end.

  Fixpoint big_or_aux pr (r : list A) (l : seq (Sigma * R)) : state :=
    match l with 
    | [::] => big_and pr r
    | (s,r1) :: xs => Or (big_and pr r) s (big_or_aux pr r1.(premises) xs)
    end.

  Definition big_or pr s t :=
    let l := F pr t s in
    if l is (s,r) :: xs then (Or Bot s (big_or_aux pr r.(premises) xs))
    else Bot.

  Lemma big_and_dead {p l}: is_dead (big_and p l) = false.
  Proof. elim l => //. Qed.

  Lemma big_and_cut {p l}: big_and p l = cutl (big_and p l) -> False.
  Proof. elim l => //. Qed.

  Lemma dead_big_or p s t: is_dead (big_or p s t) = false.
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
  Qed. 

  Fixpoint expand s A : expand_res :=
    match A with
    (* meta *)
    | OK => Success s OK
    | Bot => Failure Bot

    (* meta *)
    | Dead => Failure Dead
    
    (* lang *)
    | Top              => Expanded s OK
    | Goal _ Cut       => CutBrothers s OK
    | Goal pr (Call t) => Expanded s (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        if is_dead A then mkOr A sB (expand s B)
        else
        match expand s A with
        | Success s A    => Success s      (Or A sB B)
        | Expanded s A    => Expanded s  (Or A sB B)
        | CutBrothers s A => Expanded s  (Or A sB (cutr B))
        | Failure A     => Failure       (Or A sB B)
        end
    | And A B0 B =>
        match expand s A with
        | Success s1 A     => mkAnd    A B0  (expand s1 B)
        | Expanded s A    => Expanded s     (And A B0 B)
        | CutBrothers s A => CutBrothers s  (And A B0 B)
        | Failure A       => Failure        (And A B0 B)
        end
    end
  .

  (* OK returns None since,
     We can have the state "A" = (OK \/ B) /\ C
     It happens that the current substitution makes C to fail
     "A" becomes: (OK \/ B) /\ Bot.
     The OK node should be transformed into a Dead so that 
     "B /\ C" is tried with the subst for B *)
  Fixpoint next_alt (s : Sigma) (A : state) : option (Sigma * state) :=
    match A with
    | Bot | OK => None
    | Dead => None
    | Top | Goal _ _ => Some (s, A)
    | And A B0 B =>
      if is_dead A then None else
      if failed A then 
        match next_alt s A with
        | None => None
        | Some (s, A) => if failed B0 then None else Some (s, And A B0 B0)
        end
      else
      match next_alt s B, next_alt s A with
      | None, None => None
      | None, Some (s, A) => if failed B0 then None else Some (s, And A B0 B0)
      | Some (s, B), _ => Some (s, And A B0 B)
      end
    | Or A sB B => 
      if is_dead A then
        match next_alt s B with
        | None => None
        | Some (sB1, B) => Some (sB1, Or A sB B)
        end
      else
        match next_alt s A with
        | None =>
            if is_dead B then None else 
            (* if failed B then  *)
              match next_alt sB B with
              | None => None
              | Some (s, B) => Some (s, Or (dead1 A) sB B)
              end
            (* else Some (sB, Or (dead1 A) sB B) *)
        | Some (sA, A) => Some (sA, Or A sB B)
        end
  end.

  Inductive expandedb : Sigma -> state -> exp_res -> bool -> Prop :=
    | expanded_done {s s' A alt}     : expand s A = Success s' alt  -> expandedb s A (Done s' alt) false
    | expanded_fail {s A B}          : expand s A = Failure B -> expandedb s A (Failed B) false
    | expanded_cut {s s' r A B b}      : expand s A = CutBrothers s' B -> expandedb s' B r b -> expandedb s A r true
    | expanded_step {s s' r A B b}     : expand s A = Expanded s' B  -> expandedb s' B r b -> expandedb s A r b.

  Fixpoint clean_success (A: state):= 
    match A with
    | OK => Bot
    | Bot | Dead | Top | Goal _ _ => A
    | Or A s B => 
      if is_dead A then Or A s (clean_success B)
      else Or (clean_success A) s B
    | And A B0 B =>
      if success A then And A B0 (clean_success B)
      else And A B0 B
    end.

  Inductive runb : Sigma -> state -> Sigma -> state -> bool -> Prop :=
    | run_done {s s' A B C b}        : 
      expandedb s A (Done s' B) b -> C = clean_success B -> runb s A s' C b
    | run_backtrack {s s1 s2 A B C D b1 b2 b3} : 
        expandedb s A (Failed B) b1 -> next_alt s B = (Some (s1, C)) -> 
          runb s1 C s2 D b2 -> b3 = (b1 || b2) -> runb s A s2 D b3.

  Definition expanded s A r := exists b, expandedb s A r b.
  Definition run s A s1 B := exists b, runb s A s1 B b.

  Definition run_classic s A s1 B := runb s A s1 B false. 
  Definition expanded_classic s A r := expandedb s A r false. 


  (********************************************************************)
  (* EXPAND SIMPLIFICATION                                            *)
  (********************************************************************)

  Lemma simpl_expand_or_solved {s s1 s2 A B C} :
    expand s1 (Or A s B) = Success s2 C ->
      (exists A', expand s1 A = Success s2 A' /\ C = Or A' s B) \/
      (exists B', is_dead A /\ expand s1 B = Success s2 B' /\ C = Or A s B').
  Proof.
    move=> //=.
    case: ifP => dA.
      unfold mkOr.
      case X: expand => //-[]*;subst.
      right; do 2 eexists; repeat split.
    case Y: expand => //=-[]??;subst.
    by left; eexists.
  Qed.

  Lemma simpl_expand_or_fail {s s1 A B C} :
    expand s1 (Or A s B) = Failure C -> 
      (exists A', is_dead A = false /\ expand s1 A = Failure A' /\ C = Or A' s B) \/
      (exists B', is_dead A /\ expand s1 B = Failure B' /\ C = Or A s B').
  Proof.
    move=>/=; case: ifP => dA.
      rewrite /mkOr. 
      case X: expand => //= [D][]?;subst.
      by right; eexists; repeat split; rewrite dead2.
    case X: expand => // => -[]?;subst.
    by left; eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_solved {s s2 A B0 B C} :
    expand s (And A B0 B) = Success s2 C -> 
      exists s' A' B', 
        expand s A = Success s' A' /\
          expand s' B = Success s2 B' /\ C = And A' B0 B'.
  Proof.
    move=> //=; case X: expand => //.
    case Y: expand => // [s'' B'].
    move=> [] /[subst1] /[subst1].
    by do 3 eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_fail {s A B B0 C} :
    expand s (And A B0 B) = Failure C ->
      (exists A', expand s A = Failure A' /\ C = And A' B0 B) \/ 
        (exists s' A' B', expand s A = Success s' A' /\  
          expand s' B = Failure B' /\ C = And A' B0 B').
  Proof.
    move=> //=; case X: expand => //= [D|s' D].
    - by move=> []<-; left; eexists.
    - case Y: expand => //= -[]?;subst; right.
      by do 3 eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_cut {s s2 A B B0 C}:
    expand s (And A B0 B) = CutBrothers s2 C ->
    (exists A', expand s A = CutBrothers s2 A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Success s' A' /\ expand s' B = CutBrothers s2 B' /\ C = And (cutl A') (cutl B0) B').
  Proof.
    move=> //=; case X: expand => //=.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right; subst.
       do 3 eexists; repeat split => //=.
       apply Y.
  Qed.

  Lemma simpl_expand_and_expanded {s s2 A B B0 C}:
    expand s (And A B0 B) = Expanded s2 C ->
    (exists A', expand s A = Expanded s2 A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Success s' A' /\ expand s' B = Expanded s2 B' /\ C = And A' B0 B').
  Proof.
    move=> /=; case X: expand => //=.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right; subst.
      do 3 eexists; repeat split => //=; eassumption.
  Qed.

  (********************************************************************)
  (* EXPAND PROPERTIES                                                *)
  (********************************************************************)

  Lemma is_ko_expand {A s1}: is_ko A -> expand s1 A = Failure A.
  Proof.
    elim: A s1 => //.
    - move=> A HA s B HB s1 /=.
      case: ifP=> //dA/andP[kA kB].
        rewrite HB//.
      rewrite HA//.
    - move=> A HA B0 _ B HB s1 /= kA.
      rewrite HA//.
  Qed.

  Lemma is_dead_big_and {p r}: is_dead (big_and p r) = false.
  Proof. elim: r p => //=. Qed.

  Lemma is_dead_big_or {p r rs}: is_dead (big_or_aux p r rs) = false.
  Proof. 
    elim: rs r p => //=.
    - move=> *; apply: is_dead_big_and.
    - move=> [s r] l/= H rs p; rewrite H andbF//.
  Qed. 

  Lemma is_dead_expand {s A}: 
    is_dead A -> expand s A = Failure A.
  Proof. move=>/is_dead_is_ko/is_ko_expand//. Qed.

  Lemma is_ko_expanded s {A}: 
    is_ko A -> expandedb s A (Failed A) false.
  Proof. move=> dA; apply: expanded_fail (is_ko_expand _) => //. Qed.

  Lemma is_dead_expanded s {A}: 
    is_dead A -> expandedb s A (Failed A) false.
  Proof. move=>/is_dead_is_ko/is_ko_expanded//. Qed.

  Lemma succes_is_solved s {A}: success A -> expand s A = Success s A.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
      case:ifP => /eqP// H sA.
        rewrite (HB s)//.
      rewrite (HA s)//.
    + move=> A HA B0 HB0 B HB s /=.
      move=>/andP[sA sB].
      rewrite (HA s)// (HB s)//.
  Qed.

  Lemma expand_solved_same {s1 A s2 B}: 
    expand s1 A = Success s2 B -> ((s1 = s2) * (A = B))%type.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ??? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB s1 s2 C/=.
      case: ifP => dA.
        case X: expand =>//-[??];subst => /=.
        rewrite 2!(HB _ _ _ X)//.
      case X: expand => //-[??]; subst.
      rewrite 2!(HA _ _ _ X)//.
    + move=> A HA ? _ B HB s1 s2 C /=.
      case X: expand => //.
      case Y: expand => //=-[??]; subst.
      rewrite 2!(HA _ _ _ X)//2!(HB _ _ _ Y)//.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: 
    expand s1 A = Success s2 B -> (success A * success B)%type.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ??? [] /[subst2].
    + move=> p [] //.
    + move=> A HA s B HB s1 s2 C/=.
      case: ifP => dA.
        case X: expand =>//-[??];subst => /=.
        rewrite dA.
        by have := HB _ _ _ X.
      have:= HA s1; case: expand => //.
      move=> D E /(_ _ _ erefl)[->] sE [??]; subst => /=.
      rewrite sE.
      move: sE.
      by move=>/success_is_dead->.
    + move=> A HA ? _ B HB s1 s2 C /=.
      have:= HA s1.
      case: expand => // s D /(_ _ _ erefl)[]->.
      have:= HB s.
      case: expand => // s3 E /(_ _ _ erefl)[]->.
      by move=> sE sD [??]; subst => /=; rewrite sE sD.
  Qed.

  Lemma expanded_Done_success {s1 A s2 B b}: 
    expandedb s1 A (Done s2 B) b -> success B.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    by move=> s s' A B /expand_solved_success[sA sB] ?? [_<-].
  Qed.

  Lemma expanded_success {s A r b}: 
    success A -> expandedb s A r b -> r = Done s A /\ b = false.
  Proof.
    move=> sA H.
    inversion H; subst.
    - have:= succes_is_solved s sA.
      rewrite H0 => -[<-<-]//.
    - have:= succes_is_solved s sA; congruence. 
    - have := succes_is_solved s sA; congruence.
    - have := succes_is_solved s sA; congruence.
  Qed.

  Lemma expand_solved_is_solved {s s1 s2 A B}:
    expand s A = Success s1 B -> expand s2 B = Success s2 B.
  Proof. move=> /expand_solved_success[sA]. apply: succes_is_solved. Qed.

  Lemma expand_not_solved_not_success {s1 A r}:
    expand s1 A = r -> is_solved r = false -> success A = false.
  Proof.
    case: r=> //[s|s|]B/=; case X: success; try by rewrite // (succes_is_solved s1 X).
  Qed.

  Lemma expand_not_dead {s A r}: 
    is_dead A = false -> expand s A = r -> is_dead (get_state r) = false.
  Proof.
    move=> + <-.
    elim: A s; clear; try by move=> //=.
    + move=> p [|t]//= s _; apply dead_big_or.
    + move=> A HA s B HB s1 => //=.
      case: ifP => dA/=.
        rewrite get_state_Or/=dA; apply: HB.
      move=> _.
      have:= HA s1 dA.
      case X: expand => //=->//.
    + move=> A HA B0 _ B HB s1 //= dA.
      have:= HA s1 dA.
      case X: expand => [|||s A']//=dA'.
      rewrite get_state_And/= fun_if dA'.
      case Y: expand => //[s2 C]/=.
      have [sA']:= expand_solved_success X.
      move=>/success_cut.
      apply: success_is_dead.
  Qed.

  Lemma expanded_not_dead {s A r b}: 
    is_dead A = false -> expandedb s A r b -> is_dead (get_state_exp r) = false.
  Proof.
    move=> + H.
    elim: H; clear.
    + move=> s s' A A' H1 H2 /=; apply: expand_not_dead H2 H1.
    + move=> s A B H1 H2 /=; apply: expand_not_dead H2 H1.
    + move=> s s' r A A' b H _ IH dA; apply: IH (expand_not_dead dA H).
    + move=> s s' r A A' b H _ IH dA; apply: IH (expand_not_dead dA H).
  Qed.

  Lemma expand_solved_cutl {s1 A s2 B}: expand s1 A = Success s2 B -> cutl A = cutl B.
  Proof. move=> /expand_solved_same->//. Qed.

  Lemma expand_solved_failed {s1 A s2 B}: 
    expand s1 A = Success s2 B -> failed A = false /\ failed B = false.
  Proof.
    move=>/expand_solved_success [].
    by do 2 move=> /success_failed->.
  Qed.

  Lemma expand_failure_failed {s1 A B}:
    expand s1 A = Failure B -> (failed A * failed B)%type.
  Proof.
    elim: A s1 B; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2 C.
      move=>/simpl_expand_or_fail[].
        move=>[A'[dA[HA' ->]]] /=.
        rewrite dA (expand_not_dead dA HA'); apply: HA HA'.
      move=> [B' [dA [HB' ->]]] /=-.
      rewrite dA; apply: HB HB'.
    + move=> A HA B0 _ B HB s C.
      move=> /simpl_expand_and_fail[].
        move=> [A' [HA'->]]/=.
        by have:= HA _ _ HA'=>-[]-> //->.
      move=> [s' [A' [B' [HA' [HB' ->]]]]]/=.
      have:= HB _ _ HB' => -[]->->.
      have:= expand_solved_success HA' => -[] ->->.
      by rewrite !orbT.
  Qed. 

  Lemma failed_expand {s1 A}:
    failed A -> expand s1 A = Failure A.
  Proof.
    elim: A s1; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2/=.
      case: ifP => [dA fB|dA fA].
        rewrite HB//.
      rewrite HA//.
    + move=> A HA B0 _ B HB s/=.
      case X: failed => /=.
        move=>_; rewrite HA => //.
      move=>/andP[sA fB].
      rewrite succes_is_solved//.
      rewrite HB//.
  Qed. 

  Lemma expand_not_failed {s1 A r}:
    expand s1 A = r -> ~ (is_fail r) -> failed A = false.
  Proof.
    move=><-; clear r.
    elim: A s1; try by move=> // s1 <-//=.
    - move=> A HA s B HB s1/=.
      case: ifP => dA.
        have:= HB s1; case X: expand => //=; rewrite dA => H//.
      have:= HA s1.
      case X: expand => //= /(_ notF).
    - move=> A HA B0 _ B HB s1/=.
      have:= HA s1.
      case X: expand => //= [||s2 C]/(_ notF) ->; try rewrite (expand_not_solved_not_success X erefl)//.
      have [-> sC]:= expand_solved_success X.
      have:= HB s2.
      case Y: expand => //= H1; rewrite success_failed//=?success_cut//?sC/==>H2; rewrite H1//andbF//.
  Qed.


  Lemma expandedb_Done_not_failed {s1 A s2 B b}: 
    expandedb s1 A (Done s2 B) b -> failed A = false.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    - move=> s s' A A'/expand_solved_failed [->]//.
    - move=> s s' r A B b HA HB IH s1 C ?; subst.
      apply: expand_not_failed HA _ => //.
    - move=> s s' r A B b HA HB IH s1 C ?; subst.
      apply: expand_not_failed HA _ => //.
  Qed.

  Lemma expandedb_big_or_not_done {s p s1 t res b}:
    expandedb s (big_or p s1 t) res b -> is_done res = false.
  Proof.
    rewrite /big_or; case f: F => [|[s2 r] rs].
      inversion 1; subst => //.
    inversion 1; subst => //.
  Qed.


  (********************************************************************)
  (* NEXT_ALT OP PROPERTIES                                           *)
  (********************************************************************)

  Lemma is_ko_next_alt {s A}: is_ko A -> next_alt s A = None.
  Proof.
    elim: A s => //.
      move=> A HA s1 B HB s2 /=/andP[kA kB].
      rewrite HA//!HB//!if_same//.
    move=> A HA B0 _ B HB /= s1 kA.
    rewrite is_ko_failed//HA//if_same//.
  Qed.

  Lemma is_dead_next_alt {s A}: is_dead A -> next_alt s A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed.

  Definition same_sol (A B : option (Sigma * state)) := 
    match A, B with
    | None, None => true
    | Some (_, A), Some (_, B) => A == B
    | _, _ => false
    end.

  Lemma next_alt_same_sol s1 s2 A:
    same_sol (next_alt s1 A) (next_alt s2 A).
  Proof.
    elim: A s1 s2 => //; try by move=> [] *; subst.
    + by move=> ??[]/=.
    + move=> A HA s B HB s1 s2 /=.
      case:ifP => dA.
        have:= HB s1 s2.
        case: next_alt => //[[s5 E]|]; case: next_alt => //[[s6 F]].
        by move=> /=/eqP->.
      have:= HA s1 s2.
      case NA: next_alt => [[s3 C]|].
        by case: next_alt => // [[s4 D]]/eqP->/=; rewrite eqxx.
      case: next_alt => // _.
      case: ifP => dB//.
      (* case: ifP => fB//=. *)
      (* have:= HB s1 s2. *)
      case: next_alt => [[??]|]//=.
        (* by case: next_alt => [[??]|]///eqP<-. *)
      (* case: next_alt => //. *)
    + move=> A HA B0 _ B HB s1 s2 /=.
      case: ifP => // _.
      case: ifP => // _.
        have:= HA s1 s2.
        case NA: next_alt => [[s3 C]|].
          case: next_alt => [[s4 D]|]///eqP->/=.
          case: ifP => //=.
        case: next_alt => //.
      have:= HB s1 s2.
      case: next_alt => //[[??]|].
        case: next_alt => //[[??]]/eqP->//=.
      case: next_alt => //.
      have:= HA s1 s2.
      case: next_alt => //=[[s3 C]|]; case: next_alt => //[[s4 D]].
      move=>/eqP ->/=.
      case: ifP => //=.
  Qed.

  Lemma next_alt_none {s1 A}:
    next_alt s1 A = None ->
      forall s2, next_alt s2 A = None.
  Proof.
    move=> H s2.
    have := next_alt_same_sol s1 s2 A.
    rewrite H => /=; case: next_alt => //.
  Qed.

  Lemma next_alt_some {s1 s2 A B}:
    next_alt s1 A = Some (s2, B) ->
      (forall s3, exists s4, next_alt s3 A = Some (s4, B)).
  Proof.
    move=> H s3.
    have := next_alt_same_sol s1 s3 A.
    rewrite H/=.
    by case X: next_alt => // [[s4 C]]/eqP->; eexists.
  Qed.

  Lemma next_alt_dead {A D s1 s2}: 
    next_alt s1 A = Some (s2, D) -> is_dead A = false /\ is_dead D = false.
  Proof.
    elim: A D s1 s2 => //.
    - move=>/=???[_<-]//.
    - move=>/=?????[_<-]//.
      move=> A HA s B HB C s1 s2/=.
      case: ifP => dA.
        case X: next_alt => //[[s3 D]].
        have [??]:= HB _ _ _ X.
        move=> []??;subst => /=; split => //.
        rewrite dA//.
      case X: next_alt => //= [[s3 D]|].
        move=>[_<-]; split => //=; rewrite (proj2 (HA _ _ _ X))//.
      case: ifP => dB//.
      (* case:ifP => fB. *)
        case Y: next_alt => //[[s3 D]] [_ <-]/=.
        rewrite is_dead_dead (proj2 (HB _ _ _ Y))//.
      (* move=>[_ <-]/=; rewrite is_dead_dead; split => //. *)
    move=> A HA B0 _ B HB C s1 s2 /=.
    case: ifP => dA//.
    case X: next_alt => //[[s3 D]|].
      case: ifP => fA.
        case: ifP => //fB0[_<-]/=; rewrite (proj2 (HA _ _ _ X))//.
      case Y: next_alt => [[s4 E]|].
        move=> [_<-]/=; rewrite dA//.
      case: ifP => fB0//[_<-]/=; rewrite (proj2 (HA _ _ _ X))//.
    case: ifP => fA//.
    case Y: next_alt => [[s3 D]|]//[_<-]//.
  Qed.

  Lemma next_alt_failed {s A s1 B}:
    next_alt s A = Some (s1, B) -> ((failed B = false) * (success B = false))%type.
  Proof.
    elim: A B s s1 => //.
    - move=>/=???[_<-]//.
    - move=>?????[_<-]//.
      move=> A HA s B HB C s1 s2/=.
      case X: next_alt => [[s3 D]|].
        case: ifP => dA.
          move=>[_<-]/=; rewrite dA; apply: HB X.
        case Y: next_alt => [[s4 E]|]//.
          move=>[_<-]/=.
          rewrite (HA _ _ _ Y)//(proj2 (next_alt_dead Y))(HA _ _ _ Y)//.
        case: ifP => dB//.
        have [s' H]:= next_alt_some X s.
        rewrite H.
        by move=> [_<-]/=; rewrite is_dead_dead//; apply: HB X.
      case: ifP => //dA.
      case Y: next_alt => [[s4 E]|]//.
        move=>[_<-]/=.
        rewrite (HA _ _ _ Y)// (proj2 (next_alt_dead Y))(HA _ _ _ Y)//.
      case: ifP => //dB.
      rewrite (next_alt_none X s)//.
      (* do 2 case: ifP => //; move=> fB dB [_<-]/=. *)
      (* rewrite [failed(dead1 _)]is_dead_failed is_dead_dead//. *)
    move=> A HA B0 _ B HB C s1 s2/=.
    case: ifP => dA//.
    case: ifP => fA.
      case X: next_alt => //[[s3 D]].
      case: ifP => // fB0 [_<-]/=; rewrite fB0 andbF !(HA _ _ _ X)//.
    case X: next_alt => [[s4 E]|].
      move=>[_<-]/=; rewrite fA !(HB _ _ _ X) andbF//.
    case Y: next_alt => //[[s3 D]].
    case: ifP => // fB0 [_<-]/=.
    rewrite fB0 andbF !(HA _ _ _ Y)//.
  Qed.

  Lemma next_alt_or_some {s B s' C y}:
    next_alt s B = Some (s', C) ->  is_dead y = false -> forall x, next_alt s (Or B x y) = Some (s', Or C x y).
  Proof.
    move=> /= H dy x.
    have [dB dC] := next_alt_dead H.
    rewrite dB H//.
  Qed.

  Lemma next_alt_clean_success {s s1 B}:
    success B -> next_alt s B = None ->
      next_alt s1 (clean_success B) = None.
  Proof.
    elim: B s s1 => //.
    - move=> A HA s B HB s1 s2/=.
      case: ifP => dA.
        move=>sB.
        case X: next_alt => [[s3 C]|]//.
        move=>/=; rewrite (HB s1 s2)// dA//.
      move=> sA.
      case X: next_alt => [[s3 C]|]//.
      case: ifP => dB.
        rewrite /= (HA s1 s2)//dB is_dead_next_alt//if_same//.
      (* case: ifP => fB//. *)
      case Y: next_alt => [[s3 C]|]//=.
      have:= next_alt_none Y=>->.
      rewrite (HA s1 s2)//Y!if_same//.
    - move=> A HA B0 _ B HB/= s1 s2/andP[sA sB].
      rewrite sA/= success_is_dead//success_failed//.
      case Y: next_alt => [[s3 C]|]//.
      rewrite (HB s1 s2)//.
      case Z: next_alt => [[s3 D]|]//.
        case: ifP => //fB0.
        case: next_alt => [[s4 E]|]//; rewrite !if_same//.
      by have:= next_alt_none Z s2 => ->.
  Qed.
End Run.
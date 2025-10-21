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

Inductive state :=
  | Bot : state
  | OK : state
  | Top : state
  | Dead : state
  | CallS : program  -> Callable -> state
  | CutS : state
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
    | OK | Bot | CutS | CallS _ _ | Top => Dead
    | And A B0 B => And (dead1 A) (dead1 B0) (dead1 B)
    | Or A s B => Or (dead1 A) s (dead1 B)
    end.

  Fixpoint is_dead A :=
    match A with
    | Dead => true
    | OK | Bot | CutS | CallS  _ _ | Top => false
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
    | OK | CutS | CallS  _ _ | Top => false
    | And A B0 B => is_ko A
    | Or A s B => is_ko A && is_ko B
    end.

  Fixpoint success (A : state) : bool :=
    match A with
    | OK => true
    | Top | CutS | CallS _ _ | Bot | Dead => false
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
    | Top | CutS | CallS _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    (* We keep the if condition to have the right behavior in next_alt *)
    | Or A _ B => if is_dead A then failed B else failed A (*&& failed B*)
    end.


  Fixpoint cutr A :=
    match A with
    | CutS | CallS _ _ | Top | Bot => Bot
    | OK => Bot
    | Dead => Dead
    | And A B0 B => And (cutr A) (cutr B0) (cutr B)
    | Or A s B => Or (cutr A) s (cutr B)
    end.

  Fixpoint cutl A :=
    (* if A == dead A then Dead else *)
    match A with
    | CutS | CallS _ _ | Top | Bot => Bot
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
  
  Lemma cutr_dead {a}: cutr (dead1 a) = dead1 a.
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

  Lemma is_dead_cutr {A}: is_dead (cutr A) = is_dead A.
  Proof. elim: A => //A HA s B HB/=; rewrite HA HB//. Qed.

  Lemma is_dead_cutl {A}: is_dead (cutl A) = is_dead A.
  Proof. elim: A => //A HA s B HB/=; rewrite fun_if/=HB HA is_dead_cutr if_same//. Qed.


  Lemma success_cut {A} : success (cutl A) = success A.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      case: ifP => /= dA; rewrite ?is_dead_cutl dA//.
    + move=> A HA B HB C HC /=.
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
    rewrite success_cut//sA/=HB//orbT//.
  Qed.    
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

Definition A2CallCut pr (A:A) : state :=
  match A with
  | ACut => CutS
  | ACall tm => CallS pr tm
  end.

Fixpoint big_and pr (a : list A) : state :=
  match a with
  | [::] => Top
  | x :: xs => And (A2CallCut pr x)  (big_and pr xs) (big_and pr xs)
  end.

Fixpoint big_or_aux pr (r : list A) (l : seq (Sigma * R)) : state :=
  match l with 
  | [::] => big_and pr r
  | (s,r1) :: xs => Or (big_and pr r) s (big_or_aux pr r1.(premises) xs)
  end.

Lemma big_and_dead {p l}: is_dead (big_and p l) = false.
Proof. elim l => //-[]//. Qed.

Lemma big_and_cut {p l}: big_and p l = cutl (big_and p l) -> False.
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

  Fixpoint expand s A : expand_res :=
    match A with
    (* meta *)
    | OK => Success s OK
    | Bot => Failure Bot

    (* meta *)
    | Dead => Failure Dead
    
    (* lang *)
    | Top              => Expanded s OK
    | CutS       => CutBrothers s OK
    | CallS pr t => Expanded s (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        if is_dead A then mkOr A sB (expand sB B)
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

  Fixpoint clean_success (A: state):= 
    match A with
    | OK => Bot
    | Bot | Dead | Top | CutS | CallS _ _ => A
    | Or A s B => 
      if is_dead A then Or A s (clean_success B)
      else Or (clean_success A) s B
    | And A B0 B =>
    (* TODO: cambiare con And (clean_success A) B0 B0 *)
      if success A then And A B0 (clean_success B)
      else And A B0 B
    end.

  (* OK returns None since,
     We can have the state "A" = (OK \/ B) /\ C
     It happens that the current substitution makes C to fail
     "A" becomes: (OK \/ B) /\ Bot.
     The OK node should be transformed into a Dead so that 
     "B /\ C" is tried with the subst for B *)
    (* TODO: togliere s come argomento? *)
  Fixpoint next_alt (A : state) : option (state) :=
    match A with
    | Bot => None
    | Dead => None
    | OK | Top | CutS | CallS _ _ => Some A
    | And A B0 B =>
      if is_dead A then None else
      if failed A then 
        match next_alt A with
        | None => None
        | Some (A) => Some (And A B0 B0)
        end
      else
      if success A then
        match next_alt B with
        | None => Some (And (clean_success A) B0 B0)
        | Some (B) => Some (And A B0 B)
        end
      else Some (And A B0 B)
    | Or A sB B => 
      if is_dead A then
        match next_alt B with
        | None => None
        | Some B => Some (Or A sB B)
        end
      else
        match next_alt A with
        | None =>
          if is_dead B then None else 
          (* if failed B then  *)
            match next_alt B with
            | None => None
            | Some B => Some (Or (dead1 A) sB B)
            end
          (* else Some (sB, Or (dead1 A) sB B) *)
        | Some (A) => Some (Or A sB B)
        end
  end.

  Lemma next_alt_not_failed A:
    (failed A) = false -> next_alt A = Some A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA fB.
        rewrite HB//=.
      rewrite HA//.
    - move=> A HA B0 _ B HB.
      case: ifP => dA.
        rewrite is_dead_failed//.
      case: ifP => //=fA.
      case: ifP => //=sA fB.
      rewrite HB//.
  Qed.

  Goal next_alt (And (Or OK empty Top) OK Bot) = Some (And (Or Bot empty Top) OK OK).
  Proof. move=> //=. Qed.

  Goal next_alt (And (Or OK empty OK) OK Bot) = Some (And (Or Bot empty OK) OK OK).
  Proof. move=> //=. Qed.

  Goal (next_alt (Or Bot empty OK)) = Some (Or Dead empty OK). move=> //=. Qed.

  (* Lemma success_next_alt {B x} y:
    success B -> next_alt x B = next_alt y B.
  Proof.
    elim: B x y => //=.
    - move=> A HA s B HB x y; case:ifP => //dA sA; rewrite (HA _ y sA)//.
    - move=> A HA B0 _ B HB x y /andP[sA sB].
      rewrite success_is_dead// success_failed//.
      rewrite (HB _ y sB) (HA _ y sA)//.
  Qed.

  Lemma failed_next_alt {B x} y:
    failed B ->
      next_alt x B = next_alt y B.
  Proof.
    elim: B x y => //=.
    - move=> A HA s B HB x y.
      case: ifP => dA f.
        case X: next_alt => //.
      rewrite (HA _ y)//.
    - move=> A HA B0 _ B HB x y.
      case: ifP => // dA.
      move=> /orP[fA|/andP[sA fB]].
        rewrite fA //.
        rewrite (HA _ y)//.
      rewrite success_failed//.
      rewrite (HB _ y)//(success_next_alt y)//.
  Qed. *)

  Inductive expandedb : Sigma -> state -> exp_res -> bool -> Prop :=
    | expanded_done {s s' A alt}     : expand s A = Success s' alt  -> expandedb s A (Done s' alt) false
    | expanded_fail {s A B}          : expand s A = Failure B -> expandedb s A (Failed B) false
    | expanded_cut {s s' r A B b}      : expand s A = CutBrothers s' B -> expandedb s B r b -> expandedb s A r true
    | expanded_step {s s' r A B b}     : expand s A = Expanded s' B  -> expandedb s B r b -> expandedb s A r b.

  Inductive runb : Sigma -> state -> Sigma -> state -> bool -> Prop :=
    | run_done {s s' A B C b}        : 
      expandedb s A (Done s' B) b -> C = clean_success B -> runb s A s' C b
    | run_backtrack {s s2 A B C D b1 b2 b3} : 
        expandedb s A (Failed B) b1 -> next_alt B = (Some (C)) -> 
          (* Note: if a next_alt exists the subst considered is taken from the tree *)
          runb s C s2 D b2 -> b3 = (b1 || b2) -> runb s A s2 D b3.

  Definition dead_run s1 A := forall s2 B b, runb s1 A s2 B b -> False.

  (* Definition expandedb s A r := exists b, expandedb s A r b.
  Definition run s A s1 B := exists b, runb s A s1 B b.

  Definition run_classic s A s1 B := runb s A s1 B false. 
  Definition expanded_classic s A r := expandedb s A r false.  *)


  (********************************************************************)
  (* EXPAND SIMPLIFICATION                                            *)
  (********************************************************************)

  Lemma simpl_expand_or_solved {s s1 s2 A B C} :
    expand s1 (Or A s B) = Success s2 C ->
      (exists A', expand s1 A = Success s2 A' /\ C = Or A' s B) \/
      (exists B', is_dead A /\ expand s B = Success s2 B' /\ C = Or A s B').
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
      (exists B', is_dead A /\ expand s B = Failure B' /\ C = Or A s B').
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
  Proof. elim: r p => //=-[]//. Qed.

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

  (* Lemma expand_solved_success {s1 A s2 B}: 
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
  Qed. *)

  Fixpoint get_substS s A :=
    match A with
    | Top | CutS | CallS _ _ | Bot | OK | Dead => s
    | Or A s1 B => if is_dead A then get_substS s1 B else get_substS s A
    | And A _ B => if success A then get_substS (get_substS s A) B else (get_substS s A)
    end.

  Lemma succes_is_solved s {A}: success A -> expand s A = Success (get_substS s A) A.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
      case:ifP => //= H sA.
        rewrite HB//=.
      rewrite HA//.
    + move=> A HA B0 HB0 B HB s /=.
      move=>/andP[sA sB].
      rewrite sA HA// HB//.
  Qed.

  Lemma expand_solved_same {s1 A s2 B}: 
    expand s1 A = Success s2 B -> (((s2 = get_substS s1 A) * (A = B)) * (success B))%type.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ??? [] /[subst2].
    + move=> A HA s B HB s1 s2 C/=.
      case: ifP => dA/=.
        case X: expand =>//-[??];subst => /=.
        rewrite dA !(HB _ _ _ X)//.
      case X: expand => //=-[??]; subst => /=.
      have {}HA := HA _ _ _ X.
      rewrite success_is_dead !HA//.
    + move=> A HA B0 _ B HB s1 s2 C /=.
      case X: expand => // [s3 A'].
      case Y: expand => //=[s4 B'][??]; subst.
      have {}HA := HA _ _ _ X.
      have {}HB := HB _ _ _ Y.
      rewrite /= !HA !HB !HA//.
  Qed.

  Lemma expand_failed_same {s1 A B}: 
    expand s1 A = Failure B -> ((A = B))%type.
  Proof.
    elim: A s1 B => //.
    + move=> s1 B[<-]//.
    + move=> s1 B[<-]//.
    + move=> A HA s B HB s1 C/=.
      case: ifP => dA/=.
        case X: expand =>//-[?];subst => /=.
        rewrite (HB _ _ X)//.
      case X: expand => //=-[?]; subst => /=.
      rewrite (HA _ _ X)//.
    + move=> A HA B0 _ B HB s1 C /=.
      case X: expand => // [A'|s' A'].
        move=> [<-]; rewrite (HA _ _ X)//.
      case Y: expand => //=[B'][<-].
      rewrite (HB _ _ Y) (expand_solved_same X)//.
  Qed.

  Lemma expanded_Done_success {s1 A s2 B b}: 
    expandedb s1 A (Done s2 B) b -> success B.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    move=> s s' A B /expand_solved_same H ??; rewrite !H => -[_<-]; rewrite H//.
  Qed.

  Lemma run_Solved_id {s s1 A r alt b}:
      expand s A = Success s1 alt -> expandedb s A r b -> r = Done s1 alt.
  Proof.
    move=> + H; by case: H => //=; clear; congruence.
  Qed.

  Lemma expanded_success1 {A} s: 
    success A -> expandedb s A (Done (get_substS s A) A) false.
  Proof.
    move=> sA.
    apply: expanded_done.
    apply: succes_is_solved sA.
  Qed.

  Lemma expanded_consistent: forall {s0 A s1 s2 b1 b2},
    expandedb s0 A s1 b1 -> expandedb s0 A s2 b2 -> ((s1 = s2) * (b1 = b2))%type.
  Proof.
    move=> s0 A s1 + b1 + H.
    elim:H; clear.
    + move=> s s' A alt H b1 b2 H1.
      move: (run_Solved_id H H1) => /[subst1].
      by inversion H1; try congruence; subst.
    + move=> s A B HA r b H0.
      inversion H0; try congruence; subst.
      move: H1; rewrite HA => -[] /[subst1]//.
    + move=> s1 s2 r A B b HA HB IH s3 b1; inversion 1; try congruence; subst.
      move: H1; rewrite HA => -[] /[subst2].
      by have:= IH _ _ H2 => -[] /[subst2].
    + move=> s1 s2 r A B b1 + HB IH r2 b2 HA.
      inversion HA; try congruence; subst; rewrite H0 => -[] /[subst2]; auto.
  Qed.

  Lemma run_consistent {s A s1 B b1}:
    runb s A s1 B b1 -> forall {s2 C b2}, runb s A s2 C b2 -> ((s1 = s2) * (B = C) * (b1 = b2))%type.
  Proof.
    move=> H; elim: H; clear.
    + move=> s s' A B C b H -> s2 D b2 H1.
      inversion H1; clear H1; subst;
      by have:= expanded_consistent H H0 => -[] // [->->]->//.
    + move=> s s1 A B C D b1 b2 b3 HA HB HC IH ? s3 E s4 H1; subst.
      inversion H1; subst; have [] := expanded_consistent HA H0 => //.
      move=>[??]; subst.
      move: H2; rewrite HB => -[?]; subst.
      have {}H := IH _ _ _ H3.
      rewrite !H//.
  Qed.

  Lemma is_ko_next_alt {A}: is_ko A -> next_alt A = None.
  Proof.
    elim: A => //.
      move=> A HA s1 B HB /=/andP[kA kB].
      rewrite HA//!HB//!if_same//.
    move=> A HA B0 _ B HB /= kA.
    rewrite is_ko_failed//HA//if_same//.
  Qed.

  Lemma is_ko_clean_success {A}: is_ko A -> clean_success A = A.
  Proof.
    elim: A => //.
      move=> A HA s1 B HB /=/andP[kA kB].
      case: ifP => dA; rewrite ?HA//HB//.
    move=> A HA B0 _ B HB /= kA; case: ifP => //=.
    rewrite is_ko_success//.
  Qed.

  Lemma success_clean_success_dead A:
    success A -> is_dead (clean_success A ) = false.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB.
      case: ifP => [dA sB|dA sA]/=.
        rewrite dA HB//.
      rewrite HA//.
    - move=> A HA B0 _ B HB/andP[/[dup]sA-> sB]/=.
      rewrite success_is_dead//.
  Qed.

  Lemma success_clean_success_failed {A}: success A -> failed (clean_success A).
  Proof.
    elim: A => //.
      move=> A HA s1 B HB /=.
      case: ifP => dA s/=.
        rewrite dA HB//.
      rewrite HA//success_clean_success_dead//.
    move=> A HA B0 _ B HB /= /andP[sA sB].
    by rewrite sA/= sA HB// orbT.
  Qed.

  Lemma is_ko_runb {s s1 A B b}: is_ko A -> runb s A s1 B b -> False.
  Proof.
    elim: A s s1 B b => //=.
    - move=> s s1 B b _; inversion 1; inversion H1 => //; subst.
      move: H13 => [?]; subst => //.
    - move=> s s1 B b _; inversion 1; inversion H1 => //; subst.
      move: H13 => [?]; subst => //.
    - move=> A HA s B HB s1 s2 C b /andP[H1 H2].
      inversion 1; subst.
      - have:= @is_ko_expanded s1 (Or A s B) => /=.
        rewrite H1 H2 => /(_ isT).
        move=> /(expanded_consistent H3)[]//.
      - have:= @is_ko_expanded s1 (Or A s B) => /=.
        rewrite H1 H2 => /(_ isT).
        move=> /(expanded_consistent H3)[]//[??]; subst.
        rewrite is_ko_next_alt//=H1 H2// in H4.
    - move=> A HA B0 HB0 B HB s1 s2 C b kA. 
      inversion 1; subst.
      - have:= @is_ko_expanded s1 (And A B0 B) kA.
        move=> /(expanded_consistent H1)[]//.
      - have:= @is_ko_expanded s1 (And A B0 B) kA.
        move=> /(expanded_consistent H1)[]//[??]; subst.
        rewrite is_ko_next_alt// in H2.
  Qed.

  Lemma expanded_success {s A r b}: 
    success A -> expandedb s A r b -> ((r = Done (get_substS s A) A) * (b = false))%type.
  Proof. move=> sA H; have:= expanded_success1 s sA => /(expanded_consistent H)//. Qed.

  Lemma runb_success {A} s1: 
    success A -> runb s1 A (get_substS s1 A) (clean_success A) false.
  Proof.
    move=> sA.
    apply: run_done erefl.
    apply: expanded_success1 sA.
  Qed.

  Lemma expand_not_solved_not_success {s1 A r}:
    expand s1 A = r -> ~ (is_solved r) -> success A = false.
  Proof.
    case: r=> //[s|s|]B/=; case X: success; try by rewrite // (succes_is_solved s1 X).
  Qed.

  Lemma expand_cb_same_subst {A B s1 s2}:
    expand s1 A = CutBrothers s2 B -> s2 = get_substS s1 A.
  Proof.
    elim: A B s1 s2 => //=.
    - move=> B s1 s2 []//.
    - move=> A HA s B HB C s1 s2; case: ifP => dA; case: expand => //.
    - move=> A HA B0 _ B HB C s1 s2.
      case e: expand => //[s' A'|s' A'].
        move=>[??]; subst.
        rewrite (HA _ _ _ e) (expand_not_solved_not_success e)//.
      have [[??] SA] := expand_solved_same e; subst.
      rewrite SA.
      case e1: expand => //=[s3 B'][<-] _.
      apply: HB e1.
  Qed.

  Lemma expand_not_dead {s A r}: 
    is_dead A = false -> expand s A = r -> is_dead (get_state r) = false.
  Proof.
    move=> + <-.
    elim: A s; clear; try by move=> //=.
    - move=> p t s/= _; apply dead_big_or.
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
      have [[??]]:= expand_solved_same X; subst.
      rewrite -success_cut.
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
      have [[??]H] := expand_solved_same HA'; subst; rewrite H !orbT//.
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
        by have:= HB s; case X: expand.
      by have:= HA s1; case X: expand.
    - move=> A HA B0 _ B HB s1/=.
      have:= HA s1.
      case X: expand => //= [||s2 C] ->; try by rewrite?(expand_not_solved_not_success X)//.
      rewrite (expand_solved_same X)/=.
      have:= HB (get_substS s1 A).
      case Y: expand => //= ->//; rewrite andbF//.
  Qed.

  Lemma expand_not_failed_Expanded {s1 A s2 B}:
    (* This is wrong: if A is a call and there is no impl, then B = Bot which is failed *)
    expand s1 A = Expanded s2 B -> failed B = false.
  Proof.
  Abort.

  Lemma expandedb_Done_not_failed {s1 A s2 B b}: 
    expandedb s1 A (Done s2 B) b -> failed A = false.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd => //; clear.
    - move=> s s' A A' /expand_solved_same [[??]+] ??[??]; subst => /success_failed//.
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

  Lemma failed_big_or p s t: failed (big_or p s t).
  Proof. rewrite/big_or; case: F => //-[]//. Qed.

  Lemma expandedb_failed {s1 A B b1}: expandedb s1 A (Failed B) b1 -> failed B.
  Proof.
    remember (Failed B) as fB eqn:HfB => H.
    elim: H B HfB => //; clear.
    move=> s1 A B H C []<-.
    have []:= expand_failure_failed H => //.
  Qed.

  (********************************************************************)
  (* NEXT_ALT OP PROPERTIES                                           *)
  (********************************************************************)

  Lemma is_dead_next_alt {A}: is_dead A -> next_alt A = None.
  Proof. move=>/is_dead_is_ko/is_ko_next_alt//. Qed.

  (* Definition same_sol (A B : option (Sigma * state)) := 
    match A, B with
    | None, None => true
    | Some (s1, A), Some (s2, B) => (A == B)
    | _, _ => false
    end.

  Lemma same_sol_refl A: same_sol A A.
  Proof.
    case: A => //-[s A]/=.
    rewrite !eqxx//.
  Qed. *)

  (* Lemma next_alt_same_sol s1 s2 A:
    same_sol (next_alt s1 A) (next_alt s2 A).
  Proof.
    elim: A s1 s2 => //; try by move=> [] *; subst.
    + move=> ??/=.
    + move=> A HA s B HB s1 s2 /=.
      case:ifP => dA.
        rewrite same_sol_refl//.
      (*         
        have:= HB s1 s2.
        case: next_alt => //[[s5 E]|]. case: next_alt => //[[s6 F]].
        by move=> /=/eqP->. *)
      have:= HA s1 s2.
      case NA: next_alt => [[s3 C]|].
        by case: next_alt => // [[s4 D]]/eqP->/=; rewrite eqxx.
      case: next_alt => // _.
      rewrite same_sol_refl//.
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
  Qed. *)

  Lemma next_alt_dead {A D}: 
    next_alt A = Some (D) -> ((is_dead A = false) * (is_dead D = false))%type.
  Proof.
    elim: A D => //=; try by move=>/=?[]//<-//.
    - move=>/= p c d []// <-//.
    - move=> A HA s B HB C/=.
      case: ifP => dA.
        case X: next_alt => //[D].
        have [??]:= HB _ X.
        move=> []?;subst => /=; split => //.
        rewrite dA//.
      case X: next_alt => //= [D|].
        move=>[<-]; split => //=; rewrite ((HA _ X))//.
      case: ifP => dB//.
        case Y: next_alt => //[D] [<-]/=.
        rewrite is_dead_dead ((HB _ Y))//.
    move=> A HA B0 _ B HB C /=.
    case: ifP => dA//.
    case: ifP => fA.
      case X: next_alt => //[A0].
      move=> [<-]/=; rewrite HA//.
    case: ifP => sA/=.
      case X: next_alt => [B'|][<-]/=.
        rewrite dA//.
      rewrite success_clean_success_dead//.
    move=>[<-]//.
  Qed.

  (* Lemma next_alt_failed {A B}:
    next_alt A = Some (B) -> ((failed B = false))%type.
  Proof.
    elim: A B => //=; try by move=>/=?[]//<-//.
    - move=>???[]//<-//.
    - move=> A HA s B HB C /=.
      case X: next_alt => [D|].
        case: ifP => dA.
          move=>[<-]/=; rewrite dA.
          apply: HB X.
        case Y: next_alt => [E|]//.
          move=>[<-]/=.
          rewrite (HA _ Y).
          case:ifP => //.
          rewrite (next_alt_dead Y)//.
        case: ifP => dB//[?]; subst => /=.
        rewrite is_dead_dead.
        apply: HB X.
      case: ifP => //dA.
      case Y: next_alt => [E|]//.
        move=>[<-]/=.
        rewrite (HA _ Y)// ((next_alt_dead Y))//.
      by case: ifP => //.
    move=> A HA B0 _ B HB C/=.
    case: ifP => dA//.
    case: ifP => fA.
      case X: next_alt => //[D].
      case: ifP => // fB0 [<-]/=; rewrite fB0 andbF !(HA _ X)//.
    case: ifP => sA.
      case X: next_alt => [E|].
        move=>[<-]/=; rewrite fA !(HB _ X) andbF//.
      move=>[<-]/=.
      admit.
    move=> [<-]/=.
    rewrite fA sA//.
  Qed. *)

  Lemma next_alt_clean_success {B}:
    success B -> next_alt B = None ->
      next_alt (clean_success B) = None.
  Proof.
    elim: B => //.
    - move=> A HA s B HB/=.
      case: ifP => dA.
        move=>sB.
        case X: next_alt => [C|]//=.
        rewrite dA HB//.
      move=> sA.
      case X: next_alt => [C|]//.
      case: ifP => dB.
        rewrite /= (HA)//dB is_dead_next_alt//if_same//.
      case Y: next_alt => [C|]//=.
      rewrite Y.
      rewrite (HA sA X)// !if_same//.
    - move=> A HA B0 _ B HB/= /andP[sA sB].
      rewrite sA/= success_is_dead//success_failed//.
      case Y: next_alt => [C|]//.
  Qed.

  Section same_structure.

    Fixpoint same_structure A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => [&& same_structure B0 B0', same_structure A1 A' & same_structure B1 B']
        | _ => false
        end
      | Or A1 s B1 =>
        match B with 
        | Or A' s' B' => [&& s == s', same_structure A1 A' & same_structure B1 B']
        | _ => false
        end
      | _ => true
      end.

    Lemma same_structure_id {A}: same_structure A A.
    Proof. 
      elim: A => //=.
        by move=>?->??->; rewrite eqxx.
      by move=> ?->? ->?->.
    Qed.

    Lemma same_structure_trans: transitive same_structure.
    Proof.
      move=> + A; elim: A => //.
      - move=> A HA s B HB []//A' s' B'[]//A2 s2 B2/=.
        move=>/and3P[/eqP<-HA' HB']/and3P[/eqP<-HA2 HB2].
        rewrite eqxx (HA A' A2)//(HB B' B2)//.
      - move=> A HA B0 HB0 B HB[]//A1 B01 B1[]//A2 B02 B2/=.
        move=>/and3P[HA1 HB01 HB1]/and3P[HA2 HB02 HB2].
        rewrite (HA A1 A2)//(HB B1 B2)//(HB0 B01 B02)//.
    Qed.

    Lemma same_structure_cutr {A B}: same_structure A B -> same_structure A (cutr B).
    Proof. 
      elim: A B => //=.
        by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=/and3P[/HB0-> /HA-> /HB->]//.
    Qed.
    
    Lemma same_structure_cut {A B}: same_structure A B -> same_structure A (cutl B).
    Proof. 
      elim: A B => //=.
        move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<- H2 H3].
        case: ifP => //.
          by rewrite H2 HB//eqxx.
        by rewrite eqxx HA// same_structure_cutr//.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=. 
      move=> /and3P[sB0 sA sB].
      rewrite HA//HB0//HB//.
    Qed.
    
    Lemma same_structure_dead {B}: same_structure B (dead1 B).
    Proof. 
      elim: B => //=.
        move=> A HA s B HB; rewrite eqxx HA HB//.
      move=> A HA B0 HB0 B HB; rewrite HA HB0 HB//.
    Qed.

    Lemma expand_same_structure {s A r}: 
      expand s A = r -> same_structure A (get_state r).
    Proof.
      elim: A s r => //.
        move=> A HA s B HB s1 [s2|s2||s2] C.
        - move=> /=.
          case: ifP => dA.
            case eB: expand => //[s1' B'|s1' B'][_<-]; rewrite eqxx same_structure_id (HB _ _ eB)//.
          case eA: expand => //[s1' A'|s1' A'][_<-]; rewrite eqxx (HA _ _ eA)?same_structure_id// same_structure_cutr//same_structure_id//.
        - move=> /=; case: ifP => dA; case: expand => //.
        - move=> /simpl_expand_or_fail [].
            by move=>[A'[_[HA'->]]]/=; rewrite eqxx (HA _ _ HA') same_structure_id.
          by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
        - move=> /simpl_expand_or_solved[].
            by move=>[A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
          by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
      move=> A HA B0 HB0 B HB s1 [s2|s2||s2]C.
      - move=> /simpl_expand_and_expanded[].
          by move=>[A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        by move=> [s'[A'[B' [HA'[HB' ->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
      - move=> /simpl_expand_and_cut[].
          by move=>[A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        move=>[s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite (HB _ _ HB')//(same_structure_cut same_structure_id).
        by have:= (HA _ _ HA') => /same_structure_cut->.
      - move=> /simpl_expand_and_fail[].
          by move=> [A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        by move=> [s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
      - by move=> /simpl_expand_and_solved [s'[A'[B'[HA'[HB'->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
    Qed.

    Lemma expandedb_same_structure {s A r b}: 
      expandedb s A r b -> same_structure A (get_state_exp r).
    Proof.
      move=> H; elim: H; clear => /=.
      + move=> s1 s2 A B.
        apply: expand_same_structure.
      + move=> ???; apply: expand_same_structure.
      + move=> ??????/expand_same_structure/= + _.
        apply: same_structure_trans.
      + move=> ??????/expand_same_structure/= + _.
        apply: same_structure_trans.
    Qed.

    Lemma same_structure_clean_success {A}:
      same_structure A (clean_success A).
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=; case: ifP => //_; rewrite ?HA?HB same_structure_id eqxx//.
      - move=> A HA B0 _ B HB/=; case: ifP => _; rewrite !same_structure_id//?HA//.
    Qed.
  End same_structure.
End main.
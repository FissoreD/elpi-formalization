From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Module Language.
  Inductive D := Func | Pred.
  Inductive B := Exp | d of D.
  Inductive mode := i |o.
  Inductive S :=  b of B | arr of mode & S & S.
  Notation "x '--i-->' y" := (arr i x y) (at level 3).
  Notation "x '--o-->' y" := (arr o x y) (at level 3).

  Definition P := nat.
  derive P.
  Elpi derive.eqbOK.register_axiom P is_P is_nat_inhab P_eqb P_eqb_correct P_eqb_refl.

  Definition K := nat.
  derive K.
  Elpi derive.eqbOK.register_axiom K is_K is_nat_inhab K_eqb K_eqb_correct K_eqb_refl.

  Definition V := nat.
  derive V.
  Elpi derive.eqbOK.register_axiom V is_V is_nat_inhab V_eqb V_eqb_correct V_eqb_refl.

  Inductive C := 
    | p of P 
    | v of V
    .
  derive C.

  Inductive Tm := 
    | Code : C -> Tm
    | Data : K -> Tm
    | Comb : Tm -> Tm -> Tm.
    (* | Lam  : V -> S -> Tm -> S -> Tm. *)
  derive Tm.

  Record R_ {A} := mkR { head : Tm; premises : list A }.
  Arguments mkR {_} _ _.
  derive R_.
  Inductive A :=
    | Cut
    | Call : Tm -> A.
  derive A.

    (* | PiImpl : V -> R_ A -> A -> A. *)
  Notation R := (@R_ A).

  HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build C C_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build P P_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build K K_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.
  HB.instance Definition _ := hasDecEq.Build R (R__eqb_OK _ _ A_eqb_OK).

  Record Sigma := { sigma : V -> option Tm }.
  Definition empty : Sigma := {| sigma := fun _ => None |}.

  Definition index := list R.
  Definition mode_ctx := Tm -> list mode.
  Definition sigT := P -> S.
  (* 
    The predicate knows about the signature of all predicates, therefore,
    for each predicate we return a S (not an option S)
  *)
  Record program := { (*depth : nat;*) rules : index; modes : mode_ctx; sig : sigT }.
End Language.

Module Type Unif.
  Import Language.
  Parameter unify : Tm -> Tm -> Sigma -> option Sigma.
  Parameter matching : Tm -> Tm -> Sigma -> option Sigma.

  Parameter program_eqb : program -> program -> bool.
  Parameter is_program : program -> Type.
  Parameter is_program_inhab : forall p : program, is_program p.
  Parameter program_eqb_correct : forall p1 p2, program_eqb p1 p2 -> p1 = p2.
  Parameter program_eqb_refl : forall x, program_eqb x x.


  Parameter Sigma_eqb : Sigma -> Sigma -> bool.
  Parameter is_Sigma : Sigma -> Type.
  Parameter is_Sigma_inhab : forall p : Sigma, is_Sigma p.
  Parameter Sigma_eqb_correct : forall p1 p2, Sigma_eqb p1 p2 -> p1 = p2.
  Parameter Sigma_eqb_refl : forall x, Sigma_eqb x x.


  Parameter same_subst : forall (s1 s2 : Sigma), s1 = s2.
  Parameter same_progr : forall (s1 s2 : program), s1 = s2.
End Unif.

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


  Elpi derive.eqbOK.register_axiom program U.is_program U.is_program_inhab U.program_eqb U.program_eqb_correct U.program_eqb_refl.
  Lemma program_eqb_OK : Equality.axiom U.program_eqb.
  apply: iffP2 U.program_eqb_correct U.program_eqb_refl.
  Qed.
  HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.
  
  Elpi derive.eqbOK.register_axiom Sigma U.is_Sigma U.is_Sigma_inhab U.Sigma_eqb U.Sigma_eqb_correct U.Sigma_eqb_refl.
  Lemma Sigma_eqb_OK : Equality.axiom U.Sigma_eqb.
  apply: iffP2 U.Sigma_eqb_correct U.Sigma_eqb_refl.
  Qed.
  HB.instance Definition _ : hasDecEq Sigma := hasDecEq.Build Sigma Sigma_eqb_OK.

  Inductive state :=
    | KO : state
    | OK : state
    | Top : state
    | Bot : state
    | Dead : state
    (* | CutOut : state *)
    | Goal : program  -> A -> state
    | Or  : state -> Sigma -> state -> state               (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
    | And : state -> state -> state -> state  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
    .
  derive state.
  HB.instance Definition _ := hasDecEq.Build state state_eqb_OK.

  Definition is_and s := match s with And _ _ _ => true | _ => false end.
  Definition is_or s  := match s with Or _ _ _ => true | _ => false end.
  Definition is_cut A := match A with Goal _ Cut => true | _ => false end.

  (* Notation "A ∧ B" := (And A B) (at level 13000).
  Notation "A ∨ B" := (Or A B) (at level 13000). *)

  Inductive expand_res :=
    | Expanded    of Sigma & state
    | CutBrothers of Sigma & state
    | Failure     of state
    | Solved      of Sigma & state.
  derive expand_res.
  HB.instance Definition _ := hasDecEq.Build expand_res expand_res_eqb_OK.

  Fixpoint dead A :=
  match A with
  | Dead => Dead
  | OK | KO | Bot | Goal _ _ | Top => Dead
  | And A B0 B => And (dead A) (dead B0) (dead B)
  | Or A s B => Or (dead A) s (dead B)
  end.

  Lemma dead_dead_same {A}: dead (dead A) = dead A.
  Proof.
    elim: A => //.
    by move=> A HA s B HB /=; rewrite HA HB.
    by move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0.
  Qed.

  Definition mkOr A sB r :=
    match r with
    | Failure B       => Failure     (Or A sB B)
    | Expanded s B    => Expanded s  (Or A sB B)
    | CutBrothers s B => Expanded s  (Or A sB B)
    | Solved s B      => Solved   s  (Or A sB B)
    end.

  Fixpoint cutr A :=
    (* if A == dead A then Dead else *)
    match A with
    | Bot | Goal _ _ | Top | OK => KO
    | Dead | KO => A
    | And A B0 B => And (cutr A) (cutr B0) (cutr B)
    | Or A s B => Or (cutr A) s (cutr B)
    end.

   Fixpoint success (A : state) : bool :=
    match A with
    | OK => true
    | Top | Bot | Goal _ _ | KO | Dead => false
    | And A _ B => success A && success B
    | Or A _ B => if A == dead A  then success B else success A
    end.


    (* Maybe replace all cutout with bot, and remove the cutout constructor *)
  Fixpoint cutl A :=
    (* if A == dead A then Dead else *)
    match A with
    | Bot | Goal _ _ | Top => KO
    | Dead | KO | OK => A
    | And A B0 B => And (cutl A) (cutl B0) (cutl B)
    | Or A s B => 
        if A == dead A then Or A s (cutl B)
        else  Or (cutl A) s (cutr B)
         (* Or (cutl A) s (if success A then cutr B else cutl B) *)
    end.


  Definition mkAnd A B0 r :=
    match r with
    | Failure B       => Failure       (And A B0 B)
    | Expanded s B    => Expanded    s (And A B0 B)
    | CutBrothers s B => CutBrothers s (And (cutl A) B0 B)
    | Solved s B      => Solved      s (And A B0 B)
    end.

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

  Definition get_state r := match r with 
    | Failure A | Solved _ A | CutBrothers _ A | Expanded _ A => A 
  end.


  Fixpoint expand s A : expand_res :=
    match A with
    (* meta *)
    | OK => Solved s OK
    | KO => Failure KO

    (* meta *)
    | Dead => Failure Dead
    
    (* lang *)
    | Top              => Expanded s OK
    | Bot              => Expanded s KO
    | Goal _ Cut       => CutBrothers s OK
    | Goal pr (Call t) => Expanded s (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        if A == dead A then mkOr A sB (expand s B)
        else
        match expand s A with
        | Solved s A    => Solved s      (Or A sB B)
        | Expanded s A    => Expanded s  (Or A sB B)
        | CutBrothers s A => Expanded s  (Or A sB (cutr B))
        | Failure A     => Failure       (Or A sB B)
        end
    | And A B0 B =>
        match expand s A with
        | Solved s1 A     => mkAnd    A B0  (expand s1 B)
        | Expanded s A    => Expanded s     (And A B0 B)
        | CutBrothers s A => CutBrothers s  (And A B0 B)
        | Failure A       => Failure        (And A B0 B)
        end
    end
  .


  Fixpoint failed (A : state) : bool :=
    match A with
    | KO | Dead => true
    | Top | Bot | Goal _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    | Or A _ B => if A == dead A then failed B else failed A (*&& failed B*)
    end.

  Lemma failed_success A: failed A -> success A = false.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; case: eqP => [_ /HB| _ /HA].
    + by move=> A HA B0 _ B HB /= /orP [/HA|/andP [-> /HB]] ->.
  Qed.

  Lemma success_failed A: success A -> failed A = false.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; case: eqP => [_ /HB| _ /HA].
    + by move=> A HA B0 _ B HB /= /andP[] /[dup] /HA -> ->/HB ->.
  Qed.

  Lemma dead_failed {A} : A = dead A -> failed A.
  Proof. elim: A => //.
    + by move=> A HA s B HB /= [] /HA -> /HB -> ; rewrite if_same.
    + by move=> A HA B0 HB0 B HB /= [] /HA ->.
  Qed.

  Lemma failed_dead {A} : failed A = false -> A <> dead A.
  Proof. elim: A => //.
    + move=> A HA s B HB /=; case: eqP.
      + move=> <- /HB H [] //.
      + move=> H _ [] //.
    + move=> A HA B0 HB0 B HB /= /orP H [] H1 H2 H3.
      apply: H.
      by left; apply: dead_failed H1.
  Qed.

  Definition is_base X := match X with Top | Bot | Goal _ _ => true | _ => false end.
  Definition is_expanded X := match X with Expanded _ _ => true | _ => false end.


  Fixpoint next_alt (s : Sigma) (A : state) : option (Sigma * state) :=
    match A with
    | KO | OK => None
    | Dead => None
    | Top | Bot | Goal _ _ => None
    | And A B0 B =>
      if (A == dead A) then None else
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
      if A == dead A then
        match next_alt s B with
        | None => None
        | Some (sB1, B) => Some (sB1, Or A sB B)
        end
      else
        (* if B == dead B then None else *)
        match next_alt s A with
        | None =>  
            if failed B then 
              match next_alt sB B with
              | None => None
              | Some (sB1, B) => Some (sB1, Or (dead A) sB B)
              end
            else if B == dead B then None else Some (sB, Or (dead A) sB B)
        | Some (sA, A) => Some (sA, Or A sB B)
        end
    end.

  Lemma next_alt_dead {A D s1 s2}: 
    next_alt s1 A = Some (s2, D) -> A <> dead A /\ D <> dead D.
  Proof.
    elim: A D s1 s2 => //.
      move=> A HA s B HB C s1 s2/=.
      case: ifP => /eqP/=.
        move=>->.
        case X: next_alt => //[[s3 D]].
        have [??]:= HB _ _ _ X.
        move=> []??;subst => /=; rewrite dead_dead_same; split; congruence.
      have:= (HA _ s1).
      case: next_alt => //= [[s3 D]|].
        move=> /(_ _ _ erefl) []?? _ []??;subst => /=; split; congruence.
      move=> _ dA.
      case: ifP => //fB.
        have:= HB _ s.
        case: next_alt => //[[s3 D]] /(_ _ _ erefl) []?? []??;subst => /=.
        split; congruence.
      case: ifP => ///eqP H [??]; subst => /=; rewrite dead_dead_same; split; congruence.
    move=> A HA B0 _ B HB C s1 s2 /=.
    have:= HB _ s1.
    case: next_alt => //[[s3 D]|].
      move=> /(_ _ _ erefl) dD; case: ifP => //.
      case: eqP => // dA _.
      case: ifP => // fA.
        have:= HA _ s1.
        case: next_alt => //[[s4 E]].
        move=> /(_ _ _ erefl) []??.
        by case:ifP => // _[]??;subst; split => /=; congruence.
      by move=> []??;subst; split => /=-[].
    move=> _; case: ifP => //.
    case:eqP => //; move=> dA _.
    have:= HA _ s1.
    case: next_alt => //[[s3 D]|].
      move=> /(_ _ _ erefl) []??.
      case: ifP => //fA.
        case: ifP => // ? []??;subst => /=; split; congruence.
      case: ifP => // fB0.
      by move=> []??;subst; split => -[].
    case: ifP => //.
  Qed.

  Lemma next_alt_failed {s A s1 B}:
    next_alt s A = Some (s1, B) -> failed B = false.
  Proof.
    elim: A B s s1 => //.
      move=> A HA s B HB C s1 s2/=.
      case: ifP => /eqP.
        move=>->; case X: next_alt => //[[s3 D]].
        move=> []??;subst => /=; rewrite dead_dead_same eqxx.
        apply: HB X.
      have:= HA _ s1.
      case X: next_alt => // [[s3 D]|].
        move=>/(_ _ _ erefl) fD dA.
        move=>[]??;subst => /=.
        rewrite fD.
        have [_ +] := next_alt_dead X.
        by case: ifP => /eqP //.
      move=> _ dA.
      case: ifP => // fB.
        have:= (HB _ s).
        case Y: next_alt => [[s3 D]|]//.
        move=> /(_ _ _ erefl) fD []?? ;subst => /=.
        by rewrite dead_dead_same eqxx.
      by case: ifP => //dB [??]; subst => /=; rewrite dead_dead_same eqxx.
    move=> A HA B0 _ B HB C s1 s2.
    move=> /=.
    case: ifP => /eqP//dA.
    case: ifP => // fA.
      have:= HA _ s1.
      case X: next_alt => //[[s3 D]].
      move=> /(_ _ _ erefl) fD.
      case: ifP => // fB0.
      move=> []??; subst => /=; rewrite fD.
      by rewrite fB0 andbF.
    have:= HB _ s1.
    case: next_alt => //[[s4 E]|].
      move=>/(_ _ _ erefl) fE []??;subst => /=.
      by rewrite fA fE andbF.
    move=> _.
    have:= HA _ s1.
    case X: next_alt => //[[s3 D]].
    move=> /(_ _ _ erefl) fD.
    case: ifP => // fB0.
    move=> []??; subst => /=; rewrite fD.
    by rewrite fB0 andbF.
  Qed.

  Lemma next_alt_dead1 {s A}: next_alt s (dead A) = None.
  Proof.
    elim: A => //.
      move=> A HA s1 B HB => /=.
      rewrite dead_dead_same eqxx.
      by rewrite HB.
    move=> A HA B0 _ B HB /=.
    by rewrite dead_dead_same eqxx.
  Qed.

  Lemma cutr_dead1 {A}: cutr A = dead A -> dead A = A.
  Proof. 
    elim: A=> //.
      move=> A HA s B HB/=[]??; rewrite HA//HB//.
    move=> A HA B0 HB0 B HB/=[]???; rewrite HA//HB//HB0//.
  Qed.

  Lemma dead_cutr_is_dead {A}: dead(cutr A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0.
  Qed.  
  
  Lemma failed_cutr {A}: failed (cutr A) = true.
  Proof.
    elim: A => //.
      move=> A HA s B HB /=.
      by rewrite HA HB if_same.
    move=> A HA B0 _ B HB /=.
    by rewrite HA.
  Qed.

  Lemma next_alt_cutr {s A}: next_alt s (cutr A) = None.
  Proof.
    elim: A s => //.
      move=> A HA s1 B HB s2 /=.
      by rewrite HA failed_cutr !HB if_same.
    move=> A HA B0 _ B HB /= s1.
    by rewrite failed_cutr HA if_same.
  Qed.

  Lemma next_alt_or_some {s B s' C y}:
    next_alt s B = Some (s', C) ->  y <> dead y -> forall x, next_alt s (Or B x y) = Some (s', Or C x y).
  Proof.
    move=> /= H dy x.
    have [dB dC] := next_alt_dead H.
    do 2 case: ifP => /eqP// _; by rewrite H.
  Qed.

  (* Lemma next_alt2 {s s1 A B}: next_alt s A = Some (s1, B) -> forall s2, isSome (next_alt s2 B).
  Proof.
    Falso!
  Qed. *)
  

  Definition has_next_alt s := isSome (next_alt empty s).

  Lemma cut_dead1 {A}: cutl A = dead A -> A = dead A.
  Proof. 
    elim: A=> //.
      move=> A HA s B HB/=.
      case: ifP => /eqP.
        by move=><-[]/HB<-.
      by move=> dA []/HA<- /cutr_dead1->.
    move=> A HA B0 HB0 B HB/=[] H H2 H3; rewrite -HA//-HB//-HB0//.
  Qed.

  Inductive run_res := Done of Sigma & state | Failed of state.
  derive run_res.
  HB.instance Definition _ := hasDecEq.Build run_res run_res_eqb_OK.

  Definition get_state_run r := match r with Done _ s => s | Failed s => s end.
  Definition is_fail A := match A with Failure _ => true | _ => false end.
  Definition is_failed A := match A with Failed _ => true | _ => false end.
  Definition is_done A := match A with Done _ _ => true | _ => false end.

  Inductive expandedb : Sigma -> state -> run_res -> bool -> Prop :=
    | expanded_done {s s' A alt}     : expand s A = Solved s' alt  -> expandedb s A (Done s' alt) false
    | expanded_fail {s A B}          : expand s A = Failure B -> expandedb s A (Failed B) false
    | expanded_cut {s s' r A B b}      : expand s A = CutBrothers s' B -> expandedb s' B r b -> expandedb s A r true
    | expanded_step {s s' r A B b}     : expand s A = Expanded s' B  -> expandedb s' B r b -> expandedb s A r b.

  Inductive runb : Sigma -> state -> run_res -> bool -> Prop :=
    | run_done {s s' A B b}        : expandedb s A (Done s' B) b -> runb s A (Done s' B) b
    | run_fail {s A B b}           : expandedb s A (Failed B) b -> next_alt s B = None -> runb s A (Failed B) b
    | run_backtrack {s s' s'' A B C b1 b2 b3} : expandedb s A (Failed B) b1 -> next_alt s B = (Some (s', C)) ->  runb s' C s'' b2 -> b3 = (b1 || b2) -> runb s A s'' b3.

  Definition expanded s A r := exists b, expandedb s A r b.
  Definition run s A r := exists b, runb s A r b.

  Definition run_classic s A r := runb s A r false. 
  Definition expanded_classic s A r := expandedb s A r false. 

  Lemma simpl_expand_or_solved {s s1 s2 A B C} :
    expand s1 (Or A s B) = Solved s2 C ->
      (exists A', expand s1 A = Solved s2 A' /\ C = Or A' s B) \/
      (exists B', A = dead A /\ expand s1 B = Solved s2 B' /\ C = Or A s B').
  Proof.
    move=> //=.
    case: ifP => /eqP.
      move=>->.
      unfold mkOr.
      case X: expand => //-[]*;subst.
      right; do 2 eexists; repeat split.
      by rewrite dead_dead_same.
    move=> _; case Y: expand => //=-[]??;subst.
    by left; eexists.
  Qed.

  Lemma simpl_expand_or_cut {s s1 s2 A B C} :
    expand s1 (Or A s B) = CutBrothers s2 C -> 
      exists B', A = dead A /\ expand s1 B = CutBrothers s2 B' /\ C = Or A s B'.
  Proof.
    move=>/=; case: ifP => [/eqP->|/eqP DA].
      case X:expand => //=-[]*;subst; do 2 eexists; repeat split.
      (* by rewrite dead_dead_same. *)
    case X:expand => //.
  Qed.

  Lemma dead_big_or p s t: dead (big_or p s t) <> big_or p s t.
  Proof.
    rewrite /big_or; case F: F => // [[s1 r] xs] //.
  Qed. 

  Lemma simpl_expand_or_fail {s s1 A B C} :
    expand s1 (Or A s B) = Failure C -> 
      (exists A', A <> dead A /\ expand s1 A = Failure A' /\ C = Or A' s B) \/
      (exists B', A = dead A /\ expand s1 B = Failure B' /\ C = Or A s B').
  Proof.
    move=>/=; case: ifP => [/eqP->|/eqP DA];subst.
      rewrite /mkOr. 
      case X: expand => //= [D][]?;subst.
      by right; eexists; repeat split; rewrite dead_dead_same.
    case X: expand => // => -[]?;subst.
    by left; eexists; repeat split.
  Qed.

  Lemma simpl_expand_or_expanded {s s1 s2 A B C} :
    expand s1 (Or A s B) = Expanded s2 C ->
      (exists A', A <> dead A /\ expand s1 A = Expanded s2 A' /\ C = Or A' s B ) \/ 
      (exists A', A <> dead A /\ expand s1 A = CutBrothers s2 A' /\ C = Or A' s (cutr B)) \/
      (A = dead A /\ (exists B', (expand s1 B = Expanded s2 B' \/ expand s1 B = CutBrothers s2 B') /\ C = Or A s B')).
  Proof.
    move=>/=; case: ifP => /eqP.
      move=>->.
      case X: expand => //=.
        move=>[]??;subst; right; right; rewrite dead_dead_same; split => //.
        eexists; repeat split; auto.
      move=>[]??;subst; right; right; rewrite dead_dead_same; split => //.
      eexists; repeat split; auto.
    move=> H.
    case X: expand => //=-[]??;subst.
      by left; eexists; repeat split.
    by right; left; eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_solved {s s2 A B0 B C} :
    expand s (And A B0 B) = Solved s2 C -> 
      exists s' A' B', 
        expand s A = Solved s' A' /\
          expand s' B = Solved s2 B' /\ C = And A' B0 B'.
  Proof.
    move=> //=; case X: expand => //.
    case Y: expand => // [s'' B'].
    move=> [] /[subst1] /[subst1].
    by do 3 eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_fail {s A B B0 C} :
    expand s (And A B0 B) = Failure C ->
      (exists A', expand s A = Failure A' /\ C = And A' B0 B) \/ 
        (exists s' A' B', expand s A = Solved s' A' /\  
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
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = CutBrothers s2 B' /\ C = And (cutl A') B0 B').
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
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = Expanded s2 B' /\ C = And A' B0 B').
  Proof.
    move=> /=; case X: expand => //=.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right; subst.
      do 3 eexists; repeat split => //=; eassumption.
  Qed.

  (* Lemma expand_solved_ok {s1 s2 A}:
    expand s1 A = Solved s2 OK -> False.
  Proof.
    elim: A s1 s2 => //.
    + by move=> pr [] ?? //= ?; case: F => //= [[] xs] //=.
    + move=> A IHA s B IHB s1 s2 /simpl_expand_or_solved [].
      + by move=> [] A' [] B' [IHA' [IHB']].
      + by move=> [A' [H]].
    + by move=> A IHA B IHB s1 s2 /simpl_expand_and_solved [s' [A' [B' [H1 [H2]]]]].
  Qed. *)

  (* Lemma cut_dead {A}: cutl A = dead (cutl A) -> dead A = A.
  Proof.
    elim: A=> //.
    + move=> A HA s B HB /=; case X: eq_op => /=.
      + by move: X => /eqP [] -> -> _; rewrite !dead_dead_same.
      + move=> [] /HA {}HA /HB {}HB; congruence.
    + move=> A HA B0 HB0 B HB /=; case X: eq_op => /=.
      + by move: X => /eqP [] <-.
      + by move=> [] /HA ->.
  Qed. *)


  Lemma success_dead {A}: success (dead A) = false.
  Proof. 
    elim: A=> //. 
      by move=> A HA s B HB /=; rewrite HA HB if_same.
    by move=> A HA B0 ? B HB/=; rewrite HA ?HB.
  Qed.

  Lemma cut_dead_is_dead {A}: cutl(dead A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA dead_dead_same eqxx HB.
    + move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0//.
  Qed.

  Lemma cutr_dead_is_dead {A}: cutr(dead A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0.
  Qed.

  Lemma dead_cut_is_dead {A}: dead(cutl A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite fun_if/= HA HB //dead_cutr_is_dead// if_same.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0.
  Qed.

  Definition is_meta X := match X with OK | KO | Dead => true | _ => false end.

  (* Lemma simpl_next_alt_false {s1 s2 A B r}: 
    next_alt false s1 (Or A s2 B) = Some r -> 
      (is_meta A /\ r = (s2, Or Dead s2 B)) \/ (is_base A /\ r = (s1, Or A s2 B)) \/
      (A = And X Y0 Y /\).
  Proof.
    case X: A ; try by move=> // [] /[subst1]; left.
    + move=> [] ?/[subst]; right => //. 
    + move=> [] ?/[subst]; right => //.
    + move=> [] ?/[subst]; right => //.
    + move=> /=; case Y: next_alt; admit.
    + move=> /=; case Y: next_alt => [[ ]|].
      + move=> [] ?.  *)

  Lemma simpl_is_base {B}: is_base B -> B = Top \/ B = Bot \/ (exists p t, B = Goal p t).
  Proof. by case B => //=; auto; right; right; do 2 eexists. Qed.

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
    (* + by move=> ??[]/=. *)
    + move=> A HA s B HB s1 s2 /=.
      case:ifP => /eqP.
        move=>->.
        have:= HB s1 s2.
        case: next_alt => //[[s5 E]|]; case: next_alt => //[[s6 F]].
        by move=> /=/eqP->.
      have:= HA s1 s2.
      case NA: next_alt => [[s3 C]|].
        by case: next_alt => // [[s4 D]]/eqP->/=; rewrite eqxx.
      case: next_alt => // _.
      case: ifP => //.
        by case: next_alt => //[[??]]//=.
      by move=> _ _; case: ifP => //=.
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

  (* Lemma simpl_next_alt_some {b s s1 s2 A B C}: next_alt b s1 (Or A s B) = Some (s2, C) -> 
    (exists B', A = dead A /\ next_alt false s1 B = Some (s2, B') /\ C = Or A s B') \/
    (A <> dead A /\ B <> dead B /\ 
      ((exists A', next_alt false s1 A = Some (s2, A') /\ C = Or A' s B) \/
      (next_alt false s1 A = None /\ C = Or (dead A) s B))).
  Proof.
    move=> //=.
    case:ifP => /eqP.
      move=>->.
      case: next_alt => // [[s3 D]].
      case:ifP => /eqP// dD []??;subst.
      by rewrite dead_dead_same; left; eexists.
    move=> dA; case: ifP => ///eqP dB.
    case X: next_alt => [[s3 D] |]-[]*;subst.
      right; repeat split => //.
      left; eexists => //.
    right; repeat split => //.
    by right.
  Qed. *)


  Lemma success_dead1 {A}: success A -> A <> dead A.
  Proof.
    move=> + H.
    by rewrite H success_dead.
  Qed.

  Definition is_cutbrothers X := match X with CutBrothers _ _ => true | _ => false end.
 
  Lemma get_state_And A B0 B : get_state (mkAnd A B0 B) = And (if is_cutbrothers B then cutl A else A) B0 (get_state B).
  Proof. by case: B. Qed.

  Lemma get_state_Or A s B : get_state (mkOr A s B) = Or A s (get_state B).
  Proof. by case: B. Qed.


  Lemma expand_dead {s A}: 
    A = dead A -> expand s A = Failure A.
  Proof.
    move=> ->.
    elim: A s => //.
    + move=> A HA s B HB s1 => //=.
      by rewrite dead_dead_same eqxx HB /=.
    + move=> A HA B0 _ B HB s1 /=.
      by rewrite HA.
  Qed.

  Lemma expand_not_dead {s A r}: 
    A <> dead A -> expand s A = r -> get_state r <> dead (get_state r).
  Proof.
    move=> + <-.
    elim: A s; clear; try by move=> //=.
    + move=> p [|t]//= s _ /esym; apply dead_big_or.
    + move=> A HA s B HB s1 => //=.
      case: ifP => /eqP.
        move=>->/=.
        rewrite dead_dead_same.
        move=> H; have {}H: B <> dead B by congruence.
        have:= HB s1 H.
        case X: expand => //=?; rewrite dead_dead_same; congruence.
      move=> dA _.
      have:= HA s1 dA.
      case X: expand => //=?;subst; congruence.
    + move=> A HA B0 _ B HB s1 //= H.
      have:= HA s1.
      case X: expand => [|||s A']/=; last first; [|move=> {}HA[H1 H2 H3]; (have: A <> dead A by congruence); move=>/HA//..].
      case: (A =P dead A) => dA.
        rewrite expand_dead in X => //.
      move=> /(_ dA) dA'.
      case: expand => //=[_|_||_]B'[]//.
      by rewrite dead_cut_is_dead => /cut_dead1.
  Qed.

  Lemma expand_not_deadb {s A r}: 
    A == dead A = false -> expand s A = r -> get_state r == dead (get_state r) = false.
  Proof.
    move=>/eqP H1 H2.
    case: eqP => //= H3.
    by have:= expand_not_dead H1 H2 H3.
  Qed.

  Lemma expanded_not_dead {s A r b}: 
    A <> dead A -> expandedb s A r b -> get_state_run r <> dead (get_state_run r).
  Proof.
    move=> + H.
    elim: H; clear.
    + move=> s s' A A' H1 H2 /=; apply: expand_not_dead H2 H1.
    + move=> s A B H1 H2 /=; apply: expand_not_dead H2 H1.
    + move=> s s' r A A' b H _ IH dA; apply: IH (expand_not_dead dA H).
    + move=> s s' r A A' b H _ IH dA; apply: IH (expand_not_dead dA H).
  Qed.

  Lemma expanded_dead s {A}: 
    A = dead A -> expandedb s A (Failed A) false.
  Proof.
    move=> ->.
    case: A s; try by move=>?; apply: expanded_fail.
    + try by move=>??; apply: expanded_fail.
    + by move=> /= _ _ s; apply expanded_fail.
    + all: move=> *; apply: expanded_fail;
      rewrite /= expand_dead//!dead_dead_same//eqxx//.
  Qed.

  Lemma succes_is_solved s {A}: success A -> expand s A = Solved s A.
  Proof.
    elim: A s => //; try by do 2 eexists.
    + move=> A HA s1 B HB s /=.
        (* move=>[-> vB]/=.
        rewrite dead_dead_same eqxx.
        move=>sB.
        by have H := HB s vB sB; rewrite H. *)
      (* move=>[dA[vA bB]]/=. *)
      case:ifP => /eqP// H sA.
        rewrite (HB s)//.
      rewrite (HA s)//.
    + move=> A HA B0 HB0 B HB s /=.
      move=>/andP[sA sB].
      rewrite (HA s)// (HB s)//.
  Qed.

  Lemma expand_solved_success {s1 A s2 B}: 
    expand s1 A = Solved s2 B -> success A /\ success B.
  Proof.
    elim: A s1 s2 B => //.
    + by move=> /= ??? [] /[subst2].
    + move=> ? [] //.
    + move=> A HA s B HB s1 s2 C/=.
      case: ifP => /eqP dA.
        case X: expand =>//-[??];subst => /=.
        rewrite dA dead_dead_same eqxx.
        by have := HB _ _ _ X.
      have:= HA s1; case: expand => //.
      move=> D E /(_ _ _ erefl)[->] sE [??]; subst => /=.
      rewrite sE.
      move: sE.
      by case: ifP => /eqP//->; rewrite success_dead.
    + move=> A HA ? _ B HB s1 s2 C /=.
      have:= HA s1.
      case: expand => // s D /(_ _ _ erefl)[]->.
      have:= HB s.
      case: expand => // s3 E /(_ _ _ erefl)[]->.
      by move=> sE sD [??]; subst => /=; rewrite sE sD.
  Qed.

  Lemma expand_solved_failed {s1 A s2 B}: 
    expand s1 A = Solved s2 B -> failed A = false /\ failed B = false.
  Proof.
    move=>/expand_solved_success [].
    by do 2 move=> /success_failed->.
  Qed.

  Lemma expand_failure_failed {s1 A B}:
    expand s1 A = Failure B -> failed A /\ failed B.
  Proof.
    elim: A s1 B; clear => //; try by move=> ? [] //.
    + move=> A HA s1 B HB s2 C.
      move=>/simpl_expand_or_fail[].
        move=>[A'[dA[HA' ->]]] /=.
        move: (dA) => /eqP/negbTE->.
        have /=/eqP/negbTE-> := expand_not_dead dA HA'.
        apply: HA HA'.
      move=> [B' [dA [HB' ->]]] /=-.
      by rewrite -dA eqxx; apply: HB HB'.
    + move=> A HA B0 _ B HB s C.
      move=> /simpl_expand_and_fail[].
        move=> [A' [HA'->]]/=.
        by have:= HA _ _ HA'=>-[]-> //->.
      move=> [s' [A' [B' [HA' [HB' ->]]]]]/=.
      have:= HB _ _ HB' => -[]->->.
      have:= expand_solved_success HA' => -[] ->->.
      by rewrite !orbT.
  Qed. 

  Lemma success_cutr {A} : success (cutr A) = false.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      rewrite dead_cutr_is_dead.
      case:ifP=>/eqP //.
    + move=> A HA B HB C HC /=.
      by rewrite HA ?HC.
  Qed.

  Lemma success_cut {A} : success (cutl A) = success A.
  Proof.
    elim: A => //. 
    + move=> A HA s B HB /=.
      rewrite (fun_if (success))/= HA HB success_cutr.
      do 2 case: ifP => //.
      by move=>/eqP; rewrite dead_cut_is_dead => /cut_dead1<-; rewrite eqxx.
    + move=> A HA B HB C HC /=.
      by rewrite HA ?HC.
  Qed.

  Lemma success_cut1 {A} : success A -> success (cutl A).
  Proof. by rewrite success_cut. Qed.

  Lemma failed_dead1 {A}: failed (dead A).
  Proof.
    elim: A => //.
      by move=>A HA s B HB/=; rewrite dead_dead_same eqxx.
    move=> A HA B0 _ B HB/=.
    by rewrite HA.
  Qed.

  Lemma cutr2_same {a}: cutr (cutr a) = cutr a.
  Proof.
    elim: a => //=.
    + move=> A HA s B HB.
      by move=> /=; rewrite HA HB.
    + move=> A HA B0 HB0 B HB.
      by move=> /=; rewrite HA ?HB0 ?HB.
  Qed.



  Lemma cutr_cutl_is_cutr A: cutr (cutl A) = cutr A.
  Proof.
    elim: A => //.
      by move=> A HA s B HB /=; rewrite fun_if/=HA HB cutr2_same if_same.
    by move=> A HA B0 HB0 B HB /=; rewrite HA HB0 HB.
  Qed.

    Lemma cutl_cutr_is_cutr A: cutl (cutr A) = cutr A.
  Proof.
    elim: A => //.
      by move=> A HA s B HB /=; case: ifP; rewrite ?cutr2_same ?HA ?HB.
    by move=> A HA B0 HB0 B HB /=; rewrite HA HB HB0.
  Qed.

  Lemma cut_cut_same {a}: cutl (cutl a) = cutl a.
  Proof.
    elim: a => //=.
    + move=> A HA s B HB.
      rewrite (fun_if cutl)/= HA HB !cutr_cutl_is_cutr cutl_cutr_is_cutr cutr2_same if_same.
      by case: ifP => ///eqP->; rewrite dead_dead_same eqxx.
    + move=> A HA B0 HB0 B HB.
      by move=> /=; rewrite HA ?HB0 ?HB.
  Qed.


  Lemma big_or_failed {p s1 t}: failed (big_or p s1 t) = false.
  Proof.
    unfold big_or.
      case: F => //.
    move=> [s r] l.
    by move=>/=.
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
    rewrite success_cut.
    by move=>/andP[->/HB->]; rewrite orbT.
  Qed.

  Lemma big_and_dead {p l}: big_and p l = dead (big_and p l) -> False.
  Proof. elim l => //. Qed.

  Lemma big_and_cut {p l}: big_and p l = cutl (big_and p l) -> False.
  Proof. elim l => //. Qed.
End Run.
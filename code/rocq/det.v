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
  | Cut
  | Call : C -> A
  | App : A -> Tm -> A.
  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).

Definition Sigma := V -> option Tm.
Definition empty : Sigma := fun _ => None.

Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
Axiom matching : Tm -> Tm -> Sigma -> option Sigma.

Definition index := list R.
Definition mode_ctx := P -> list mode.
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx }.

Inductive goal_ alt := Goal of program & A & list alt.
Arguments Goal {_} _ _ _.
Inductive alt := Alt of Sigma & list (goal_ alt).
Notation goal := (goal_ alt).

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

Definition build_alt (pr: program) (gl:list goal) (alts:list alt) (s:Sigma) (r : R) : alt := 
  Alt s ([seq Goal pr x alts | x <- r.(premises)] ++ gl).  

Definition F pr pname args (gl:list goal) s (alts:list alt) :=
  let rules := pr.(rules) in
  let modes := pr.(modes) pname in
  let rules := select args modes rules s in
  let f := fun x => match x with (s,r)=> build_alt pr gl alts s r end in
  [seq f r | r <- rules].

(* Axiom F : program -> P -> list Tm -> list goal -> Sigma -> list alt -> list alt. *)

Definition stack := list Tm.

Inductive run : stack -> alt -> list alt -> option (list alt * Sigma) -> Prop :=
  | run_cut P s gl cta r _a :

      run [::] (Alt s gl) cta r
      (*--------------------------------------*) ->
      run [::] (Alt s (Goal P Cut cta :: gl)) _a r

  | run_top s a :

      (*------------------------------------*)
      run [::] (Alt s [::]) a (Some (a, s))

  | run_call s P pname args gl al a' al' r _a :

      F P pname args gl s al = a' :: al' ->
      run [::] a' al' r
      (*------------------------------------*) ->
      run args (Alt s (Goal P (Call (p pname)) _a :: gl)) al r

  | run_back s P pname args gl a al r _a :

      F P pname args gl s (a :: al) = [::] ->
      run [::] a al r
      (*----------------------------------------*) ->
      run args (Alt s (Goal P (Call (p pname)) _a :: gl)) (a :: al) r

  | run_fail s P pname args gl _a :

      F P pname args gl s [::] = [::] 
      (**********************************) ->
      run args (Alt s (Goal P (Call (p pname)) _a :: gl)) [::] None
 
  | run_sigma s P vname pname stack gl a al r :

      s vname = Some (Code (p pname)) -> (* TODO: Comb -> App *)
      run stack (Alt s (Goal P (Call (p pname)) a :: gl)) al r
      (**********************************) ->
      run stack (Alt s (Goal P (Call (v vname)) a :: gl)) al r

  | run_app s P arg atom stack gl a al r :
      run (rcons stack arg) (Alt s (Goal P atom a :: gl)) al r
      (**********************************) ->
      run stack (Alt s (Goal P (App atom arg) a :: gl)) al r
.

Axiom suffix : seq alt -> seq alt -> Prop.
Axiom suffix0 : forall a, suffix a [::].
Axiom valid : seq alt -> Prop.
Axiom append_alt : seq alt -> seq alt -> seq alt.
Axiom append_alt_ok : forall a a1, valid a -> valid a1 -> valid (append_alt a a1).
Axiom valid_run : forall a al a' s, valid (a :: al) -> run [::] a al (Some(a',s)) -> valid a'.

Inductive run1_outcome (s : Sigma) gl : goal -> list alt -> list alt -> Sigma -> Prop :=
| IsCut s'' cta P a' s' a'' :
    run [::] (Alt s'' gl) cta (Some(a',s')) ->
    run1_outcome s gl (Goal P Cut cta) a'' a'  s'
| Fails g a' s' a1 a2 :
    run [::] (Alt s [:: g]) [::] None ->
    run [::] a1 a2 (Some(a',s')) ->
      run1_outcome s gl g (a1::a2) a' s'
| NotCut g P cta a a' a'' s' s'' :
    ~ (g = Goal P Cut cta) ->
    run [::] (Alt s [:: g]) [::] (Some(a,s'')) ->
    run [::] (Alt s'' gl) (append_alt a a'') (Some(a',s')) ->
      run1_outcome s gl g a'' a' s'.


Lemma run1P s g gl a' a'' s' :
  valid ((Alt s (g :: gl)) :: a'') ->
  run [::] (Alt s (g :: gl)) a'' (Some(a',s')) ->
  run1_outcome s gl g a'' a' s'.
Proof.
(* case: g => p atom cta.
elim: atom.
  move=> H H1; apply: IsCut. inversion H1; subst. by eassumption.
  move=> [pn|vn] Hv H; inversion H; subst.
  have [[Hf [x[ax[def_a Hx]]]]|[_a Ha]] : (run [::] a'0 al' None /\ exists x ax,x :: ax = a /\ run [::] x ax (Some (a', s'))) \/
                                  (exists _a, run [::] a'0 al' (Some (_a, s'))).
    admit.
  admit.
  admit.
  admit.
  admit.
move=> atom IH arg Hv H; inversion H; subst.


move=> Valid H. 
remember (Alt _ _) as a eqn:Ha.
remember (Some _) as r eqn:Hr.
remember [::] as stk eqn:Hs.
elim: H Ha Hr Hs.
  move=> P s1 gl1 cta {}r _a Hr IH [? ? ? ? _]; subst; apply: IsCut; by eassumption.
  by [].
  move=> s1 P pn args gl1 a1 a2 a3 a4 {}r a5 Hf Hr IH [? ? ? ? ?]. subst.
inversion H; subst => {H}.
  apply: IsCut; by eassumption.
- admit.
- apply: Fails. apply: run_fail. admit. assumption.


 *)
Admitted.

Lemma run_cut_gl P cta s g gl a' a'' s' {stk}:
  run stk (Alt s (g :: gl)) a'' (Some(a',s')) ->
  g = Goal P Cut cta ->
  exists s'', run stk (Alt s'' gl) cta (Some(a',s')).
Proof. move=> H1 ?; subst; inversion H1; eexists; eassumption. Qed.

Lemma run_call_pn_empty P cta pn s g gl a' a'' s' stk :
  run stk (Alt s (g :: gl)) a'' (Some(a',s')) ->
  g = Goal P (Call (p pn)) cta ->
  F P pn stk gl s a'' = [::] ->
  exists x xs, x :: xs = a'' /\ run [::] x xs (Some(a',s')).
Proof.
  move=> H; inversion H; subst => {}H FP.
    by [].
    by injection H => ???; subst; rewrite H6 in FP.
    injection H => ???; subst; exists a, al; auto.
    by [].
    by [].
Qed.

Lemma run_call_pn_some P cta pn s g gl a a' s' stk x xs:
  run stk (Alt s (g :: gl)) a (Some(a',s')) ->
  g = Goal P (Call (p pn)) cta ->
  F P pn stk gl s a = x :: xs ->
  run [::] x xs (Some(a',s')).
Proof.
  move=> H; inversion H; subst => {}H FP; try by []; injection H => ???; subst.
    2: by rewrite H6 in FP.
    by rewrite H6 in FP; inversion FP; subst.
Qed.

Lemma run_var_gl P cta vname s g gl a' a'' s' stk :
  run stk (Alt s (g :: gl)) a'' (Some(a',s')) ->
  g = Goal P (Call (v vname)) cta ->
  exists x xs, 
    (x :: xs = a'' \/ (exists pn, s vname = Some (Code (p pn)) /\ F P pn stk gl s a'' = x :: xs)) 
      /\ run [::] x xs (Some(a',s')).
Proof. 
  move=> H1 ?; subst; inversion H1; subst.
  inversion H10; subst; do 2 eexists; split; auto.
  by right; eexists; split; eassumption.
  auto.
Qed.



(* Lemma run_x_y s g gl a' a'' s' :
  valid ((Alt s (g :: gl)) :: a'') ->
  run [::] (Alt s (g :: gl)) a'' (Some(a',s')) ->
  (exists P cta s'' a, g = Goal P Cut cta,
                 run [::] (Alt s'' gl) cta (Some(a',s')))
  \/
  (exists s'' a, (froall P cta, ~ (g = Goal P Cut cta)) /\
                 run [::] (Alt s [:: g]) [::] (Some(a,s'')) /\
                 run [::] (Alt s'' gl) (append_alt a a'') (Some(a',s')))
  \/
  (run [::] (Alt s [:: g]) a'' None /\ exists a1 a2, a1 :: a2 = a'' /\ run [::] a1 a2 (Some(a',s'))).
Proof.
Admitted. *)


(* Lemma run_x_cut_y P s g1 g2 cta _a a' s' s'' :
  run [::] (Alt s (g1 ++ [:: Goal P Cut cta] ++ g2)) [::] (Some(a',s')) ->
  run [::] (Alt s g1) [::] (Some(_a,s'')) ->
  run [::] (Alt s'' g2) cta (Some(a',s')).
Proof.
move: ([::] : list alt) cta (suffix0 cta).
elim: g1 => [|g gl IH] e cta Hcta.
  rewrite cat0s cat_cons cat0s => H.
  inversion H; subst => {H} H1.
  by inversion H1; subst => {H1}.
rewrite cat_cons => H H1.
case/run_x_y: H1 => s1 [a [H1 H2]]. *)


Definition is_det P p args :=
  forall a s0 s, run args (Alt s0 [:: Goal P (Call p) [::]]) [::] (Some(a,s)) -> a = [::].

Definition Gamma := C -> S.

Axiom lookup_Gamma : Gamma -> C -> list Tm -> B * list (S * Tm) * list (S * Tm). 

Fixpoint allp2 {A B} (f : A -> B -> Prop)  l :=
  match l with
  | [::] => True
  | [:: (x,y) & l] => f x y /\ allp2 f l
  end.

#[bypass_check(guard)]
Fixpoint sem P G ty (t : Tm) {struct t} :=
  match ty, t with
  | Base Exp, Data _ _ => True
  | Base (Det d'), Code c args =>
      let: (d,i, o) := lookup_Gamma G c args in
      d = Det d' /\
      if d is Det Func then allp2 (sem P G) i -> is_det P c args /\ True
      else True
  | Arr _ _ _, Lam _ _ _ _ => False
  | _, _ => False
  end.

Definition checked P G :=
  forall c args,
  let: (f,i, o) := lookup_Gamma G c args in
  sem P G (Base f) (Code c args).

Axiom le : S -> S -> Prop.

Inductive assume : S -> Tm -> Gamma -> Gamma -> Prop :=
| assume_exp s g f args b i o : lookup_Gamma g f args = (b,i,o) -> assume s (Data f args) g g
.


From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Fixpoint list_to_state (l: alts) : state :=
  match l with
  | no_alt => Bot
  | more_alt x no_alt => 
    let l := goals_to_state x.2 KO in
    Or KO x.1 l
  | more_alt x (more_alt y ys as t) => 
    let t := goals_to_state x.2 (list_to_state t) in
    Or KO x.1 t
  end
with goals_to_state (l:goals) t: (state):=
  match l with
  | no_goals => (Or Top empty t)
  | more_goals x xs => 
    let '(l, tca) := goal_to_state x in
    let r := goals_to_state xs t  in
      (And l l r)
  end
with goal_to_state (l:G) :=
  match l with
  | call pr tm ca => (CallS pr tm, list_to_state ca)
  | cut ca => (CutS, list_to_state ca)
  end
. *)

Inductive G' := 
  | call' : program -> Callable -> G'
  | cut' : alts' -> G'
with alts' :=
  | no_alt'
  | more_alt' : (nat * Sigma * goals') -> alts' -> alts'
with goals' :=
  | no_goals'
  | more_goals' : (nat * G') -> goals' -> goals' 
  .

Fixpoint erase_G' (g : G') : G :=
  match g with
  | call' p c => call p c
  | cut' a => cut (erase_alts' a)
  end
with erase_alts' (a : alts') : alts := 
  match a with
  | no_alt' => nilC
  | more_alt' (_, s,gl') a' => (s,erase_goals' gl') ::: (erase_alts' a')
  end
with erase_goals' (a : goals') : goals :=
  match a with
  | no_goals' => nilC
  | more_goals' (_, g') a' => (erase_G' g') ::: (erase_goals' a')
  end.

  Fixpoint append_alts' l1 l2 := 
    match l1 with
    | no_alt' => l2
    | more_alt' (n, hd) tl => more_alt' (n, hd) (append_alts' tl l2)
    end.

    Axiom eqb_alts' : alts' -> alts' -> bool.
    Lemma xx a b : reflect (a = b) (eqb_alts' a b).
    Admitted.

    Lemma xx_refl a: eqb_alts' a a. Admitted. 

  Lemma alts_eqb_OK' : Equality.axiom eqb_alts'.
  Proof. apply: iffP2 xx xx_refl. Qed.
  HB.instance Definition _ : hasDecEq _ := hasDecEq.Build _ alts_eqb_OK'.

  Fixpoint map_alts' F l :=
    match l with
    | no_alt' => no_alt'
    | more_alt' x xs => more_alt' (F x) (map_alts' F xs)
    end.


  #[program] Global Instance IsList_alts' : @IsList (nat * Sigma * goals') alts' :=
    {| 
    nilC := no_alt'; consC := more_alt';
    appendC := append_alts'; 
    map := map_alts';
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
  Admit Obligations.

  Fixpoint append_goals' l1 l2 := 
    match l1 with
    | no_goals' => l2
    | more_goals' (n, hd) tl => more_goals' (n, hd) (append_goals' tl l2)
    end.

  Fixpoint map_goals' F l :=
    match l with
    | no_goals' => no_goals'
    | more_goals' x xs => more_goals' (F x) (map_goals' F xs)
    end.


  #[program] Global Instance IsList_goals' : @IsList _ _ :=
    {| 
    nilC := no_goals'; consC := more_goals';
    appendC := append_goals';
    map := map_goals';
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
  Admit Obligations.

Definition add_ca' alts a : (nat * _) :=
  match a with
  | (n, cut' a1) => (n, cut' (a1 ++ alts))
  | (n, call' pr t) => (n, call' pr t)
  end.

Definition save_goals' (a: alts') (gs b:goals') := map (add_ca' a) b ++ gs.

Definition save_alts' (a : alts') (gs: goals') (bs : alts') := 
  map (fun '((n,s,x): nat * Sigma * goals') => (n, s, save_goals' a gs x)) bs.

  Definition a2g' p A :=
  match A with
  | ACut => cut' nilC
  | ACall t => call' p t
  end.

Fixpoint a2gs' n p (b: seq A) := 
  match b with
  | nil => nilC
  | x::xs => (n, a2g' p x) ::: (a2gs' n p xs)
  end.

Fixpoint aa2gs' n p (b: (seq (Sigma * R))) := 
  match b with
  | nil => nilC
  | x::xs => (n, x.1, a2gs' n p x.2.(premises)) ::: (aa2gs' n p xs)
  end.

Definition a2gs1' n p (b : Sigma * R) :=
  a2gs' n p b.2.(premises).

Definition isnil x := erase_goals' x == nilC.
Definition isnila x := erase_alts' x == nilC.

Definition same' x y := erase_alts' x = erase_alts' y.

Definition hd' x y ys := erase_goals' x = (erase_G' y) ::: (erase_goals' ys).

Inductive nur' u : Sigma -> goals' ->  alts' -> Sigma -> alts' -> Type :=
| StopE' s a : nur' s nilC a s a
| CutE' s s1 a ca r gl n1 : nur' s gl ca s1 r -> nur' s ((n1, cut' ca) ::: gl) a s1 r
| CallE' p s s1 a b bs gl r t n1: 
  F u p t s = [:: b & bs ] -> 
    nur' b.1 (save_goals' a gl (a2gs1' n1.+1 p b)) (save_alts' a gl ((aa2gs' n1.+1 p) bs) ++ a) s1 r -> 
      nur' s ((n1, call' p t) ::: gl) a s1 r
| FailE' p s s1 s2 t gl a al r n n1 : 
  F u p t s = [::] -> nur' s1 a al s2 r -> nur' s ((n, call' p t) ::: gl) ((n1, s1, a) ::: al) s2 r.

(* Lemma listP' {l x xs} : erase_goals' l = x ::: xs ->
  exists y ys, erase_goals' l = (erase_G' y) ::: (erase_goals' ys).
Admitted. *)

Fixpoint decorate_G (g : G) : G' :=
  match g with
  | call p c => call' p c
  | cut a => cut' (decorate_alts a)
  end
with decorate_alts (a : alts) : alts' :=
  match a with
  | no_alt => nilC
  | more_alt (s,gl) a => (0, s,decorate_goals gl) ::: (decorate_alts a)
  end
with decorate_goals (a : goals) : goals' :=
  match a with
  | no_goals => nilC
  | more_goals g a => (0, decorate_G g) ::: (decorate_goals a)
  end.

Lemma erase_decorate_G x : erase_G' (decorate_G x) = x
with erase_decorate_goals x : erase_goals' (decorate_goals x) = x
with erase_decorate_alts x : erase_alts' (decorate_alts x) = x.
- by case: x => //= a; rewrite erase_decorate_alts.
- by case: x => //= g gs; rewrite erase_decorate_goals erase_decorate_G.
- by case: x => //= -[s g] gs /=; rewrite erase_decorate_alts erase_decorate_goals.
Qed.

Definition ed := (erase_decorate_alts, erase_decorate_goals, erase_decorate_G).

Notation elpi_annot := nur'.
Notation elpi := nur.

(* Lemma e erase_goals' (map (add_ca' a)) = mapG (add_ca (erase_alts' a)) *)

Lemma erase_append x a b : erase_alts' x = a ++ b -> exists a' b', erase_alts' a' = a /\ erase_alts' b' = b /\ x = a' ++ b'.
elim: x a b.
  case => //=; case => //= _ ; exists nilC, nilC; repeat split.
move=> p a IH b c.
Admitted.

Lemma cat_erase_alts' a x : erase_alts' a ++ erase_alts' x = erase_alts' (a ++ x).
Admitted.

Lemma save_alts_erase x y gl :
  save_alts (erase_alts' x) (erase_goals' y) (erase_alts' gl) =
  erase_alts' (save_alts' x y gl)
with save_goals_erase x y gl :
  save_goals (erase_alts' x) (erase_goals' y) (erase_goals' gl) =
  erase_goals' (save_goals' x y gl).
- rewrite /save_alts.
  case: gl => //= -[[? s] gl] a.
  rewrite map_cons.
  congr ((_,_) ::: _).
    by rewrite save_goals_erase.
  by rewrite [LHS]save_alts_erase.
- case: gl => //= -[? g gs] //=.
  rewrite /save_goals /save_goals' !map_cons /= [in RHS]cat_cons /=.
  rewrite cat_cons.
  case: g => /= [p c|a].
  congr (_ ::: _).
    by rewrite -save_goals_erase.
  congr ((cut _) ::: _); try rewrite -save_goals_erase //.
  exact: cat_erase_alts'.
Qed.

Lemma aa2gs_erase n p bs : (aa2gs p bs) = erase_alts' (aa2gs' n p bs).
Admitted.
Lemma a2gs1_erase n p bs : (a2gs1 p bs) = erase_goals' (a2gs1' n p bs).
Admitted.

Lemma one u s xs a s1 a1: nur' u s xs a s1 a1 -> 
  nur u s (erase_goals' xs) (erase_alts' a) s1 (erase_alts' a1).
Proof.
  elim => /=; clear.
  - move=> *; constructor.
  - move=> *; constructor => //.
  - move=> p s s1 a [s2 r] rs gl a1 t n/= H H1 H2.
    apply: CallE H _ => /=.
    move: H2.
    rewrite/save_goals/=/map/=/save_goals'/=.
    rewrite -!save_goals_erase => H.
    congr (elpi _ _ _ _ _) : H.
      by rewrite /save_goals/map/= -a2gs1_erase.
    by rewrite (aa2gs_erase n.+1) save_alts_erase cat_erase_alts'.
  - move=> p s s1 s2 t gl a al r _ _ H H1 H2.
    apply: FailE H H2.
Qed.


Lemma two' {u s s1 alts alts_left andg}  : nur u s andg alts s1 alts_left -> forall alts' andg',
  (erase_alts' alts' = alts) -> 
  (erase_goals' andg' = andg) ->
  Texists alts_left',
  (erase_alts' alts_left' = alts_left) /\ (nur' u s andg' alts' s1 alts_left').
elim; clear.

move=> s a a' [|[]//] ? _; subst.
by eexists; split => //; apply: StopE'.

move=> s s1 a ca r gl H IH ? [|[n g gs]]// H1 [H2 H3].
case: g H2 => //= [? [?]]; subst.
have [x [? ?]] := IH _ _ erefl erefl.
subst.
eexists; split => //.
by apply: CutE'.

move=> p s1 s2 old_alts [s0 b0]/= bs andg new_alts c EF He IH old_alts' [|[n [p'|ct]] c'] // andg' E1 /= [-> ->] E2.
subst.
rewrite (aa2gs_erase n.+1) save_alts_erase cat_erase_alts' in IH.
have {}IH:= (IH _ _ erefl).
rewrite (a2gs1_erase n.+1) save_goals_erase in IH.
have {IH} [new_alts' [H1 H2]]:= (IH _ erefl).
eexists; split; try eassumption.
apply: CallE' EF H2 => /=.

move=> p s s1 s2 c gl gl1 al al1 BC H1 IH [//|[[]]] /= n s3 g' a' [//|[m [|]//]] p' c' g'' [???] [???].
subst.
have [new_alts' [? ?]] := (IH _ _ erefl erefl).
eexists; split; try eassumption.
by apply: FailE' BC _  => /=.

Defined.


Definition l2l' {u s s1 a a1 xs} (H : elpi u s xs a s1 a1) :
  Texists xs' a' a1', erase_alts' a1' = a1 /\ elpi_annot u s xs' a' s1 a1'.
have @H1 : erase_alts' (decorate_alts a) = a by rewrite ed.
have @H2 : erase_goals' (decorate_goals xs) = xs by rewrite ed.
exists (decorate_goals xs), (decorate_alts a).
have @H3 := two' H _ _ H1 H2.
have [a' [??]]:= two' H _ _ H1 H2.
by exists a'.
Defined.

Definition annotate_left_alts {u s s1 a a1 xs} (H : elpi u s xs a s1 a1) : alts' :=
  projT1 (projT2 (projT2 (l2l' H))).

Definition annotate_start_alts {u s s1 a a1 xs} (H : elpi u s xs a s1 a1) : alts' :=
  projT1 (projT2 (l2l' H)).

Definition annotate_start_gls {u s s1 a a1 xs} (H : elpi u s xs a s1 a1) : goals' :=
 (projT1 (l2l' H)).

Lemma annotate_start_gls_call p u s c s1 a1 (H : elpi u s ((call p c):::nilC) nilC s1 a1) :
  annotate_start_gls H = (((0,call' p c):::nilC)).
by [].
Qed.

Lemma annotate_start_alts_nil u s s1 a1 g (H : elpi u s g nilC s1 a1) :
  annotate_start_alts H = nilC.
by [].
Qed.



Lemma l2l'P {u s s1 a a1 xs} (H : elpi u s xs a s1 a1) :
  elpi_annot u s (annotate_start_gls H) (annotate_start_alts H) s1 (annotate_left_alts H).
Proof.
  rewrite /annotate_left_alts /annotate_start_gls /annotate_start_alts.
   move: (l2l' _) => [? [? [? [? ? ]]]] //=.
Qed.

Fixpoint la2t (a : alts') : state :=
  match a with
  | no_alt' => Bot
  | more_alt' (n,s,gl) a => g2t gl
  end
with g2t (g : goals') : state :=
  match g with
  | no_goals' => Top
  | more_goals' (n,g) gs => G2t g
  end
with G2t (g : G') : state :=
  match g with
  | call' p c => CallS p c
  | cut' ca => CutS
end
.


Definition l2tP {u s xs a s' a'} : elpi_annot u s xs a s' a' ->
  Texists b n, run u s (la2t ((n,s,xs):::a)) s' (la2t a') b.
Admitted.

Lemma init_valid  u s g a s1 a1 (H : elpi u s g a s1 a1) :
  valid_state (la2t (annotate_start_alts H)).
Admitted.

Lemma final p u s c s1 a1 (H : elpi u s ((call p c):::nilC) nilC s1 a1) :
  run u s (CallS p c) s1 (la2t (annotate_left_alts H)) 0.
Proof.
  have H' := l2l'P H.
  have [b [n H1]] := l2tP H'.
  rewrite !(annotate_start_gls_call,annotate_start_alts_nil) /= in H' H1.
  simpl in H'.
  suff <- : b = 0 by [].
  admit.
Admitted.
From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang list.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

(*BEGIN*)

Declare Scope L.
Infix "::" := consC : L.
Bind Scope L with IsList.

(*SNIP: elpi_def*)
Inductive alts := no_alt | more_alt of (Sigma * goals) & alts
with goals := no_goals | more_goals of (A * alts) & goals .
(*ENDSNIP: elpi_def*)

Declare Scope alts_scope.
Delimit Scope alts_scope with A.
Bind Scope alts_scope with alts.

Declare Scope goals_scope.
Delimit Scope goals_scope with G.
Bind Scope goals_scope with goals.

Notation "[ :: ]" := no_goals (format "[ :: ]") : goals_scope.
Notation "[ :: ]" := no_alt (format "[ :: ]") : alts_scope.

Notation "[ :: x1 ]" := (more_alt x1%G [::]) (format "[ ::  x1 ]") : alts_scope.
Notation "[ :: x1 ]" := (more_goals x1%A [::]) (format "[ ::  x1 ]") : goals_scope.

Notation "[ :: x & s ]" := (more_alt x%G s) (format "'[hv' [ :: '['  x ']' '/ ' &  s ] ']'") : alts_scope.
Notation "[ :: x & s ]" := (more_goals x%A s) (format "'[hv' [ :: '['  x ']' '/ ' &  s ] ']'") : goals_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (more_alt x1 (more_alt x2 .. (more_alt xn s) ..))
  (format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : alts_scope.
Notation "[ :: x1 , x2 , .. , xn & s ]" := (more_goals x1 (more_goals x2 .. (more_goals xn s) ..))
  (format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : goals_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (more_alt x1 (more_alt x2 .. (more_alt xn [::]) ..))
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : alts_scope.
Notation "[ :: x1 ; x2 ; .. ; xn ]" := (more_goals x1 (more_goals x2 .. (more_goals xn [::]) ..))
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : goals_scope.


Open Scope goals_scope.
Open Scope alts_scope.

Fixpoint eqbA t1 t2 :=
  match t1, t2 with
  | no_alt, no_alt => true
  | more_alt (s1,h1) t1, more_alt (s2, h2) t2 => (s1 == s2) && eqbGs h1 h2 && eqbA t1 t2
  | _, _ => false
  end
with eqbGs t1 t2 :=
  match t1, t2 with
  | no_goals, no_goals => true
  | more_goals (a1,h1) t1, more_goals (a2,h2) t2 => (a1 == a2) && eqbA h1 h2 && eqbGs t1 t2
  | _, _ => false
  end.

Lemma eqb_reflA l : eqbA l l
  with eqb_reflG l : eqbGs l l.
Proof.
  {
    case: l => /=//.
    move=> [s1 g] gs; rewrite eqxx eqb_reflA eqb_reflG//.
  }
  case: l => /=//.
  move=> [a al] /= gs; rewrite ?eqxx eqb_reflG//eqb_reflA//.
Qed.

Lemma eqbPA l1 l2 : reflect (l1 = l2) (eqbA l1 l2)
  with eqbPG l1 l2 : reflect (l1 = l2) (eqbGs l1 l2).
Proof.
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> ??; constructor => //.
    - move=> []?; constructor => //.
    - move=> [s1 x] xs [s2 y] ys.
      case: eqP => //=?; last first; subst.
        constructor; congruence.
      apply: (iffP andP) => [[/eqbPG -> /eqbPA -> //]|[-> ->]].
      by split; [ apply/eqbPG| apply/eqbPA].
  }
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> ??; constructor => //.
    - move=> []?; constructor => //.
    - move=> [s1 x] xs [s2 y] ys.
      case: eqP => //=?; last first; subst.
        constructor; congruence.
      apply: (iffP andP) => [[/eqbPA -> /eqbPG -> //]|[-> ->]].
      by split; [ apply/eqbPA| apply/eqbPG].
  }
Qed.

Lemma goals_eqb_OK : Equality.axiom eqbGs.
Proof. apply: iffP2 eqbPG eqb_reflG. Qed.
HB.instance Definition _ : hasDecEq goals := hasDecEq.Build goals goals_eqb_OK.

Lemma alts_eqb_OK : Equality.axiom eqbA.
Proof. apply: iffP2 eqbPA eqb_reflA. Qed.
HB.instance Definition _ : hasDecEq alts := hasDecEq.Build alts alts_eqb_OK.

  Fixpoint seq2alts (l : seq (Sigma * goals)) : alts :=
    match l with
    | [::]%SEQ => [::]
    | [:: x & xs]%SEQ => [:: x & seq2alts xs]
    end.

  Fixpoint alts2seq (a : alts) : seq (Sigma * goals) :=
    match a with
    | [::] => [::]%SEQ
    | [:: x & xs] => [:: x & alts2seq xs]%SEQ
    end.
  Lemma alts2seqs : forall x xs, alts2seq [:: x & xs ] = [:: x & alts2seq xs]%SEQ. by []. Qed.
  Lemma alts2seq0 : alts2seq [::] = [::]%SEQ. by []. Qed.
  Lemma seq2altss : forall x xs, seq2alts [:: x & xs ]%SEQ = [:: x & seq2alts xs]. by []. Qed.
  Lemma seq2alts0 : seq2alts [::]%SEQ = [::]. by []. Qed.
  Lemma alts2seqK : forall l, alts2seq (seq2alts l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2altsK : forall l, seq2alts (alts2seq l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2alts_inj : forall l1 l2,  seq2alts l1 = seq2alts l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]alts2seqK -[l2]alts2seqK H. Qed.
  Lemma alts2seq_inj : forall l1 l2,  alts2seq l1 = alts2seq l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]seq2altsK -[l2]seq2altsK H. Qed.

  Global Instance IsList_alts : @IsList (Sigma * goals)%type alts :=
    mkIsList seq2alts alts2seq alts2seqs alts2seq0 seq2altss seq2alts0
      alts2seqK seq2altsK seq2alts_inj alts2seq_inj.

  Fixpoint seq2goals (l : seq (A * alts)) : goals :=
    match l with
    | [::]%SEQ => [::]%G
    | [:: x & xs]%SEQ => [:: x & seq2goals xs]%G
    end.

  Fixpoint goals2seq (a : goals) : seq (A * alts) :=
    match a with
    | [::]%G => [::]%SEQ
    | [:: x & xs]%G => [:: x & goals2seq xs]%SEQ
    end.
  Lemma goals2seqs : forall x xs, goals2seq [:: x & xs ]%G = [:: x & goals2seq xs]%SEQ. by []. Qed.
  Lemma goals2seq0 : goals2seq [::]%G = [::]%SEQ. by []. Qed.
  Lemma seq2goalss : forall x xs, seq2goals [:: x & xs ]%SEQ = [:: x & seq2goals xs]%G. by []. Qed.
  Lemma seq2goals0 : seq2goals [::]%SEQ = [::]%G. by []. Qed.
  Lemma goals2seqK : forall l, goals2seq (seq2goals l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2goalsK : forall l, seq2goals (goals2seq l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2goals_inj : forall l1 l2,  seq2goals l1 = seq2goals l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]goals2seqK -[l2]goals2seqK H. Qed.
  Lemma goals2seq_inj : forall l1 l2,  goals2seq l1 = goals2seq l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]seq2goalsK -[l2]seq2goalsK H. Qed.

  Global Instance IsList_goals : @IsList (A * alts)%type goals :=
    mkIsList seq2goals goals2seq goals2seqs goals2seq0 seq2goalss seq2goals0
      goals2seqK seq2goalsK seq2goals_inj goals2seq_inj.

Ltac fConsA x xs := change (more_alt x xs) with (consC x xs).
Ltac fConsG x xs := change (more_goals x xs) with (consC x xs).
Ltac fNilA := change no_alt with (@nilC _ _ IsList_alts).
Ltac fNilG := change no_goals with nilC.

Lemma seq2alts_cat : forall l1 l2,  seq2alts (l1 ++ l2) = (seq2alts l1 ++ seq2alts l2).
Proof. by elim => //=[|x xs IH] l2; rewrite (cat0s, cat_cons)//IH. Qed.
Lemma seq2goals_cat : forall l1 l2,  seq2goals (l1 ++ l2) = (seq2goals l1 ++ seq2goals l2).
Proof. by elim => //=[|x xs IH] l2; rewrite (cat0s, cat_cons)//IH. Qed.

Lemma cat_right_same {l1 l2} (l3:alts): 
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof.
  elim: l1 l2 l3 => //.
    move=>[]//x xs l3/=.
    fConsA x xs; fNilA.
    rewrite cat0s => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite size_cons size_cat.
    by rewrite addnC -addnS => /addSn_false.
  move=> x xs IH [|y ys]//l3; fNilA.
    fConsA x xs => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite cat_cons size_cons !size_cat size_nil.
    by rewrite addnC -addnS => /esym /addSn_false.
  move=>[<-]/IH->//.
Qed.

Section cat.
  Variable A B T : Type.
  Definition catr {H : IsList A B} (suff: B) (e: T * B) := (e.1, e.2 ++ suff).
  Definition catl {H : IsList A B} (pref: B) (e: T * B) := (e.1, pref ++ e.2).
End cat.

Definition save_goals (a: alts) (gs b:goals) := map (catr a) b ++ gs.

Definition save_alts (a : alts) (gs: goals) (bs : alts) := 
  map (fun '(s,x) => (s, save_goals a gs x)) bs.

Definition empty_ca_G (g : A * alts) :=
  match g with (_,[::]) => true | _ => false end.

Definition empty_caG goals := all empty_ca_G goals.
Definition empty_ca alts := all (fun x => empty_caG (snd x)) alts.

Definition a2g (b: seq A) := seq2goals [seq (x, [::]) | x <- b].

Definition r2a (b: (seq (Sigma * seq A))) : alts := 
    seq2alts [seq (x.1, a2g x.2) | x <- b].

(* Definition a2g1 (b : Sigma * R) := a2g b.2.(premises). *)

Section Nur.

Variable u : Unif.
Variable p : program.

From det Require Import finmap.
Open Scope fset_scope.

(*SNIP: stepE *)
Definition stepE fv t s a gl :=
  let (fv', rs) := bc u p fv t s  in
  let rs_ca := save_alts a gl (r2a rs) in
  (fv', rs_ca).
(*ENDSNIP: stepE *)

(*prooftree: nurbp*)
(*SNIP: nur *)
(*SNIP: nur_type*)
Inductive nur : fvS -> Sigma -> goals ->  alts -> Sigma -> alts -> Prop :=
(*ENDSNIP: nur_type*)
| StopE s a fv : nur fv s [::] a s a
| CutE s s1 a ca r gl fv : nur fv s gl ca s1 r -> nur fv s [:: (cut, ca) & gl] a s1 r
| CallE s s1 al b bs gl r t ca fv fv': 
    stepE fv t s al gl = (fv', [:: b & bs ]) -> 
      nur fv' b.1 b.2 (bs++al) s1 r -> 
        nur fv s [:: (call t, ca) & gl] al s1 r
| FailE s s1 s2 t gl a al r ca fv fv': 
    stepE fv t s al gl = (fv', [::]) -> 
      nur fv' s1 a al s2 r ->   
        nur fv s [:: (call t, ca) & gl] [:: (s1, a) & al] s2 r.
(*ENDSNIP: nur *)
(*endprooftree: nurbp *)

Lemma stepE_len fv t s a1 a2 gl:
  size (stepE fv t s a1 gl).2 = size (stepE fv t s a2 gl).2.
Proof.
  rewrite/stepE; case: bc => //= _ b.
  by rewrite/save_alts !size_map.
Qed.

Lemma nur_consistent fv s G x xs1 xs2 s1 s2 :
  nur fv s G x s1 xs1 -> nur fv s G x s2 xs2 -> xs1 = xs2 /\ s1 = s2.
Proof.
  move=> H; elim: H xs2 s2 => //; clear.
  - inversion 1 => //.
  - move=> s a ca r gl fv H IH xs2.
    by inversion 1; subst; auto.
  - move=> s s1 a b bs gl r t ca fv1 fv2 H H1 IH xs2 s2 H2.
    apply: IH.
    inversion H2; subst => //; first by congruence.
    have:= stepE_len fv1 t s al [:: (s3, a0)& al] gl.
    by rewrite H10 H.
  - move=> s s1 s2 t gl a al r ca f1 f2 H H1 IH xs2 s3 H2.
    apply: IH.
    inversion H2; subst => //; try congruence.
    have:= stepE_len f1 t s al [:: (s1, a)& al] gl.
    by rewrite H10 H.
Qed.

End Nur. 
(*END*)
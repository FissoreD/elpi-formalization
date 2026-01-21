From mathcomp Require Import all_ssreflect.
From det Require Import tree elpi.

(*BEGIN*)
Definition make_lB0 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, x ++ lB0)) xs.

Definition make_lB01 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, lB0 ++ x)) xs.

Definition add_ca_deep_g' (add_ca_deep : alts -> alts -> alts) bt (x : A * alts) :=
  match x with
  | (a,ca) => (a,add_ca_deep bt ca ++ bt)
  end.

Fixpoint add_ca_deep (bt:alts) (ats: alts) : alts :=
  match ats with
  | [::] => [::]
  | [:: (hd,xs) & tl ] => [:: (hd, add_ca_deep_goals bt xs) & (add_ca_deep bt tl) ]
  end
with add_ca_deep_goals bt (gl : goals) : goals :=
  match gl with
  | [::]%G => [::]%G 
  | [:: g & tl ]%G => [:: add_ca_deep_g' add_ca_deep bt g & add_ca_deep_goals bt tl ]
  end.

Notation add_ca_deep_g := (add_ca_deep_g' add_ca_deep).

Fixpoint add_deep (bt: alts) (l: goals) (A : alts) : alts :=
  match A with
  | [::] => [::]
  | [:: (s,hd) & tl ] => [:: (s,add_deepG bt l hd) & add_deep bt l tl]
  end
  with add_deepG (bt: alts) (l: goals) (A : goals) : goals :=
  match A with
  | [::]%G => [::]%G 
  | [:: (call t,ca) & tl ]%G => [:: (call t,ca) & add_deepG bt l tl]
  | [:: (cut,   ca) & tl ]%G =>
      let s := size ca - size bt in
      let xx := (add_deep bt l (ca)) in
      let ca := (make_lB0 (take s xx) l ++ drop s ca) in
      [:: (cut, ca) & add_deepG bt l tl]
  end.

Definition kill (A: goals) := map (apply_cut (fun x => [::])) A.

(* reset-point to list *)
Definition r2l a : goals := seq2goals [seq a2g x | x <- a].


  (* bt is the backtracking list for the cut-alternatives
    this list is important since in this tree:
          or   
        /  \  
        or   K 
      /  \    
      !    J   
    K is in bt but not J, i.e. we have to consider two different levels:
    the "siblings" on the right of a cut are NOT alternatives
    the "great^n uncles" on the right of a cut ARE alternatives
  *)

(*SNIP: t2l*)
Fixpoint t2l (A: tree) s (bt : alts) : alts :=
match A with
| OK          => [:: (s, [::]) ]
| Bot         => [::]
| Dead        => [::]
| TA cut      => [:: (s, [:: (cut,[::]) ]) ]
| TA (call t) => [:: (s, [:: (call t,[::]) ]) ]
| Or A s1 B => 
    let lB := t2l B s1 [::] in
    let lA := t2l A s lB in
    add_ca_deep bt (lA ++ lB)
| And A B0 B =>
    let hd  := r2l B0 in
    let lA  := t2l A s bt in
    if lA is [:: (slA, x) & xs] then 
      (* the reset point exists, it has to be added to all cut-to alternatives *)
      let xz := add_deepG bt hd x in
      let xs := add_deep bt hd xs in 
      (* each alt in xs must have hd has rightmost conjunct  *)
      let xs := make_lB0 xs hd in
      (* xs are alternatives that should be added in the deep cuts in B *)
      let lB   := t2l B slA (xs ++ bt) in
      (* lB are alternatives, each of them have x has head *)
      (make_lB01 lB xz) ++ xs
    else [::]
end.
(*ENDSNIP*)
(* 
Global Notation "-nilCG" :=
  (@nilC _ _ IsList_goals)
  (at level 2, no associativity, only parsing)
  : SE.
Global Notation "-nilCA" :=
  (@nilC _ _ IsList_alts)
  (at level 2, no associativity, only parsing)
  : SE. *)

Lemma make_LB0_cons a (ax : alts) (gl : goals) :
  make_lB0 [::a & ax] gl  = [:: (a.1, a.2 ++ gl) & make_lB0 ax gl].
Proof. by rewrite /make_lB0 [map _ _]map_cons; case: a. Qed.

Lemma make_LB0_nil gl : make_lB0 [::] gl = [::]. by []. Qed.

Lemma make_LB01_cons a (ax : alts) (gl : goals) :
  make_lB01 [::a & ax] gl  = [:: (a.1, gl ++ a.2) & make_lB01 ax gl].
Proof. by rewrite /make_lB01 [map _ _]map_cons; case: a. Qed.

Lemma make_LB01_nil gl : make_lB01 [::] gl = [::]. by []. Qed.

Definition make_LBE := (make_LB0_cons,make_LB01_cons,make_LB0_nil,make_LB01_nil,cat_cons,cat0s).

Section test.
  Variable u : Unif.
  Variable s1 : Sigma.
  Variable p : program.
  Variable sx : Sigma.
  Variable p1 : program.
  (* Definition g p := (And (Or OK s1 CutS) p OK). *)

  Goal forall s3 l, 
    t2l (And (Or OK s1 (TA cut)) ([:: cut]) Bot) s3 l = 
      t2l (And (Or Dead s1 (TA cut)) ([:: cut]) (TA cut)) s3 l.
  Proof.
    move=>s3 l/=.
    rewrite /=!cat0s ?cat0s subnn.
    by rewrite drop0 /= !make_LB0_cons !make_LB01_cons.
  Qed.
End test.
(*END*)
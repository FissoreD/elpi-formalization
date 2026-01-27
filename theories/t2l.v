From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree elpi.


(*BEGIN*)
Definition catr (suff: goals) (e: Sigma * goals) := (e.1, e.2 ++ suff).
Definition catl (pref: goals) (e: Sigma * goals) := (e.1, pref ++ e.2).

Lemma catl0 l: map (catl [::]) l = l.
Proof. elim: l => //=[[s g]gs] H; rewrite map_cons/=H/catl cat0s//. Qed.

Lemma catr0 l: map (catr [::]) l = l.
Proof. elim: l => //=[[s g]gs] H; rewrite map_cons/=H/catr cats0//. Qed.

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
  | [:: g & tl ]%G => [:: add_ca_deep_g' add_ca_deep bt g & add_ca_deep_goals bt tl ]%G
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
  | [:: (a, ca) & tl ]%G =>
      let s := size ca - size bt in
      let xx := (add_deep bt l (ca)) in
      let ca := map (catr l) (take s xx) ++ drop s ca in
      [:: (a, ca) & add_deepG bt l tl]%G
  end.

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
| OK           => [:: (s, [::]) ]
| (KO | Dead) => [::]
| TA a         => [:: (s, [:: (a,[::]) ]) ]
| Or A s1 B    =>
    let lB := t2l B s1 [::] in
    let lA := t2l A s lB in
    add_ca_deep bt (lA ++ lB)
| And A B0 B   =>
    let lB0 : goals := r2l B0 in
    let lA  := t2l A s bt in
    if lA is [:: (slA, x) & xs] then 
      (* the reset point exists, it has to be added to all cut-to alternatives *)
      let xz := add_deepG bt lB0 x in
      let xs := add_deep bt lB0 xs in 
      (* each alt in xs must have lB0 has rightmost conjunct  *)
      let xs := map (catr lB0) xs in
      (* xs are alternatives that should be added in the deep cuts in B *)
      let lB := t2l B slA (xs ++ bt) in
      (* lB are alternatives, each of them have x has head *)
      (map (catl xz) lB) ++ xs
    else [::]
end.
(*ENDSNIP*)

Section test.
  Variable u : Unif.
  Variable s1 : Sigma.
  Variable p : program.
  Variable sx : Sigma.
  Variable p1 : program.

  Goal forall s3 l, 
    t2l (And (Or OK s1 (TA cut)) ([:: cut]) KO) s3 l = 
      t2l (And (Or Dead s1 (TA cut)) ([:: cut]) (TA cut)) s3 l.
  Proof.
    move=>s3 l/=.
    rewrite /=!cat0s ?cat0s subnn.
    by rewrite drop0 /=.
  Qed.
End test.
(*END*)
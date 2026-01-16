From mathcomp Require Import all_ssreflect.
From det Require Import tree elpi.

Definition make_lB0 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, x ++ lB0)) xs.

Definition make_lB01 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, lB0 ++ x)) xs.

Fixpoint add_ca_deep (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, add_ca_deep_goals bt xs) ::: (add_ca_deep bt tl)
  end
with add_ca_deep_goals bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (add_ca_deep_g bt hd) ::: (add_ca_deep_goals bt tl)
  end
with add_ca_deep_g bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut ((add_ca_deep bt ca) ++ bt)
  end.

Fixpoint add_deep (bt: alts) (l: goals) (A : alts) : alts :=
  match A with
  | no_alt => nilC
  | more_alt (s,hd) tl => (s,add_deepG bt l hd) ::: (add_deep bt l tl)
  end
  with add_deepG (bt: alts) (l: goals) (A : goals) :=
  match A with
  | no_goals => nilC
  | more_goals hd tl => (add_deep_G bt l hd) ::: (add_deepG bt l tl)
  end
  with add_deep_G bt l A :=
  match A with
  | cut ca => 
    let s := size ca - size bt in
    let xx := (add_deep bt l (ca)) in
    cut (make_lB0 (take s xx) l ++ drop s ca)
  | call pr t => call pr t 
  end.

Definition kill (A: goals) := map (apply_cut (fun x => nilC)) A.

(* reset-point to list *)
Fixpoint r2l pr a : goals :=
  match a with
  | [::] => no_goals
  | x::xs => more_goals ((a2g pr x)) (r2l pr xs)
  end.


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

Fixpoint t2l (A: tree) s (bt : alts) : alts :=
match A with
| OK => (s, nilC) ::: nilC
| Bot => nilC
| Dead => nilC
| CutS => (s, ((cut nilC) ::: nilC)) ::: nilC
| CallS pr t => (s, ((call pr t) ::: nilC)) ::: nilC
| Or A s1 B => 
  let lB := t2l B s1 nilC in
  let lA := t2l A s lB in
  add_ca_deep bt (lA ++ lB)
| And A B0 B =>
  let hd := r2l B0.1 B0.2 in
  let lA   := t2l A s bt in
  let sB0 := s in
  if lA is more_alt (slA, x) xs then 
    (* lA is split into the current goal x and the future alternatives xs *)
    (* in a valid tree lB0 has length 0 or 1 (it is a (potentially killed) base and) *)
    (* match lB0 with *)
    (* | no_alt =>  *)
      (* the reset point is empty: it kill all the alternatives in the cut-to *)
      (* let lB   := t2l B slA bt in *)
      (* make_lB01 lB (kill x) *)
    (* | more_alt (sB0,hd) no_alt => *)
      (* the reset point exists, it has to be added to all cut-to alternatives *)
      let xz := add_deepG bt hd x in
      let xs := add_deep bt hd xs in 
      (* each alt in xs must have hd has rightmost conjunct  *)
      let xs := make_lB0 xs hd in
      (* xs are alternatives that should be added in the deep cuts in B *)
      let lB   := t2l B slA (xs ++ bt) in
      (* lB are alternatives, each of them have x has head *)
      (make_lB01 lB xz) ++ xs
  else nilC
end.

Global Notation "-nilCG" :=
  (@nilC _ _ IsList_goals)
  (at level 2, no associativity, only parsing)
  : SE.
Global Notation "-nilCA" :=
  (@nilC _ _ IsList_alts)
  (at level 2, no associativity, only parsing)
  : SE.

Section test.
  Variable u : Unif.
  Variable s1 : Sigma.
  Variable p : program.
  Variable sx : Sigma.
  Variable p1 : program.
  (* Definition g p := (And (Or OK s1 CutS) p OK). *)

  Goal forall s3 l p,
    t2l (And (Or OK s1 CutS) (p, [:: ACut]) Bot) s3 l = 
      t2l (And (Or Dead s1 CutS) (p, [:: ACut]) CutS) s3 l.
  Proof.
    move=>s3 l/= [] r s.
    rewrite /=!cat0s ?cat0s.
    rewrite subnn/= take0 drop0//.
  Qed.
End test.

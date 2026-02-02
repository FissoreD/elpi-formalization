From det Require Import prelude.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From det Require Import finmap.

(******* finite maps *********************************************************)
(*                                                                           *)
(* Finite maps are finite functions (from finfun) where the domain is        *)
(* obtained by the coercion of a {fset A} to the finType of its elements     *)
(* Operations on finmap:                                                     *)
(* The following notations are in the %fmap scope                            *)
(*                                                                           *)
(*           f.[? k] == returns Some v if k maps to v, otherwise None        *)
(*             f.[p] == returns v if p has type k \in f, and k maps to v     *)
(*        f.[k <- v] == f extended with the mapping k -> v                   *)
(*            domf f == finite set (of type {fset K}) of keys of f           *)
(*          codomf f == finite set (of type {fset V}) of values of f         *)
(*           k \in f == k is a key of f                                      *)
(*                   := k \in domf f                                         *)
(*            [fmap] == the empty finite map                                 *)
(* [fmap x : S => E] == the finmap defined by E on the support S             *)
(*           f.[& A] == f restricted to A (intersected with domf f)          *)
(*           f.[\ A] := f.[& domf `\` A]                                     *)
(*                   == f where all the keys in A have been removed          *)
(*           f.[~ k] := f.[\ [fset k]]                                       *)
(*             f + g == concatenation of f and g,                            *)
(*                      the keys of g override the keys of f                 *)
(*                                                                           *)

Local Notation ctx A B := {fmap A -> B}.
Open Scope fmap_scope.

Notation key_absent k c := (k \notin c) (only parsing).
Notation remove k c := c.[~ k] (only parsing).
Notation lookup k c := c.[? k] (only parsing).
Notation add k v c := c.[k <- v] (only parsing).
Notation empty := [fmap].

Section Theory.
  Variables (K : countType) (V : eqType).
  Implicit Types c d  : ctx K V.

  Lemma valid_sig_add_diff {k k' v' c}: 
    k \notin c ->
      k <> k' ->
        k \notin (add k' v' c).
  Proof.
    by move=> + Neq; apply: contra; rewrite !inE /=; case: eqP Neq => [->|].
  Qed.


  Lemma key_absent_add_diff {k k' v c}:
    k <> k' -> key_absent k' (add k v c) = key_absent k' c.
  Proof.
    by rewrite !inE negb_or eq_sym => /eqP ->.
  Qed.

  Lemma key_absent_remove {k c} : (key_absent k c) -> remove k c = c.
  Proof.
    by exact: remf1_id.
  Qed.

  Lemma lookup_remove_None {k c}:
    (lookup k (remove k c)) = None.
  Proof.
    by rewrite fnd_rem1 eqxx.
  Qed.

  Lemma lookup_remove_diff {k k' c}:
     k' <> k ->
      lookup k (remove k' c) = lookup k c.
  Proof.
    by rewrite fnd_rem1 eq_sym => /eqP->.
  Qed.

  Lemma remove_comm {x y c}:
    remove x (remove y c) = remove y (remove x c).
  Proof.
    by apply/fmapP => k; rewrite !fnd_rem1; case: eqP; case: eqP.
  Qed.

  Open Scope fset_scope.

  Lemma lookup_cat {k} {c d}:
      lookup k (d + c) = 
        if key_absent k c then lookup k d
        else lookup k c.
  Proof.
    by rewrite fnd_cat; case: ifP.
  Qed.

  Lemma add2  {k v v1} {c} : add k v (add k v1 c) = add k v c.
  Proof.
    by apply/fmapP=> k'; rewrite !fnd_set; case: eqP.
  Qed.

  Lemma add_cat c {k v1 v2 d}:
    key_absent k c ->
    add k v1 (d.[k <- v2] + c) = (d.[k <- v1] + c).
  Proof.
    by move=> /negPf Hin; rewrite setf_catr [RHS]catf_setl Hin catf_setl !inE eqxx /= catf_setr.
  Qed.

  Lemma lookup_add_same {c} {k v}:
    lookup k (add k v c) = Some v.
  Proof.
    by rewrite fnd_set eqxx.
  Qed.

  Lemma lookup_add_Some {c} {k k' v' v}:
    lookup k (add k' v' c) = Some v ->
      if k' == k then v = v'
      else lookup k c = Some v.
  Proof.
    by rewrite fnd_set eq_sym; case: eqP => [? [->]|].
  Qed.

  Lemma lookup_add_diff {k k' v} {c}:
      k <> k' -> lookup k' (add k v c) = lookup k' c.
  Proof.
    by move=>/eqP /negPf H; rewrite fnd_set eq_sym H.
  Qed.

  Lemma lookup_add_Some2 {kB k'} k v {c}:
    lookup k' c = Some kB ->
    exists kB',
      lookup k' (add k v c) = Some kB'.
  Proof.
    case: (k =P k') => [-> H|/eqP/negPf H].
      by exists v; rewrite fnd_set eqxx.
    by exists kB; rewrite fnd_set eq_sym H.
  Qed.

  Lemma add_comm {k1 k2 m1 m2}  {c}:
    k1 <> k2 -> add k1 m1 (add k2 m2 c) = add k2 m2 (add k1 m1 c).
  Proof.
      by move=> /eqP/negPf H; rewrite setfC H.
  Qed.

  Lemma remove2 {k} {c}:
    remove k (remove k c) = remove k c.
  Proof.
    by rewrite restrictf_comp domf_rem fsetDDl fsetUid fsetIid.
  Qed.

  Lemma valPE x (H : {fmap K -> V}) (xH : x \in domf H) : [` (valP [`xH]) ] = [` xH].
  Proof.
    by move: (valP _); rewrite [val _]/= => xH'; rewrite (bool_irrelevance xH' xH).
  Qed.
  

End Theory.


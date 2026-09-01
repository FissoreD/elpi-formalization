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
(*            [fmap] == the fmap0 finite map                                 *)
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

Notation fmap0 := [fmap].

Section Theory.
  Variables (K : countType) (V : eqType).
  Implicit Types c d  : ctx K V.

  Open Scope fset_scope.

  Lemma valPE x (H : {fmap K -> V}) (xH : x \in domf H) : [` (valP [`xH]) ] = [` xH].
  Proof.
    by move: (valP _); rewrite [val _]/= => xH'; rewrite (bool_irrelevance xH' xH).
  Qed.
  

End Theory.


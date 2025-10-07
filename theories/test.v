From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_prop elpi_valid_state elpi_equiv.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section main.
  Variable u: Unif.

  Lemma xx x xs s' r:
    valid_ca (x:::xs) -> nur u x.1 x.2 xs s' r -> valid_ca r.
  Proof.
    move=> H1 H2.
    apply: valid_state_valid_ca.                           
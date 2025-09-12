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

End Language.

Module Type Unif.
  Import Language.
  Parameter unify : Tm -> Tm -> Sigma -> option Sigma.
  Parameter matching : Tm -> Tm -> Sigma -> option Sigma.

    Inductive state :=
    | Bot : state
    | OK : state
    | Top : state
    | Dead : state
    | Goal : program  -> A -> state
    | Or  : state -> Sigma -> state -> state  (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
    | And : state -> state -> state -> state  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
    .

  Inductive G := 
    | call : program -> Tm -> G
    | cut : list (list G) -> G
    .

  Definition if_cut F g :=
    match g with
    | cut a => F a
    | _ => true
    end.

  Definition apply_cut F g :=
    match g with
    | cut a => cut (F a) 
    | _ => g
    end.


  Definition alt := (list G).

  Definition a2g p A :=
    match A with
    | Cut => cut [::]
    | Call t => call p t
    end.

  Definition a2gs p (b : Sigma * R) :=
    map (a2g p) b.2.(premises).

  Section add_ca.

    Definition add_ca alts a :=
      match a with
      | cut a1 => cut (a1 ++ alts)
      | call pr t => call pr t
      end.

    Lemma add_ca_empty {lA}:
      map (add_ca [::]) lA = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs IH.
      rewrite IH; case: x => // l; rewrite cats0//if_same//.
    Qed.

    Lemma map_add0_cas_empty {lA}:
      map (map (add_ca [::])) lA  = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs ->.
      f_equal; apply add_ca_empty.
    Qed.
  End add_ca.


  Definition save_alt a gs b := map (add_ca a) b ++ gs.
  Definition more_alt a bs gs := map (save_alt a gs) bs ++ a.
  Definition get_ca g :=
    match g with
    | cut a => a 
    | _ => [::]
    end.

  Definition is_cutb' A := match A with cut _ => true | _ => false end.
  Definition cuts' A := all is_cutb' A.

  Lemma cuts_cat {x y} : cuts' (x ++ y) = cuts' x && cuts' y.
  Proof. rewrite/cuts' all_cat//. Qed.

  Fixpoint add_ca_deep n tl (alts: seq (seq G)) := (*always:= adds always alts to cut *)
    match n with
    | 0 => alts
    | n.+1 => map (map (fun x => (add_ca tl (apply_cut (add_ca_deep n tl) x)))) alts
    end.

  (* Definition add_ca1 tl a := add_ca_deep (size a) tl a. *)

  Lemma add_ca_empty1 l: add_ca [::] l = l.
  Proof. case: l => //= l1; rewrite cats0//. Qed.

  Lemma map_add1_cas_empty {T: Type} (lA: list (list T)) F:
    map (map (fun x => add_ca [::] (F x))) lA  = map (map F) lA.
  Proof.
    rewrite /add_ca; elim: lA => //= x xs ->.
    f_equal; elim: x => //=x {}xs->; case: (F x)=>//=l; rewrite cats0//.
  Qed.

  Lemma cut_add_ca {l x}: is_cutb' (add_ca l x) = is_cutb' x.
  Proof. case: x => //=*. Qed.

  Lemma cuts_add_ca {x l} : cuts' [seq add_ca l j | j <- x] = cuts' x.
  Proof. elim: x l => // x xs H/= l; rewrite H cut_add_ca//. Qed.

  Definition add_suff (bt: seq alt) hd (l:seq alt) :=
    let s := size l - size bt in
    map (fun x => x ++ hd) (take s l) ++ drop s l.

  Definition add_deep_help add_deep bt (n:nat) hd :=
    apply_cut (fun x => add_suff bt hd (add_deep bt n hd x)).

  Fixpoint add_deep bt n (l: alt) (A: seq alt) :=
    match n with
    | 0 => A
    | n.+1 =>
      map (map (add_deep_help add_deep bt n l)) A
    end. 

  Definition add_deep_ bt n (l: alt) (A: alt) :=
    match n with
    | 0 => A
    | n.+1 => (map (add_deep_help add_deep bt n l)) A
    end.

  Definition kill (A: alt) := map (apply_cut (fun x => [::])) A.

  Definition make_lB0 (xs:seq alt) (lB0: alt) := map (fun x => x ++ lB0) xs.

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

  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
    | OK => [::[::]]
    | Top => [::[::]]
    | Bot => [::]
    | Dead => [::]
    | Goal _ Cut => [::[::cut [::]]]
    | Goal pr (Call t) => [::[::call pr t]]
    | Or A _ B => 
      let lB := state_to_list B [::] in
      let lA := state_to_list A lB in
      add_ca_deep (size (lA ++ lB)) bt (lA ++ lB)
    | And A B0 B =>
      let lB0 := state_to_list B0 bt in
      let lA   := state_to_list A bt in
      if lA is x :: xs then 
        (* lA is split into the current goal x and the future alternatives xs *)
        (* in a valid state lB0 has length 0 or 1 (it is a (potentially killed) base and) *)
        match lB0 with
        | [::] => 
          (* the reset point is empty: it kill all the alternatives in the cut-to *)
          let lB   := state_to_list B bt in
          [seq (kill x) ++ y | y <- lB]
        | [::hd] =>
        (* 
          invariant every cut-to has bt has tail or is empty
        *)
          (* the reset point exists, it has to be added to all cut-to alternatives *)
          let x := add_deep_ bt (size xs).+1 hd x in
          let xs := add_deep bt (size xs) hd xs in 
          (* each alt in xs must have hd has rightmost conjunct  *)
          let xs := make_lB0 xs hd in
          (* xs are alternatives that should be added in the deep cuts in B *)
          let lB   := state_to_list B (xs ++ bt) in
          (* lB are alternatives, each of them have x has head *)
          [seq x ++ y | y <- lB] ++ xs
        | _ => [::] (*unreachable in a valid_state*)
        end
      else [::]
    end.

    Require Import Extraction.
    Extract Inductive unit => "unit" [ "()" ].
    Extract Inductive bool => "bool" [ "true" "false" ].
    Extract Inductive sumbool => "bool" [ "true" "false" ].
    Extract Inductive list => "list" [ "[]" "(::)" ].
    Extract Inductive prod => "(*)"  [ "(,)" ].
    Extract Inductive option => "option"  [ "None" "Some" ].
    Extraction "code.ml" state_to_list.
End Unif.



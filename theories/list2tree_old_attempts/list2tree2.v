From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Search exapnedb failed.

Fixpoint a2t_ l :=
  match l with
  | nilA => Bot
  | consA (s, x) xs =>
    Or (a2t_ xs) s (gs2t_ x)
  end
with gs2t_ l :=
  match l with
  | nilG => Top
  | consG x xs => 
    match (g2t_ x) with
    | (x, None) => And (gs2t_ xs) x x
    | (x, Some _) => And (gs2t_ xs) x x
    end
  end
with g2t_ l :=
  match l with
  | cut ca => (CutS, Some (a2t_ ca))
  | call p t => (CallS p t, None)
  end.

Definition a2t (l:alts) := a2t_ (rev (map (fun '(s,x) => (s, rev x)) l)).

Fixpoint of_goals l :=
  match l with
    | [::] => nilC
    | cut l :: xs => (cut l) ::: (of_goals xs)
    | (call _ _ as hd) :: xs => hd ::: (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => -nilCA
  | x :: xs => (empty, of_goals x) ::: (of_alt xs)
  end.

Section s.
  Variable p : program.
  Variable c1 : Callable.
  Variable c2 : Callable.
  Variable A B C D E F : Callable.
  Variable s : Sigma.
  Definition c := call p (c1).
  Definition q := call p (c2).

  Goal exists x, (a2t ((s, (c ::: (q:::nilC))) ::: nilC)) = x.
  Proof. move=> /=. Admitted.

  Goal exists x, a2t ((s, (c ::: nilC)) ::: ((s, (q ::: nilC)) ::: nilA)) = x.
  Proof. move=> /=. Admitted.

  Goal
  (* original is (((! \/ A) \/ B)) /\ (D) *)
  (* produced is ((bot \/ !D) \/ AC) \/ BC *)
    exists x, 
    let f x := (CallS p x) in
      a2t ((of_alt [:: 
        [::cut (of_alt [:: [:: call p B; call p C]]); call p D];
        [:: call p A; call p C]; 
        [:: call p B; call p C]])) = x.
  Proof.
    simpl of_alt.
    move=>/=.
    set X:= And Top _ _.
    set Y:= And X _ _.
    set Z := Or KO _ _.
    set X1:= And Top _ _.
    set Y1:= And X1 _ _.
    set Z1 := Or Z _ _.
    set X2:= And Top _ _.
    set Y2:= And X2 _ _.
    set Z2 := Or Z1 _ _.
  Abort.
  
  Goal
  let f x := (CallS p x) in
  (* original is (OK \/_{empty} B) /\_C ((! \/_{empty} A) /\_{E} D) *)
  (* produced is *)
  (* ((bot \/ !D) \/ DE) \/ BC *)
    exists x, a2t
    (of_alt [:: 
      [:: cut (of_alt [:: [:: call p B; call p C]]); call p D];
      [:: call p A; call p E]; 
      [:: call p B; call p C]]) = x.
  Proof.
    move=>/=.
    set X:= And Top _ _.
    set Y:= And X _ _.
    set Z := Or KO _ _.
    set X1:= And Top _ _.
    set Y1:= And X1 _ _.
    set Z1 := Or Z _ _.
    set X2:= And Top _ _.
    set Y2:= And X2 _ _.
    set Z2 := Or Z1 _ _.
  Abort.

  Goal
  (* original (OK \/ A) /\_B OK *)
  (* produces is : (KO \/ Top) \/ AB *)
  let f x := (CallS p x) in
  a2t (of_alt [::[::]; [::call p A; call p B]]) = 
    Or (Or KO empty Top) empty
    (And (And Top (CallS p A) (CallS p A)) (CallS p B) (CallS p B)).
  Proof.
    move=>/=.
    set X:= And Top _ _.
    set Y:= And X _ _.
    set Z := Or KO _ _.
    move=>//.
  Qed.

  Goal
    let f x := (CallS p x) in
    (*  original is (KO \/ A) /\B (C \/ D) *)
    (* produces is ((KO \/ (AC)) \/ (AD)) *)
    exists x, a2t
      (of_alt [:: [:: call p A; call p C]; [::call p A; call p D] ]) = x.
  Proof.
    move=>/=.
    set X:= And Top _ _.
    set Y:= And X _ _.
    set Z := Or KO _ _.
  Abort.
End s.

Module remake.

  Fixpoint add_rotate s x xs :=
    match xs with
    | Or KO s1 r => Or (Or KO s x) s1 r
    | Or l s1 r => Or (add_rotate s x l) s1 r
    | _ => Dead (*TODO: should be unreachable?*)
    end.

  (* SBAGLIATO, vedi esempio XY *)
  Fixpoint add_and_leaf x t :=
    match t with
    | Or KO s1 r => Or KO s1 (And x r r)
    | Or l s1 r => Or (add_and_leaf x l) s1 r
    | _ => Dead (*TODO: should be unreachable?*)
    end.

  (* TODO: make n odd rotations untill reaching a or with same cut-to as ca  *)
  (* Definition leverage ca t :=
    if 
    match t with
    |  *)

  Fixpoint a2t_ l :=
    match l with
    | nilA => Bot
    | consA (s, x) xs => gs2t_ s x (a2t_ xs)
    end
  with gs2t_ s l t :=
    match l with
    | nilG => add_rotate s Top t
    | consG x xs => 
      let tl := gs2t_ s xs t in
      let '(node, bt) := g2t_ x in
      match bt with
      | None => add_and_leaf node tl
      | Some _ => add_and_leaf node tl
      end
    end
  with g2t_ l :=
    match l with
    | cut ca => (CutS, Some (a2t_ ca))
    | call p t => (CallS p t, None)
    end.

  Section s.
    Variable p : program.
    Variable c1 : Callable.
    Variable c2 : Callable.
    Variable A B C D E F : Callable.
    Variable s : Sigma.
    Definition c := call p (c1).
    Definition q := call p (c2).

    Goal exists x, (a2t ((s, (c ::: (q:::nilC))) ::: nilC)) = x.
    Proof. move=> /=. Admitted.

    Goal exists x, a2t ((s, (c ::: nilC)) ::: ((s, (q ::: nilC)) ::: nilA)) = x.
    Proof. move=> /=. Admitted.

    Goal
    (* original is (((! \/ A) \/ B)) /\_C (D) *)
    (* produced is ((bot \/ !D) \/ AC) \/ BC *)
    (* expected is ((bot \/ (!D \/ AC) \/ BC *)
      exists x, 
      let f x := (CallS p x) in
        a2t ((of_alt [:: 
          [::cut (of_alt [:: [:: call p B; call p C]]); call p D];
          [:: call p A; call p C]; 
          [:: call p B; call p C]])) = x.
    Proof.
      simpl of_alt.
      move=>/=.
      set X:= And Top _ _.
      set Y:= And X _ _.
      set Z := Or KO _ _.
      set X1:= And Top _ _.
      set Y1:= And X1 _ _.
      set Z1 := Or Z _ _.
      set X2:= And Top _ _.
      set Y2:= And X2 _ _.
      set Z2 := Or Z1 _ _.
    Abort.
    
    Goal
    let f x := (CallS p x) in
    (* original is (OK \/_{empty} B) /\_C ((! \/_{empty} A) /\_{E} D) *)
    (* produced is ((bot \/ !D) \/ DE) \/ BC *)
    (* expected is (bot \/ (!D \/ DE) \/ BC *)
      exists x, a2t
      (of_alt [:: 
        [:: cut (of_alt [:: [:: call p B; call p C]]); call p D];
        [:: call p A; call p E]; 
        [:: call p B; call p C]]) = x.
    Proof.
      move=>/=.
      set X:= And Top _ _.
      set Y:= And X _ _.
      set Z := Or KO _ _.
      set X1:= And Top _ _.
      set Y1:= And X1 _ _.
      set Z1 := Or Z _ _.
      set X2:= And Top _ _.
      set Y2:= And X2 _ _.
      set Z2 := Or Z1 _ _.
    Abort.

    Goal
    (* original (OK \/ A) /\_B OK *)
    (* produces is : (KO \/ Top) \/ AB *)
    let f x := (CallS p x) in
    a2t (of_alt [::[::]; [::call p A; call p B]]) = 
      Or (Or KO empty Top) empty
      (And (And Top (CallS p A) (CallS p A)) (CallS p B) (CallS p B)).
    Proof.
      move=>/=.
      set X:= And Top _ _.
      set Y:= And X _ _.
      set Z := Or KO _ _.
      move=>//.
    Qed.

    Goal
      let f x := (CallS p x) in
      (*  original is (KO \/ A) /\B (C \/ D) *)
      (* produces is ((KO \/ (AC)) \/ (AD)) *)
      exists x, a2t
        (of_alt [:: [:: call p A; call p C]; [::call p A; call p D] ]) = x.
    Proof.
      move=>/=.
      set X:= And Top _ _.
      set Y:= And X _ _.
      set Z := Or KO _ _.
    Abort.
    
  End s.
  



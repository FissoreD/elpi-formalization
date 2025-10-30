From mathcomp Require Import all_ssreflect.
From det Require Import run.
From det Require Import zify_ssreflect.

Section RunP.
  Variable u: Unif.

  Lemma ges_subst_cutl {s A} : get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//.
    - move=> A HA B0 _ B HB s; case:ifP; rewrite success_cut => sA; rewrite sA HA//.
  Qed.

  Definition choose_cutl b1 A := (if (b1 == 0) then A else cutl A).
  
  Lemma choose_cutl_id {A}: choose_cutl 0 A = A.
  Proof. rewrite/choose_cutl eqxx//. Qed.

  Lemma choose_cutl_cutl {b2 A}: choose_cutl b2 (cutl A) = (cutl A).
  Proof. rewrite/choose_cutl cutl2 if_same//. Qed.

  Lemma choose_cutl_lt {b2 A}: 0 < b2 -> choose_cutl b2 A = cutl A.
  Proof. rewrite/choose_cutl; case: eqP => //; lia. Qed.

  Lemma expand_cutl_cb {s C s' B}: expand u s (cutl C) = CutBrothers s' B -> False.
  Proof.
    elim: C s s' B=> //=.
    - move=> A HA s B HB s1 s2 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA; case expand => //.
    - move=> A HA B0 _ B HB s1 s2 C.
      case e: expand => //[s1' A'|s1' A'].
        by have:= HA _ _ _ e.
      case f: expand => //[s1'' B'].
      by have:= HB _ _ _ f.
  Qed.

  Lemma expand_cutl_exp {s C s' B}: expand u s (cutl C) = Expanded s' B -> False.
  Proof.
    elim: C s s' B=> //=.
    - move=> A HA s B HB s1 s2 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA.
        case X: expand => //=.
          by have:= HB _ _ _ X.
        by have:= expand_cutl_cb X.
      case X: expand => //.
        by have:= HA _ _ _ X.
      by have:= expand_cutl_cb X.
    - move=> A HA B0 _ B HB s1 s2 C.
      case e: expand => //[s1' A'|s1' A'].
        by have:= HA _ _ _ e.
      case f: expand => //[s1'' B'].
      by have:= HB _ _ _ f.
  Qed.
End RunP.
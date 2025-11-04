From mathcomp Require Import all_ssreflect.
From det Require Import run.
From det Require Import zify_ssreflect.

Section RunP.
  Variable u: Unif.

  (* Lemma ges_subst_cutr {s A} : get_substS s (cutr A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; rewrite is_dead_cutr HA HB//.
    - move=> A HA B0 _ B HB s; rewrite success_cutr HA; case: ifP => //.
        rewrite success_cut sA/=HA//.
      rewrite success_cutr.
        rewrite success_cut => sA; rewrite sA HA//.
  Qed. *)

  Lemma ges_subst_cutl {s A} : 
    success A -> get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//; auto.
    - move=> A HA B0 _ B HB s /andP[sA sB]; rewrite sA/=success_cut sA HA// HB//.
  Qed.

  Definition choose_cutl b1 A := (if (b1 == 0) then A else cutl A).
  
  Lemma choose_cutl_id {A}: choose_cutl 0 A = A.
  Proof. rewrite/choose_cutl eqxx//. Qed.

  Lemma choose_cutl_cutl {b2 A}: choose_cutl b2 (cutl A) = (cutl A).
  Proof. rewrite/choose_cutl cutl2 if_same//. Qed.

  Lemma choose_cutl_lt {b2 A}: 0 < b2 -> choose_cutl b2 A = cutl A.
  Proof. rewrite/choose_cutl; case: eqP => //; lia. Qed.

  Lemma expand_cutl_cb {s C B}: expand u s (cutl C) = CutBrothers B -> False.
  Proof.
    elim: C s B=> //=.
    - move=> A HA s B HB s1 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA; case expand => //.
    - move=> A HA B0 _ B HB s1 C.
      case:ifP => sA//=.
        case X: expand => //=[A'|A'].
          by have:= HA _ _ X.
        case e: expand => //[ A''].
        by have:= HB _ _ e.
      rewrite is_ko_expand//is_ko_cutr//.
  Qed.

  Lemma expand_cutl_exp {s C B}: expand u s (cutl C) = Expanded B -> False.
  Proof.
    elim: C s B=> //=.
    - move=> A HA s B HB s1 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA.
        case X: expand => //=.
          by have:= HB _ _ X.
        by have:= expand_cutl_cb X.
      case X: expand => //.
        by have:= HA _ _ X.
      by have:= expand_cutl_cb X.
    - move=> A HA B0 _ B HB s1 C.
      case:ifP => sA/=.
        case e: expand => //[A'|A'].
          by have:= HA _ _ e.
        case X: expand => //[B'].
        by have:= HB _ _ X.
      rewrite is_ko_expand//is_ko_cutr//.
  Qed.
End RunP.
Require Export Circle.
Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Definition S1_to_S1' : S1 → S1' :=
  (S1_recur S1' north_pole (p1 @ p2)).

Definition S1'_to_S1 : S1' → S1 :=
  (S1'_recur S1 base base loop (idpath base)).

Definition f (x : S1) : S1 := S1'_to_S1 (S1_to_S1' x).

Theorem S1_equiv : S1 ≃ S1'.
Proof.
  use weq_iso.
  + exact S1_to_S1'.
  + exact S1'_to_S1.
  + use S1_ind.
    - simpl. auto.
    - rewrite transportf_paths_FlFr. simpl.
      etrans. { apply maponpaths_2. apply maponpaths. symmetry.
                apply (@maponpathscomp S1 S1' S1 base base 
                  S1_to_S1' S1'_to_S1 loop). }
      unfold S1_to_S1'.
      unfold S1'_to_S1.
      rewrite (S1_recur_loop S1' north_pole (p1 @ p2)).
      etrans. { apply maponpaths_2.
                apply maponpaths.
                apply (maponpathscomp0 
                  (S1'_recur S1 base base loop (idpath base)) p1 p2). }
      rewrite (S1'_recur_p1 S1 base base loop (idpath base)).
      rewrite (S1'_recur_p2 S1 base base loop (idpath base)). simpl.
      etrans. { apply maponpaths.
                apply maponpathsidfun. } simpl.
      rewrite pathscomp0rid.
      apply pathsinv0l.
  + simpl. use S1'_ind.
    - simpl. exact (idpath north_pole).
    - simpl. exact (! p2).
    - rewrite transportf_paths_FlFr. simpl.
      etrans. { apply maponpaths_2.
                apply maponpaths. symmetry.
                apply (@maponpathscomp S1' S1 S1' north_pole south_pole 
                  S1'_to_S1 S1_to_S1' p1). }
      unfold S1'_to_S1.
      rewrite (S1'_recur_p1 S1 base base loop (idpath base)).
      unfold S1_to_S1'.
      etrans. { apply maponpaths_2. apply maponpaths. 
                apply (S1_recur_loop S1' north_pole (p1 @ p2)). }
      etrans. { apply maponpaths.
                apply maponpathsidfun. } simpl.
      etrans. { apply maponpaths_2.
                apply pathscomp_inv. }
      rewrite <- path_assoc.
      etrans. { apply maponpaths.
                apply pathsinv0l. }
      apply pathscomp0rid.
    - rewrite transportf_paths_FlFr. simpl.
      etrans. { apply maponpaths_2.
                apply maponpaths. symmetry.
                apply (@maponpathscomp S1' S1 S1' south_pole 
                  north_pole S1'_to_S1 S1_to_S1' p2). }
      unfold S1'_to_S1.
      rewrite (S1'_recur_p2 S1 base base loop (idpath base)).
      unfold S1_to_S1'.
      etrans. { apply maponpaths_2.
                apply maponpaths.
                apply (@maponpaths_idpath S1 S1' 
                  (S1_recur S1' north_pole (p1 @ p2)) base). }
      etrans. { apply maponpaths.
                apply maponpaths.
                apply maponpathsidfun. } simpl. 
      apply pathsinv0l.
Qed.

Search (Type -> UU).

Check (univalenceUAH univalenceAxiom S1 S1').
(* Check (weqinvweq (S1 = S1') ((S1 ≃ S1'))). *)
Check univalence.

Check (pr1weq (weqinvweq (S1 = S1') ((S1 ≃ S1')))).

Check ((pr1weq (weqinvweq (S1 = S1') ((S1 ≃ S1')))) (univalence S1 S1')).


Require Export Circle.
Require Export Suspension.
Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Definition S1_to_Susp : S1 → Suspension Two :=
  (S1_recur (Suspension Two) (North Two) (merid On @ !(merid Tw))).

Definition Two_toPaths : Two → base = base.
Proof.
  use Two_rect.
  - simpl. exact loop.
  - exact (idpath base).
Defined. 

Definition Susp_to_S1 : Suspension Two → S1 :=
  (Suspension_recur S1 base base Two_toPaths).

Definition Circle_Suspension_Equiv : S1 ≃ Suspension Two.
Proof.
  use weq_iso.
  - exact S1_to_Susp.
  - exact Susp_to_S1.
  - use S1_ind.
    + simpl. auto.
    + rewrite transportf_paths_FlFr. simpl.
      etrans. { apply maponpaths_2. apply maponpaths. symmetry.
                apply (@maponpathscomp S1 (Suspension Two) S1 base base 
                  S1_to_Susp Susp_to_S1 loop). }
      unfold S1_to_Susp.
      unfold Susp_to_S1.
      rewrite (S1_recur_loop (Suspension Two) (North Two) (merid On @ !merid Tw)).
      etrans. { apply maponpaths_2.
                apply maponpaths.
                apply (maponpathscomp0 
                  (Suspension_recur S1 base base Two_toPaths) (merid On) (!merid Tw)). }
      rewrite (@Suspension_recur_merid Two On S1 base base Two_toPaths).
      etrans. { apply maponpaths_2.
              apply maponpaths.
              apply maponpaths.
              apply maponpathsinv0. }
      rewrite (@Suspension_recur_merid Two Tw S1 base base Two_toPaths). simpl.
      
      etrans. { apply maponpaths. apply maponpathsidfun. } simpl.
      rewrite pathscomp0rid.
      apply pathsinv0l.
  - use Suspension_ind.
    + simpl. exact (idpath (North Two)).
    + simpl. exact (merid Tw).
    + intro. induction x.
      * rewrite transportf_paths_FlFr. simpl.
        etrans. { apply maponpaths_2.
                  apply maponpaths. symmetry.
                  apply (@maponpathscomp (Suspension Two) S1 (Suspension Two) (North Two) (South Two) 
                    Susp_to_S1 S1_to_Susp (merid On)). }
        unfold Susp_to_S1.
        rewrite (@Suspension_recur_merid Two On S1 base base Two_toPaths).
        unfold S1_to_Susp.
        etrans. { apply maponpaths_2. apply maponpaths. 
                  apply (S1_recur_loop (Suspension Two) (North Two) (merid On @ !merid Tw)). }
        etrans. { apply maponpaths.
                  apply maponpathsidfun. } simpl.
        etrans. { apply maponpaths_2.
                  apply pathscomp_inv. }
        rewrite <- path_assoc.
        etrans. { apply maponpaths.
                  apply pathsinv0l. }
        etrans. { apply maponpaths_2.
                  apply pathsinv0inv0. }
        apply pathscomp0rid.
      * rewrite transportf_paths_FlFr. simpl.
        etrans. { apply maponpaths_2.
                  apply (pathsinv0 (@maponpathsinv0 (Suspension Two) (Suspension Two) (λ x : Suspension Two, S1_to_Susp (Susp_to_S1 x)) (North Two) (South Two)  (merid Tw))). }
        etrans. { apply maponpaths_2.
                  apply (pathsinv0 (@maponpathscomp (Suspension Two) S1 (Suspension Two) (South Two) (North Two) Susp_to_S1 S1_to_Susp  (!merid Tw))). }
        unfold Susp_to_S1.
        etrans. { apply maponpaths_2.
                  apply maponpaths.
                  apply (maponpathsinv0 (Suspension_recur S1 base base Two_toPaths) (merid Tw)). }
        rewrite (@Suspension_recur_merid Two Tw S1 base base Two_toPaths).
        unfold S1_to_Susp. unfold Two_toPaths. simpl.
        etrans. { apply maponpathsidfun. } auto.
Qed.
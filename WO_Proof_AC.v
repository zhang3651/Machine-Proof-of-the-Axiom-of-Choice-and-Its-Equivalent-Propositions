(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export Wellordering_Theorem.

(** The proof of AC **)

Definition En_CF X le := \{\ λ x y, x ∈ (pow(X)~[Φ]) /\ y∈x /\ 
  (exists z0, MinElement z0 x le /\ y = z0) \}\.

Theorem WellOrder_AC : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  generalize (classic (X = Φ)); intros; destruct H0.
  (* X = Φ 的情况 *)
  - rewrite H0; exists Φ; unfold Choice_Function; repeat split; intros.
    + unfold Relation; intros; feine z; auto.
    + feine ([x,y]); auto.
    + unfold Included; intros; unfold Range in H1.
      apply AxiomII in H1; destruct H1, H2; feine ([x,z]); auto.
    + apply AxiomI; split; intros.
      * unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
        feine ([z,x]); auto.
      * unfold Setminus in H1; apply MKT4' in H1; destruct H1.
        unfold Complement in H2; apply AxiomII in H2; destruct H2.
        unfold PowerClass in H1; apply AxiomII in H1; destruct H1.
        assert(z ⊂ Φ /\ Φ ⊂ z); auto; clear H4; rename H5 into H4.
        try (apply MKT26); apply MKT27 in H4.
        assert (z ∈ [Φ]). { apply AxiomII; split; auto. }
        contradiction.
    + unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
      feine ([A,x]); auto.
  (* X ≠ Φ 的情况 *)
  - New H; apply WellOrderMKT in H1.
    destruct H1 as [le H1]; unfold WellOrder in H1; destruct H1.
    exists (En_CF X le); unfold Choice_Function.
    assert (Function (En_CF X le)).
    { unfold Function; split; intros.
      - unfold Relation; intros; PP H3 x y; exists x, y; auto.
      - apply AxiomII' in H3; apply AxiomII' in H4.
        destruct H3, H4, H5, H6, H7, H8, H9, H10, H9, H10.
        unfold TotalOrder in H1; destruct H1.
        assert (y ∈ X /\ z ∈ X).
        { unfold Setminus in H5; apply MKT4' in H5; destruct H5.
          apply AxiomII in H5; destruct H5; split; auto. }
        generalize (classic (y = z)); intros; destruct H15; auto.
        apply H13 in H14; auto; clear H15.
        assert (x ≠ Φ). (* 要使用最小元素条件，所以要证明 x ≠ Φ *)
        { generalize (classic (x ≠ Φ)); intros; destruct H15; auto.
          apply NNPP' in H15; rewrite H15 in H7.
          feine y; auto. }
        unfold MinElement in H9, H10; destruct H9, H10, H14; auto.
        + rewrite <- H12 in H17; apply H17 in H7.
          apply notandor in H7; destruct H7; try contradiction.
          apply NNPP' in H7; symmetry; auto.
        + rewrite <- H11 in H16; apply H16 in H8.
          apply notandor in H8; destruct H8; try contradiction.
          apply NNPP' in H8; symmetry; auto. }
    split; auto; repeat split; intros.
    + unfold Included; intros; apply AxiomII in H4.
      destruct H4, H5 as [y H5]; apply AxiomII' in H5.
      destruct H5, H6, H7; clear H8; unfold Setminus in H6.
      apply MKT4' in H6; destruct H6; clear H8.
      apply AxiomII in H6; destruct H6; auto.
    + apply AxiomI; intro A; split; intros.
      * apply AxiomII in H4; destruct H4, H5 as [y H5].
        apply AxiomII' in H5; apply H5.
      * apply AxiomII; split; unfold Ensemble; eauto; New H4.
        unfold Setminus in H5; apply MKT4' in H5; destruct H5.
        apply AxiomII in H5; destruct H5; unfold Complement in H6.
        apply AxiomII in H6; destruct H6; clear H6; unfold NotIn in H8.
        assert (A ∈ [Φ] <-> Ensemble A /\ (Φ ∈ μ -> A = Φ)).
        { split; intros.
          - unfold Singleton in H5; apply AxiomII in H6; auto.
          - unfold Singleton; apply AxiomII; auto. }
        assert(~ (Ensemble A /\ (Φ ∈ μ -> A = Φ))).
        { unfold not; intros; apply H8; apply H6; auto. }
        clear H8 H6; rename H9 into H6.
        apply notandor in H6; destruct H6; try contradiction.
        apply imply_to_and in H6; destruct H6; clear H6.
        assert (A ⊂ X /\ A ≠ Φ). { split; auto. }
        apply H2 in H6; destruct H6 as [z0 H6]; New H6.
        unfold MinElement in H9; apply H9 in H8; clear H9; destruct H8.
        exists z0; apply AxiomII'; repeat split; auto.
        -- apply MKT49a; unfold Ensemble; eauto.
        -- exists z0; auto.
    + New H4; apply Property_Value in H4; auto; unfold Domain in H5.
      apply AxiomII in H5; destruct H5, H6 as [y H6]; New H6.
      apply AxiomII' in H7; destruct H7, H8, H9; clear H10.
      unfold Function in H3. destruct H3.
      apply (H10 A ((En_CF X le) [A]) y) in H6; auto.
      rewrite H6; auto.
Qed.

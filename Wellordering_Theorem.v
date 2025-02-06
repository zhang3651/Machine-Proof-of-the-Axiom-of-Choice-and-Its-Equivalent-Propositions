(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Zorn_Lemma.


(** Well-Ordering MKT **)

Definition En_L X := \{\ λ Y le, Y ⊂ X /\ Y ≠ Φ /\ WellOrder le Y\}\.

Definition lee X: Class :=
  \{\ λ L1 L2, (L1 ∈ (En_L X) /\ L2 ∈ (En_L X)) /\
  (forall x y, x∈(First L1) /\ y∈(First L1) ->
  (Rrelation x (Second L1) y <-> Rrelation x (Second L2) y)) /\
  Initial_Segment (First L1) (First L2) (Second L2) \}\.

Definition En_Z K := \{ λ x, exists Y le, [Y,le] ∈ K /\ x∈Y \}.

Definition leeq K : Class :=
  \{\ λ u v, exists Y le, [Y,le] ∈ K /\ u∈Y /\ v∈Y /\ Rrelation u le v \}\.

Definition leep Y le x :=
  \{\ λ y1 y2, (y1∈Y /\ y2∈Y /\ Rrelation y1 le y2) \/ (y1∈(Y∪[x]) /\ y2=x) \}\.

Definition leq Y := \{\ λ y1 y2, y1∈Y /\ y2∈Y /\ y1 = y2 \}\.

Lemma Property_lee : forall Y1 Y2 le1 le2,
  Ensemble ([[Y1, le1],[Y2, le2]]) -> First ([Y1,le1]) = Y1 /\
  Second ([Y1,le1]) = le1 /\ First ([Y2,le2]) = Y2 /\ Second ([Y2,le2]) = le2.
Proof.
  intros.
  apply MKT49b in H; destruct H.
  apply MKT49b in H; destruct H.
  New H1. apply (MKT54a Y1) in H1; apply (MKT54b Y1) in H2; auto.
  apply MKT49b in H0; destruct H0.
  New H3; apply (MKT54a Y2) in H3; apply (MKT54b Y2) in H4; auto.
Qed.

Lemma Lemma_WP1 : forall X, Ensemble X -> PartialOrder (lee X) (En_L X).
Proof.
  intros.
  unfold PartialOrder; repeat split.
  - assert (Ensemble (pow(X)× pow(X×X))).
    { New H; apply MKT38a in H0; auto; apply MKT74; auto. 
      apply MKT38a; auto; apply (MKT74 H) in H; auto. }
    apply MKT33 with (x:= pow(X)× pow(X×X)); auto.
    unfold Included; intros; PP H1 Y0 le0.
    destruct H3, H3. unfold WellOrder in H4; destruct H4.
    unfold TotalOrder in H4; destruct H4; clear H6.
    unfold PartialOrder in H4; destruct H4, H6, H6.
    unfold Cartesian; apply AxiomII'; repeat split; auto.
    + unfold PowerClass; apply AxiomII; split; auto.
    + unfold PowerClass; apply AxiomII; split; auto.
      * apply MKT33 in H8; auto; apply MKT74; auto.
      * unfold Included; intros; apply H8 in H9; PP H9 u v. destruct H11.
        apply AxiomII'; repeat split; auto.
  - unfold Relation; intros; PP H0 x y; unfold Ensemble; eauto.
  - unfold Included; intros; PP H0 u v.
    destruct H2, H1, H2. apply AxiomII'; auto.
  - unfold Reflexivity; intros; New H0; unfold En_L in H1.
    PP H1 u v; unfold Rrelation, lee; apply AxiomII'.
    assert (Ensemble ([u,v])). { unfold Ensemble; eauto. }
    split; try apply MKT49; auto; apply MKT49b in H2.
    destruct H2; New H4; apply (MKT54a u) in H4; apply (MKT54b u) in H5; auto. 
    rewrite H5, H4; clear H5 H4.
    split; unfold Ensemble; eauto; split; intros.
    + split; intros; auto.
    + unfold Initial_Segment; split; try (unfold Included; auto).
      destruct H3, H4; split; try apply H5; intros; apply H6.
  - unfold Antisymmetry; intros; destruct H1.
    unfold Rrelation, lee in H1, H2; apply AxiomII' in H1.
    apply AxiomII' in H2; destruct H1, H2, H3, H4; clear H2 H3 H4.
    destruct H0; PP H0 Y1 le1; PP H2 Y2 le2.
    New H1; apply Property_lee in H1.
    destruct H1, H8, H9; rewrite H1, H8, H9, H10 in H5, H6; clear H1 H8 H9 H10.
    New H0; apply MKT49b in H0. apply MKT49b in H1.
    apply MKT55; destruct H1; auto; destruct H5, H6, H9, H10, H11, H12.
    split. apply MKT27; auto.
    clear H13 H14; unfold WellOrder in H12, H11; destruct H12, H11.
    clear H13 H14; unfold TotalOrder in H12, H11; destruct H12, H11.
    clear H13 H14; unfold PartialOrder in H12, H11; destruct H12, H11.
    clear H11 H12; destruct H13, H14. clear H12 H14; destruct H13, H11.
    clear H1 H2 H3 H4 H7 H8; rename H5 into H1; rename H9 into H2; 
    rename H6 into H3; rename H10 into H4; rename H12 into H5; 
    rename H13 into H6; rename H11 into H7; rename H14 into H8.
    apply AxiomI; split; intros.
    + New H9; unfold Included in H8; apply H8 in H10; PP H10 x y.
      apply H1 in H12; unfold Rrelation in H12; apply H12; auto.
    + New H9; unfold Included in H8; apply H6 in H10; PP H10 x y.
      apply H3 in H12; unfold Rrelation in H12; apply H12; auto.
  - clear H; unfold Transitivity; intros; destruct H, H0.
    elim H; intros; destruct H3; unfold En_L in H2, H3, H4.
    PP H2 Y1 le1; PP H3 Y2 le2; PP H4 Y3 le3.
    unfold Rrelation; unfold lee; apply AxiomII'.
    unfold Rrelation in H0, H1; unfold lee in H0, H1.
    apply AxiomII' in H0; apply AxiomII' in H1; destruct H0, H1; split.
    + apply MKT49b in H0; apply MKT49b in H1; destruct H, H1.
      apply MKT49a; auto.
    + apply Property_lee in H0; apply Property_lee in H1.
      destruct H0, H1, H10, H11, H13.
      rewrite H0, H10, H1, H11 in H5; rewrite H1, H11, H13, H14 in H9.
      rewrite H0, H13, H14. destruct H5, H9.
      destruct H, H17. split; auto. destruct H15, H16.
      unfold Initial_Segment in H19, H20. 
      destruct H19, H20, H21, H22; split; intros.
      * elim H25; intros; unfold Included in H19; apply H19 in H26.
        apply H19 in H27.
        assert(x ∈ Y2 /\ y ∈ Y2); auto; clear H26; rename H27 into H26.
        apply H16 in H28.
        apply H15 in H25; split; intros. 
        rewrite H10 in H27.
        tauto.
        rewrite H10.
        tauto.
      * New H0.
        apply (MKT28 H19) in H20.
        unfold Initial_Segment; repeat split; try apply H22; auto; intros.
        apply H23 with (v:=v); destruct H26, H27; assert (u ∈ Y2).
        { apply H24 with (v:=v); unfold Included in H19.
          apply H19 in H27; repeat split; auto. }
        repeat split; auto; unfold Included in H19; apply H19 in H27.
        assert(u ∈ Y2 /\ v ∈ Y2); auto; clear H29; rename H30 into H29.
        apply H16 in H29; apply H29; auto.
Qed.

Lemma Lemma_WP2 : forall (X K : Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> WellOrder (leeq K) (En_Z K).
Proof.
  intros; New H.
  unfold Chain in H0; apply (Lemma_WP1 X) in H1; apply H0 in H1.
  clear H0; destruct H1; unfold WellOrder; split.
  - unfold TotalOrder; split; intros.
    { unfold PartialOrder; repeat split.
      - assert ((En_Z K) ⊂ X).
        { unfold Included; intros; unfold En_Z in H2.
          apply AxiomII in H2; destruct H2, H3 as [Y [le H3]], H3.
          destruct H0; unfold Included in H0; apply H0 in H3.
          unfold En_L in H3; apply AxiomII' in H3; destruct H3, H6.
          unfold Included in H6; apply H6 in H4; auto. }
        apply MKT33 in H2; auto.
      - unfold Relation; intros; PP H2 Y0 le0; unfold Ensemble; eauto.
      - unfold Included; intros; PP H2 Y0 le0.
        destruct H4, H3, H3, H4, H5; apply AxiomII'.
        repeat split; try (apply AxiomII; split); unfold Ensemble; eauto.
      - unfold Reflexivity; intros; unfold En_Z in H2; apply AxiomII in H2.
        unfold Rrelation, leeq; apply AxiomII'; destruct H2.
        destruct H3 as [Y [le H3]], H3; split; try apply MKT49; auto.
        exists Y, le; repeat split; auto; unfold Included in H0.
        apply H0 in H3; unfold En_L in H3; apply AxiomII' in H3.
        destruct H3, H5; unfold WellOrder in H6; destruct H6; clear H6.
        destruct H7; clear H7; unfold TotalOrder in H6; destruct H6; clear H7.
        unfold PartialOrder in H6; destruct H6, H7, H8; clear H9.
        unfold Reflexivity in H8; apply H8; auto.
      - unfold Antisymmetry; intros; destruct H3; apply AxiomII' in H3.
        apply AxiomII' in H4; destruct H3, H4; clear H4.
        destruct H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]].
        destruct H5, H6, H5, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1,le1])). { unfold Ensemble; eauto. }
          apply MKT49b in H13; apply MKT55 in H12; New H13; destruct H13; auto.
          clear H13 H14 H15; destruct H12; rewrite H13 in H10; clear H12.
          clear H13; destruct H0; clear H12; unfold Included in H0.
          apply H0 in H6; apply AxiomII' in H6; destruct H6, H12, H13.
          unfold WellOrder in H14; destruct H14; clear H15.
          unfold TotalOrder in H14; destruct H14; clear H15.
          unfold PartialOrder in H14; destruct H14, H15, H16, H17.
          unfold Antisymmetry in H17; apply H17; auto.
        + assert ([Y1, le1] ∈ K /\ [Y2, le2] ∈ K). { unfold Ensemble; eauto. }
          clear H2; unfold TotalOrder in H1; destruct H1.
          apply H2 in H13; auto; clear H2 H12; destruct H13.
          * unfold Rrelation in H2; apply MKT4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply AxiomII' in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Included in H0; apply H0 in H6.
            apply AxiomII' in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
          * unfold Rrelation in H2; apply MKT4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply AxiomII' in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Included in H0; apply H0 in H6.
            apply AxiomII' in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
      - unfold Transitivity; intros; destruct H2; clear H2; destruct H3.
        unfold Rrelation, leeq in H2, H3; apply AxiomII' in H2.
        apply AxiomII' in H3; destruct H2, H3; destruct H4 as [Y1 [le1 H4]].
        destruct H5 as [Y2 [le2 H5]], H4, H5, H6, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1, le1])); unfold Ensemble; eauto.
          apply MKT49b in H13; apply MKT55 in H12; New H13; destruct H13; auto.
          clear H13 H14 H15; destruct H12; rewrite H12 in H6; rewrite H13 in H10.
          unfold Rrelation, leeq; apply AxiomII'; split.
          * apply MKT49a; unfold Ensemble; eauto.
          * exists Y2, le2; repeat split; auto.
            unfold Included in H0; apply H0 in H5; unfold En_L in H5.
            apply AxiomII' in H5; destruct H5, H14, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v). auto.
        + unfold TotalOrder in H1; destruct H1; apply H13 in H12; auto.
          clear H13; destruct H12.
          * unfold Rrelation, lee in H12; apply MKT4' in H12; destruct H12.
            clear H13; apply AxiomII' in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply AxiomII'; split. apply MKT49a; eauto.
            exists Y2, le2. repeat split; auto; New H6.
            assert(u ∈ Y1 /\ v∈Y1); auto; clear H15; rename H16 into H15.
            apply H13 in H15; apply H15 in H10; clear H13 H15.
            unfold Included in H0; apply H0 in H5; unfold En_L in H5.
            apply AxiomII' in H5; destruct H5, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v); auto.
          * unfold Rrelation, lee in H12; apply MKT4' in H12; destruct H12.
            clear H13; apply AxiomII' in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply AxiomII'; split. apply MKT49a; eauto.
            exists Y1, le1; repeat split; auto; New H7.
            assert(v ∈ Y2 /\ w∈Y2); auto; clear H15; rename H16 into H15.
            apply H13 in H15; apply H15 in H11; clear H13 H15.
            unfold Included in H0; apply H0 in H4; unfold En_L in H4.
            apply AxiomII' in H4; destruct H4, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v); auto. }
    { unfold En_Z in H2; destruct H2; apply AxiomII in H2; apply AxiomII in H4.
      destruct H2, H4, H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]], H5, H6.
      generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H9.
      - assert (Ensemble ([Y1, le1])). { unfold Ensemble; eauto. }
        apply MKT49b in H10; apply MKT55 in H9; New H10; destruct H10;  auto.
        clear H10 H11 H12. destruct H9; rewrite H9 in H7; clear H9 H10; New H6.
        unfold Included in H0; apply H0 in H9; unfold En_L in H9.
        apply AxiomII' in H9; destruct H9, H10; clear H9; clear H10.
        destruct H11 as [H12 H11]; clear H12; unfold WellOrder in H11.
        destruct H11; clear H10; unfold TotalOrder in H9; destruct H9.
        clear H9; New H7; assert(x ∈ Y2 /\ y∈Y2); auto.
        clear H9; rename H11 into H9; apply H10 in H9; auto.
        clear H10 H3; destruct H9.
        + left; unfold Rrelation, leeq; apply AxiomII'.
          split; try apply MKT49; unfold Ensemble; eauto.
          exists Y2, le2; repeat split; auto.
        + right; unfold Rrelation, leeq; apply AxiomII'.
          split. apply MKT49a; eauto.
          exists Y2, le2; repeat split; auto.
      - unfold TotalOrder in H1; destruct H1; apply H10 in H9; auto.
        clear H10; destruct H9.
        + unfold Rrelation, lee in H9; apply MKT4' in H9; destruct H9.
          clear H10; apply AxiomII' in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13.
          destruct H10; clear H9; unfold Initial_Segment in H10.
          destruct H10, H10, H11; clear H12; unfold WellOrder in H11.
          destruct H11; clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Included in H10; apply H10 in H7; New H7.
          assert(x ∈ Y2 /\ y∈Y2); auto; clear H13; rename H14 into H13.
          apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply AxiomII'.
            split; try apply MKT49; unfold Ensemble; eauto.
            exists Y2, le2; repeat split; auto.
          * right; unfold Rrelation, leeq; apply AxiomII'.
            split; try apply MKT49; unfold Ensemble; eauto.
            exists Y2, le2; repeat split; auto.
        + unfold Rrelation, lee in H9; apply MKT4' in H9; destruct H9.
          clear H10; apply AxiomII' in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13; destruct H10.
          clear H9; unfold Initial_Segment in H10; destruct H10, H10, H11.
          clear H12; unfold WellOrder in H11; destruct H11.
          clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Included in H10; apply H10 in H8; New H7.
          assert(x ∈ Y1 /\ y∈Y1); auto; clear H13; rename H14 into H13.
          apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply AxiomII'.
            split; try apply MKT49; unfold Ensemble; eauto.
            exists Y1, le1; repeat split; auto.
          * right; unfold Rrelation, leeq; apply AxiomII'.
            split; try apply MKT49; unfold Ensemble; eauto.
            exists Y1, le1; repeat split; auto. }
  - intro P; intros; destruct H2; apply NEexE in H3.
    destruct H3 as [p H3]; New H3; unfold Included in H2.
    apply H2 in H4; clear H2; unfold En_Z in H4; apply AxiomII in H4.
    destruct H4, H4 as [Y [le H4]], H4; clear H2; New H4.
    apply H0 in H4; unfold En_L in H4; apply AxiomII' in H4.
    destruct H4, H6; clear H4; clear H6; unfold WellOrder in H7.
    destruct H7; clear H4; assert ((Y ∩ P) ⊂ Y /\ (Y ∩ P) ≠ Φ).
    { split.
      - unfold Included; intros; apply MKT4' in H4; apply H4.
      - apply NEexE; exists p; apply MKT4'; auto. }
    clear H3; clear H5; elim H4; intros; apply H6 in H4; clear H6.
    clear H3; destruct H4 as [q H3]; unfold MinElement in H3.
    apply H3 in H5; clear H3; destruct H5; apply MKT4' in H3.
    destruct H3; exists q; unfold MinElement; split; auto; clear H6.
    intro r; intros; intro; unfold Rrelation in H7; destruct H7.
    unfold leeq in H7; apply AxiomII' in H7; destruct H7.
    clear H7; destruct H9 as [Y1 [le1 H7]], H7, H9, H10.
    unfold TotalOrder in H1; destruct H1; unfold Connect in H11.
    generalize (classic ([Y,le] = [Y1,le1])); intros; destruct H13.
    + assert (Ensemble ([Y, le])). { unfold Ensemble; eauto. }
      apply MKT49b in H14; apply MKT55 in H13; New H14; destruct H14; auto.
      clear H14 H15 H16; destruct H13; rewrite <- H13 in H9; rewrite H14 in H4.
      apply H4 with (y:=r); try apply MKT4'; auto.
    + apply H12 in H13; auto; clear H12; destruct H13.
      * unfold Rrelation in H12; apply MKT4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply AxiomII' in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Initial_Segment in H13; destruct H13, H14.
        assert (r∈Y1 /\ q∈Y /\ Rrelation r le1 q).
        { repeat split; auto. } apply H15 in H16; clear H15.
        apply H4 with (y:=r); try apply MKT4'; auto.
        split; auto; apply H13; auto.
      * unfold Rrelation in H12; apply MKT4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply AxiomII' in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Initial_Segment in H13; destruct H13, H14.
        clear H15; New H9; unfold Included in H14; apply H14 in H15.
        apply H4 with (y:=r); try apply MKT4'; auto.
        split; auto; apply H13; auto.
Qed.

Lemma Lemma_WP3 : forall (K X: Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> exists y, BoundU y K (En_L X) (lee X).
Proof.
  intros; New H; New H0.
  apply Lemma_WP2 in H0; auto; exists ([(En_Z K),(leeq K)]).
  unfold Chain in H2; apply (Lemma_WP1 X) in H1; apply H2 in H1.
  clear H2; destruct H1; unfold BoundU; intros; destruct H3.
  assert ([En_Z K, leeq K] ∈ (En_L X)).
  { unfold En_L; apply AxiomII'; split.
    - apply MKT49a.
      + assert ((En_Z K) ⊂ X).
        { unfold Included; intros; unfold En_Z in H5.
          apply AxiomII in H5; destruct H5, H6 as [Y [le H6]], H6.
          unfold Included in H1; apply H1 in H6; unfold En_L in H6.
          apply AxiomII' in H6; destruct H6, H8; auto. }
        apply MKT33 in H5; auto.
      + assert ((leeq K) ⊂ X × X ).
        { unfold Included; intros; unfold leeq in H5.
          PP H5 u v. destruct H7, H6, H6, H7, H8.
          unfold Included in H1; apply H1 in H6; unfold En_L in H6.
          apply AxiomII' in H6; destruct H6, H10; unfold Included in H10.
          apply H10 in H7; apply H10 in H8; unfold Cartesian.
          apply AxiomII'; repeat split; auto. }
        assert (Ensemble X /\ Ensemble X). { auto. }
        destruct H6; apply (MKT74 H6) in H7; apply MKT33 in H5; auto.
    - split.
      + unfold Included; intros; unfold En_Z in H5.
        apply AxiomII in H5; destruct H5, H6 as [Y [le H6]], H6.
        unfold Included in H1; apply H1 in H6; unfold En_L in H6.
        apply AxiomII' in H6; destruct H6, H8; auto.
      + split; try apply H0; destruct H1; apply NEexE in H5.
        destruct H5; apply NEexE; New H5.
        unfold Included in H1; apply H1 in H6; PP H6 Y0 le0.
        New H6.
        destruct H8, H9.
        apply NEexE in H9. destruct H9.
        exists x; unfold En_Z; apply AxiomII; split; unfold Ensemble; eauto. }
  repeat split; auto; try apply H1; intros.
  New H6; unfold Included in H1; apply H1 in H7.
  New H7; unfold En_L in H8; PP H8 Y1 le1; clear H10.
  unfold Rrelation; unfold lee; apply AxiomII'.
  assert (Ensemble ([Y1,le1]) /\ Ensemble ([En_Z K,leeq K])). 
  { unfold Ensemble; eauto. }
  split. apply MKT49a; destruct H9; auto.
  destruct H9.
  apply MKT49b in H9; destruct H9; New H11; apply (MKT54a Y1) in H11;
  apply (MKT54b Y1) in H12; auto.
  apply MKT49b in H10; destruct H10; New H13; apply (MKT54a (En_Z K)) in H13;
  apply (MKT54b (En_Z K)) in H14; auto.
  clear H9 H10. 
  rename H11 into H9; rename H13 into H10; rename H12 into H11; rename H14 into H12.
  rewrite H9, H10, H11, H12; clear H9; clear H10; clear H11; clear H12.
  clear H3; clear H4; split; auto; split; intros.
  - destruct H3; split; intros.
    + unfold Rrelation, leeq; apply AxiomII'.
      split; try apply MKT49; unfold Ensemble; eauto.
      exists Y1, le1; repeat split; auto.
    + unfold Rrelation, leeq in H9; apply AxiomII' in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { unfold Ensemble; eauto. }
        apply MKT49b in H16; apply MKT55 in H15; New H16; destruct H16; auto.
        clear H16 H17 H18; destruct H15; rewrite H16; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply MKT4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII' in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
        -- unfold Rrelation in H14; apply MKT4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII' in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
  - unfold Initial_Segment; split.
    + unfold Included; intros; apply AxiomII; split; unfold Ensemble; eauto.
    + split; try apply H0; intros; destruct H3, H4.
      unfold Rrelation, leeq in H9; apply AxiomII' in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { unfold Ensemble; eauto. }
        apply MKT49b in H16; apply MKT55 in H15; New H16; destruct H16; auto.
        clear H16 H17 H18; destruct H15; rewrite H15; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply MKT4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII' in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Initial_Segment in H15.
           destruct H15, H15, H16; apply H17 with (v:=v); auto.
        -- unfold Rrelation in H14; apply MKT4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII' in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Initial_Segment in H15.
           destruct H15, H15; auto.
Qed.

Theorem WellOrderMKT : forall (X: Class),
  Ensemble X -> exists le0: Class, WellOrder le0 X.
Proof.
  intros.
  assert (PartialOrderSet (En_L X) (lee X)).
  { unfold PartialOrderSet; try apply Lemma_WP1; auto. }
  New H0; apply Zorn in H1; intros; try apply Lemma_WP3; auto.
  destruct H1 as [Y H1]; unfold MaxElement in H1.
  generalize (classic (X = Φ)); intros; destruct H2.
  { rewrite H2; exists Φ; unfold WellOrder; split; intros.
    - unfold TotalOrder; split; intros.
      + unfold PartialOrder; repeat split; intros.
        * apply MKT33 with (x:=X); auto; unfold Included; intros.
        * unfold Relation; intros; feine z; auto.
        * unfold Included; intros; feine z; auto.
        * unfold Reflexivity; intros; feine a; auto.
        * unfold Antisymmetry; intros; destruct H3; feine x; auto.
        * unfold Transitivity; intros; destruct H3, H3; feine u; auto.
      + destruct H3; feine x; auto.
    - destruct H3; generalize (MKT26 A); intros.
      absurd (A = Φ); auto; apply MKT27; auto. }
  assert (En_L X ≠ Φ).
  { apply NEexE in H2; destruct H2.
    apply NEexE; exists ([[x],leq ([x])]).
    unfold En_L; apply AxiomII'; repeat split; intros.
    - assert (Ensemble ([x])). { apply MKT42; unfold Ensemble; eauto. }
      apply MKT49a; auto.
      apply MKT33 with (x:= ([x])×([x])); auto.
      + apply MKT74; auto.
      + unfold Included; intros; PP H4 a b; unfold leq in H6; destruct H6, H6.
        unfold Cartesian; apply AxiomII'; repeat split; auto.
    - unfold Included; intros; unfold Singleton in H3.
      apply AxiomII in H3; destruct H3; rewrite H4; auto.
      apply MKT19; unfold Ensemble; eauto.
    - apply NEexE; exists x; apply AxiomII; unfold Ensemble; eauto.
    - apply MKT33 with (x:=X); auto; unfold Included; intros.
      unfold Singleton in H3; apply AxiomII in H3; destruct H3.
      rewrite H4; auto; apply MKT19; unfold Ensemble; eauto.
    - unfold Relation; intros; PP H3 a b; exists a, b; auto.
    - unfold Included; intros; PP H3 a b; unfold leq in H5; destruct H5, H5.
      unfold Cartesian; apply AxiomII'; repeat split; auto.
    - unfold Reflexivity; intros; unfold Rrelation, leq.
      apply AxiomII'; repeat split; auto; apply MKT49a; unfold Ensemble; eauto.
    - unfold Antisymmetry; intros; destruct H3.
      unfold Singleton in H3, H5; apply AxiomII in H3.
      apply AxiomII in H5; destruct H3, H5.
      rewrite H6, H7; try apply MKT19; unfold Ensemble; eauto.
    - unfold Transitivity; intros; destruct H3, H3, H5.
      apply AxiomII in H3; apply AxiomII in H6; destruct H3, H6.
      rewrite H7, H8; try apply MKT19; unfold Ensemble; eauto.
      unfold Rrelation, leq; apply AxiomII'; repeat split; auto.
      + apply MKT49a; unfold Ensemble; eauto.
      + unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
      + unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
    - destruct H3; apply AxiomII in H3; apply AxiomII in H5.
      destruct H3, H5; rewrite H6, H7 in H4; try apply MKT19; unfold Ensemble; eauto.
      contradiction.
    - destruct H3; apply NEexE in H4; destruct H4.
      exists x0; unfold MinElement; intros; split; auto; intros.
      intro; destruct H7; unfold Rrelation, leq in H7.
      apply AxiomII' in H7; destruct H7, H9, H10.
      rewrite H11 in H8; contradiction. }
  apply H1 in H3; clear H1 H2; destruct H3. 
  unfold En_L in H1; PP H1 Y0 le0. New H1.
  destruct H4, H5.
  apply Property_ProperIncluded in H4; destruct H4.
  - New H4; unfold ProperIncluded in H7; destruct H7; clear H8.
    apply Property_ProperIncluded' in H4; destruct H4, H4.
    assert (([Y0∪[x],(leep Y0 le0 x)]) ∈ (En_L X)).
    { unfold WellOrder in H6; destruct H6; unfold TotalOrder in H6; destruct H6.
      New H6; unfold PartialOrder in H11; destruct H11 as [H12 H11].
      clear H12; destruct H11; unfold En_L; apply AxiomII'; repeat split; intros.
      - apply MKT49b in H3; destruct H3; apply MKT49a.
        + apply AxiomIV; auto; apply MKT42; unfold Ensemble; eauto.
        + assert ((leep Y0 le0 x) ⊂ le0∪(X×X)).
          { unfold Included; intros; PP H14 y1 y2.
            destruct H16; apply MKT4. destruct H15, H16.
            - left; auto.
            - right; unfold Cartesian; apply AxiomII'; destruct H15.
              rewrite H16; repeat split; auto. 
              ++ apply MKT49a; unfold Ensemble; eauto.
              ++ apply MKT4 in H15; destruct H15; auto.
                 unfold Singleton in H15; apply AxiomII in H15; destruct H15.
                 rewrite H17; auto; apply MKT19; unfold Ensemble; eauto. }
          apply MKT33 in H14; auto; apply AxiomIV; auto.
          apply MKT74; auto.
      - unfold Included; intros; apply MKT4 in H13; destruct H13.
        + unfold Included in H7; apply H7 in H13; auto.
        + unfold Singleton in H13; apply AxiomII in H13; destruct H13.
          rewrite H14; auto; apply MKT19; unfold Ensemble; eauto.
      - apply NEexE in H5; destruct H5.
        apply NEexE; exists x0; apply MKT4; tauto.
      - apply MKT33 with (x:=X); auto; unfold Included; intros.
        apply MKT4 in H13; destruct H13; auto; unfold Singleton in H13.
        apply AxiomII in H13; destruct H13; rewrite H14; auto.
        apply MKT19; unfold Ensemble; eauto.
      - unfold Relation; intros; unfold leep in H13; PP H13 y1 y2;
        unfold Ensemble; eauto.
      - unfold Included; intros; PP H13 y1 y2.
        destruct H15; apply AxiomII'; split; auto.
        + destruct H14, H15; split; try apply MKT4; auto.
        +  destruct H14. split; auto. rewrite H15; apply MKT4.
          right; unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
      - unfold Reflexivity; intros; unfold Rrelation, leep; apply AxiomII'.
        split. apply MKT49a; unfold Ensemble; eauto. 
        apply MKT4 in H13; destruct H13.
        + left; repeat split; auto; destruct H12;
          unfold Reflexivity in H12; auto.
        + right; unfold Singleton in H13; apply AxiomII in H13; destruct H13.
          rewrite H14; try apply MKT19; unfold Ensemble; eauto; split; auto.
          apply MKT4; right; apply AxiomII; unfold Ensemble; eauto.
      - unfold Antisymmetry; intros; clear H13; destruct H14.
        unfold Rrelation, leep in H13, H14; apply AxiomII' in H13.
        apply AxiomII' in H14; destruct H13, H14, H15, H16.
        + destruct H15, H16, H17, H18, H12, H21; clear H22.
          unfold Antisymmetry in H21; apply H21; auto.
        + destruct H15, H16; rewrite H18 in H15; contradiction.
        + destruct H15, H16; rewrite H17 in H16; contradiction.
        + destruct H15, H16; rewrite H17, H18; auto.
      - clear H11; destruct H12; clear H11; destruct H12; unfold Transitivity.
        intros; unfold Transitivity in H12; destruct H13, H14, H13, H16.
        unfold Rrelation; apply AxiomII'; split; try apply MKT49a;
        unfold Ensemble; eauto.
        unfold Rrelation, leep in H14, H15; apply AxiomII' in H14.
        apply AxiomII' in H15; destruct H14, H15, H18, H19.
        + left; destruct H18, H19, H20, H21; repeat split; auto.
          apply H12 with (v:=v); auto.
        + right; destruct H19; split; auto.
        + destruct H18, H19; rewrite H20 in H19; contradiction.
        + right; destruct H19; split; auto.
      - destruct H13; apply MKT4 in H13.
        apply MKT4 in H15; destruct H13, H15.
        + New H13; assert(x0 ∈ Y0 /\ y∈Y0); auto.
          clear H16; rename H17 into H16; apply H10 in H16; auto.
          clear H10; destruct H16.
          * left; unfold Rrelation, leep; apply AxiomII'.
            repeat split; try apply MKT49; unfold Ensemble; eauto.
          * right; unfold Rrelation, leep; apply AxiomII'.
            repeat split; try apply MKT49; unfold Ensemble; eauto.
        + left; unfold Rrelation, leep; apply AxiomII'.
          split; try apply MKT49a; unfold Ensemble; eauto; right; split.
          * apply MKT4; tauto.
          * apply AxiomII in H15; destruct H15; apply H16.
            apply MKT19; unfold Ensemble; eauto.
        + right; unfold Rrelation, leep; apply AxiomII'.
          split; try apply MKT49a; unfold Ensemble; eauto; right; split.
          * apply MKT4; tauto.
          * apply AxiomII in H13; destruct H13; apply H16.
            apply MKT19; unfold Ensemble; eauto.
        + left; unfold Rrelation, leep; apply AxiomII'.
          split; try apply MKT49a; unfold Ensemble; eauto; right; split.
          * apply MKT4; tauto.
          * apply AxiomII in H15; destruct H15; apply H16.
            apply MKT19; unfold Ensemble; eauto.
      - destruct H13; assert (A ⊂ Y0 \/ (exists B, B⊂Y0 /\ A = B∪[x])).
        (** 对 (A ⊂ Y0∪[x]) 进行划分 **)
        { generalize (classic (x ∈ A)); intros; destruct H15.
          - right; exists (A ~ [x]); split.
            + unfold Included; intros; unfold Setminus in H16.
              apply AxiomII in H16; destruct H16, H17.
              unfold Complement in H18; apply AxiomII in H18; destruct H18.
              unfold NotIn in H19; unfold Included in H13; apply H13 in H17.
              apply MKT4 in H17; tauto.
            + unfold Setminus; apply AxiomI; split; intros.
              * unfold Included in H13; New H16; apply H13 in H17.
                apply MKT4; apply MKT4 in H17; destruct H17; try tauto.
                left; apply MKT4'; split; auto; unfold Complement.
                apply AxiomII; split; unfold Ensemble; eauto; unfold NotIn; intro.
                unfold Singleton in H18; apply AxiomII in H18; destruct H18.
                rewrite H19 in H17; try contradiction; try apply MKT19; unfold Ensemble; eauto.
              * apply MKT4 in H16; destruct H16.
                -- apply MKT4' in H16; apply H16.
                -- apply AxiomII in H16; destruct H16; rewrite H17; auto.
                   apply MKT19; unfold Ensemble; eauto.
          - left; unfold Included; intros; unfold Included in H13.
            New H16; apply H13 in H17; apply MKT4 in H17.
            destruct H17; auto; apply AxiomII in H17; destruct H17.
            rewrite H18 in H16; try contradiction; apply MKT19; unfold Ensemble; eauto. }
        destruct H15.
        + New H15; assert(A ⊂ Y0 /\ A ≠ Φ); auto; clear H16; rename H17 into H16.
          apply H9 in H16; clear H9.
          destruct H16; exists x0; unfold MinElement in H9.
          apply H9 in H14; clear H9; destruct H14; unfold MinElement; intros.
          split; auto; intros; apply H14 in H17; intro; elim H17; clear H17.
          destruct H18; split; auto; unfold Rrelation, leep in H17.
          apply AxiomII' in H17; destruct H17, H19; try apply H19.
          destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
        + destruct H15 as [B H15], H15.
          generalize (classic (B = Φ)); intros; destruct H17.
          * rewrite H17 in H16; rewrite MKT17 in H16; clear H17.
            rewrite H16; exists x; unfold MinElement; intros; split; intros.
            -- unfold Singleton; apply AxiomII; split; unfold Ensemble; eauto.
            -- unfold Singleton in H18; apply AxiomII in H18; destruct H18.
               intro; destruct H20; rewrite H19 in H21; try contradiction.
               apply MKT19; unfold Ensemble; eauto.
          * rewrite H16; New H15; assert(B ⊂ Y0 /\ B≠Φ); auto; clear H18.
            rename H19 into H18; clear H16; apply H9 in H18.
            clear H9; destruct H18; exists x0; unfold MinElement in H9.
            apply H9 in H17; clear H9; destruct H17; unfold MinElement; intros.
            clear H17; split; try (apply MKT4; tauto); intros.
            apply MKT4 in H17; destruct H17.
            -- apply H16 in H17; intro; elim H17; clear H17.
               destruct H18; split; auto; unfold Rrelation, leep in H17.
               apply AxiomII' in H17; destruct H17, H19; try apply H19.
               destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
            -- intro; destruct H18; apply AxiomII in H17; destruct H17.
               rewrite H20 in H18, H19; try apply MKT19; unfold Ensemble; eauto.
               unfold Rrelation; apply AxiomII' in H18; destruct H18, H21, H21.
               ++ destruct H22; contradiction.
               ++ contradiction. }
    New H9; apply H2 in H10; elim H10; clear H10; split.
    + unfold Rrelation, lee; apply AxiomII'.
      assert (Ensemble ([[Y0,le0],[Y0∪[x],leep Y0 le0 x]])).
      { apply MKT49a; unfold Ensemble; eauto. } split; auto.
      apply Property_lee in H10; destruct H10, H11, H12.
      rewrite H10, H11, H12, H13; clear H10 H11 H12 H13; split; 
      try (split; auto; apply AxiomII'; unfold Ensemble; eauto); split; intros.
      * split; intros.
        -- destruct H10; unfold Rrelation, leep; apply AxiomII'.
           split; try apply MKT49; unfold Ensemble; eauto; try tauto.
        -- unfold Rrelation, leep in H11; apply AxiomII' in H11.
           destruct H11; destruct H12, H12; try apply H13.
           destruct H10; rewrite H13 in H14; contradiction.
      * unfold Initial_Segment; split.
        -- unfold Included; intros; apply MKT4; tauto.
        -- unfold En_L in H9; apply AxiomII' in H9; destruct H9, H10, H11.
           split; try apply H12; intros; destruct H13, H14.
           unfold Rrelation, leep; apply AxiomII' in H15; destruct H15.
           destruct H16; try apply H16; destruct H16.
           rewrite H17 in H14; contradiction.
    + intro; apply MKT49b in H3; apply MKT55 in H10; destruct H3 ; auto.
      destruct H10; elim H8; rewrite H10; apply MKT4; right.
      apply AxiomII; split; unfold Ensemble; eauto.
  - rewrite H4 in H6; exists le0; auto.
Qed.

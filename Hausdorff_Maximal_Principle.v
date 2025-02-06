(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Tukey_Lemma.


(** Hausdorff Maximal Principle **)

(* LemmaH1 *)

Definition En_f1 f A := \{ λ F, F∈f /\ (F ∪ A) ∈ f \}.

Lemma LemmaH1_1 : forall (f A: Class),
  FiniteSet f -> A∈f -> FiniteSet (En_f1 f A).
Proof.
  intros.
  assert (f ≠ Φ). { apply NEexE; try exists A; auto. }
  New H.
  assert(FiniteSet f /\ f ≠ Φ); auto; clear H2; rename H3 into H2.
  apply Property_FinSet in H2; destruct H2.
  unfold FiniteSet in H; destruct H; unfold FiniteSet; repeat split.
  - unfold En_f1; assert (\{ λ F,F∈f /\ (F∪A)∈f \} ⊂ f).
    { unfold Included; intros; apply AxiomII in H5; apply H5. }
    apply MKT33 in H5; auto.
  - intro B; intro; intro B1; intros; unfold En_f1 in H5.
    apply AxiomII in H5; destruct H5, H7; unfold En_f1; apply AxiomII.
    elim H6; intros; apply H4 in H6; auto; repeat split; unfold Ensemble; eauto.
    assert ((B1 ∪ A)⊂(B ∪ A)).
    { unfold Included; intros; apply MKT4 in H11.
      apply MKT4; destruct H11; try tauto.
      unfold Included in H9; apply H9 in H11; auto. }
    assert(B ∪ A ∈ f /\ B1∪A ⊂ B∪A); auto; clear H8; rename H12 into H8.
    apply H2 in H8; auto.
  - intro B; intros; destruct H5.
    unfold En_f1; apply AxiomII; repeat split; auto.
    + apply H4; split; auto; intros; apply H6 in H7.
      unfold En_f1 in H7; apply AxiomII in H7; apply H7.
    + apply H4; split. apply AxiomIV; auto; unfold Ensemble; eauto.
      intro A1; intros; destruct H7.
      assert ((B∩A1) ⊂ B /\ Finite (B∩A1)).
      { split.
        - unfold Included; intros; apply MKT4' in H9; apply H9.
        - rewrite MKT6'. assert(A1 ∩ B ⊂ A1). 
        { unfold Included. intros. unfold Intersection in H9.
        apply AxiomII in H9; destruct H9, H10; auto. }
        apply (finsub H8) in H9; auto. }
      apply H6 in H9; unfold En_f1 in H9; apply AxiomII in H9.
      destruct H9, H10; assert (A1 ⊂ (B∩A1) ∪ A).
      { unfold Included; intros; New H12; unfold Included in H7.
        apply H7 in H13; apply MKT4 in H13; apply MKT4.
        destruct H13; try tauto; left; apply MKT4'; split; auto. }
      apply H2 with (A:= (B∩A1) ∪ A); auto.
Qed.

Proposition NNPP' : ∀ P, P <-> ~~P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Theorem LemmaH1 : forall (f A: Class),
  FiniteSet f -> A∈f -> (exists M, MaxMember M f /\ A ⊂ M).
Proof.
  intros; New H.
  assert (A ∈ (En_f1 f A)).
  { unfold En_f1; apply AxiomII; repeat split; unfold Ensemble; eauto.
    rewrite MKT5; auto. }
  assert ((En_f1 f A) ≠ Φ).
  { generalize (classic ((En_f1 f A) = Φ)); intros.
    destruct H3; auto. rewrite H3 in H2. apply MKT16 in H2; contradiction. }
  apply LemmaH1_1 with (A:=A) in H1; auto.
  assert(FiniteSet (En_f1 f A) /\ (En_f1 f A) ≠ Φ);
  auto; clear H1; rename H4 into H1.
  apply Tukey in H1; destruct H1 as [M H1]; exists M; unfold MaxMember in H1.
  New H3; apply H1 in H4; clear H1; destruct H4.
  assert ((M ∪ A) ∈ (En_f1 f A)).
  { unfold En_f1; apply AxiomII.
    unfold En_f1 in H1; apply AxiomII in H1; destruct H1, H5.
    unfold En_f1 in H2; apply AxiomII in H2; destruct H2, H7.
    repeat split. apply AxiomIV; auto. auto.
    rewrite MKT7; rewrite MKT5; auto. }
  apply H4 in H5; unfold ProperIncluded in H5; apply notandor in H5; destruct H5.
  - cut (M ⊂ M ∪ A); intros; try contradiction.
    unfold Included; intros; apply MKT4; auto.
  - apply NNPP' in H5.
    assert (A ⊂ M).
    { rewrite H5; unfold Included; intros; apply MKT4; auto. }
    split; auto; unfold MaxMember; unfold FiniteSet in H; destruct H.
    unfold En_f1 in H1; apply AxiomII in H1; destruct H1, H8; intros.
    clear H10; repeat split; auto; intro K; intros; intro.
    unfold ProperIncluded in H11; destruct H11; New H11.
    apply (MKT28 H6) in H11; apply MKT29 in H11.
    New H10; rewrite MKT6 in H11; rewrite <- H11 in H14.
    assert (K ∈ (En_f1 f A)).
    { unfold En_f1; apply AxiomII; repeat split; unfold Ensemble; eauto. }
    apply H4 in H15; unfold ProperIncluded in H15. tauto.
Qed.

(* LemmaH2 *)

(* Hypothesis HH2 : forall (A1 F: Class), A1 ⊂ F /\ Finite A1. *)

Lemma LemmaH2 : forall (A: Class),
  Ensemble A -> FiniteSet \{ λ n, n ⊂ A /\ Nest n \}.
Proof.
  intros.
  unfold FiniteSet; repeat split; intros.
  - apply MKT38a in H; auto.
    assert (\{ λ n, n ⊂ A /\ Nest n \} ⊂ pow(A)).
    { unfold Included at 1; intros; unfold PowerClass; apply AxiomII.
      apply AxiomII in H0; destruct H0, H1; split; auto. }
    apply MKT33 in H0; auto.
  - apply AxiomII in H0; apply AxiomII; destruct H0, H1, H2.
    New H2; apply (MKT28 H1) in H5; New H5.
    apply MKT33 in H6; repeat split; auto; intros; unfold Nest.
    intros; unfold Nest in H4; destruct H7; unfold Included in H1.
    apply H1 in H7; apply H1 in H8.
    assert(A0 ∈ F /\ B∈F); auto.
  - destruct H0; apply AxiomII; repeat split; auto; intros.
    + unfold Included; intros; assert ([z] ⊂ F /\ Finite ([z])).
      { split; try (apply finsin; unfold Ensemble; eauto).
        unfold Included; intros; apply AxiomII in H3.
        destruct H3; rewrite H4; auto; apply MKT19; unfold Ensemble; eauto. }
      apply H1 in H3; apply AxiomII in H3; destruct H3, H4.
      unfold Included in H4; apply H4; apply AxiomII; unfold Ensemble; eauto.
    + unfold Nest; intros; destruct H2.
      assert ([A0|B] ⊂ F /\ Finite ([A0|B])).
      { split.
        - unfold Included; intros; unfold Unordered in H4.
          apply MKT4 in H4; destruct H4.
          + unfold Singleton in H4; apply AxiomII in H4.
            destruct H4; rewrite H5; auto; apply MKT19; unfold Ensemble; eauto.
          + unfold Singleton in H4; apply AxiomII in H4.
            destruct H4; rewrite H5; auto; apply MKT19; unfold Ensemble; eauto.
        - unfold Unordered; apply MKT168.
          apply finsin; unfold Ensemble; eauto.
          apply finsin; unfold Ensemble; eauto. }
      apply H1 in H4; apply AxiomII in H4; destruct H4, H5.
      unfold Nest in H6; apply H6; split.
      * unfold Unordered; apply MKT4; left.
        unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
      * unfold Unordered; apply MKT4; right.
        unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
Qed.

(* Hausdorff Maximum Principle*)

Theorem Hausdorff : forall (A N: Class),
  Ensemble A -> N ⊂ A /\ Nest N ->
  (exists u, MaxMember u \{ λ n, n⊂A /\ Nest n \} /\ N ⊂ u).
Proof.
  intros; destruct H0; New H.
  apply LemmaH2 in H2; New H0; apply MKT33 in H0; auto.
  apply LemmaH1 with (A:=N) in H2; auto.
  apply AxiomII; auto.
Qed.

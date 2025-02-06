(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*      Copyright 2018-2019: Tianyu Sun, Yaoshun Fu and Wensheng Yu.       *)
(***************************************************************************)


Require Export Hausdorff_Maximal_Principle.


(** Maximal Principle **)

Lemma Ex_Nest : forall A, exists N, N ⊂ A /\ Nest N.
Proof.
  intros.
  exists Φ; split; try apply MKT26; unfold Nest; intros.
  destruct H. assert(B ∉ Φ). { apply MKT16. } contradiction.
Qed.

Theorem MaxPrinciple : forall (A: Class),
  Ensemble A ->
  (forall n, n⊂A /\ Nest n -> exists N, N∈A /\ (forall u, u∈n -> u⊂N))  ->
  exists M, MaxMember M A.
Proof.
  intros.
  generalize (Ex_Nest A); intros; destruct H1 as [n H1].
  assert (\{ λ n, n ⊂ A /\ Nest n \} ≠ Φ).
  { apply NEexE; exists n; destruct H1.
    apply AxiomII; repeat split; auto; apply MKT33 in H1; auto. }
  apply Hausdorff in H1; auto; destruct H1 as [u H1], H1.
  unfold MaxMember in H1; apply H1 in H2; clear H1; destruct H2.
  apply AxiomII in H1; destruct H1; elim H4; intros; apply H0 in H4.
  destruct H4 as [N H4]; exists N; unfold MaxMember; destruct H4; intro.
  clear H8; repeat split; auto; intro K; intros; intro.
  unfold ProperIncluded in H9; destruct H9.
  assert ((u ∪ [K]) ∈ \{ λ n, n⊂A /\ Nest n \}).
  { apply AxiomII; assert (Ensemble (u ∪ [K])).
    { apply AxiomIV; auto; apply MKT42; unfold Ensemble; eauto. }
    repeat split; auto; intros.
    - unfold Included; intros; apply MKT4 in H12; destruct H12.
      + unfold Included in H5; apply H5 in H12; auto.
      + unfold Singleton in H12; apply AxiomII in H12.
        destruct H12; rewrite H13; auto; apply MKT19; unfold Ensemble; eauto.
    - unfold Nest; intros; destruct H12.
      apply MKT4 in H12; apply MKT4 in H13.
      assert (K ∈ μ). { apply MKT19; unfold Ensemble; eauto. }
      unfold Nest in H6; destruct H12, H13.
      + assert(A0 ∈ u /\ B ∈ u); auto.
      + unfold Singleton in H13; apply AxiomII in H13.
        destruct H13; rewrite <- H15 in H9; auto; apply H7 in H12.
        apply (MKT28 H12) in H9; tauto.
      + unfold Singleton in H12; apply AxiomII in H12.
        destruct H12; rewrite <- H15 in H9; auto; apply H7 in H13.
        apply (MKT28 H13) in H9; tauto.
      + unfold Singleton in H12, H13; apply AxiomII in H12.
        apply AxiomII in H13; destruct H12, H13; left.
        rewrite H15, H16; auto; unfold Included; auto. }
  apply H2 in H11; unfold ProperIncluded in H11.
  apply notandor in H11; destruct H11.
  - absurd (u ⊂ u ∪ [K]); auto.
  - apply NNPP' in H11; assert (K∈u).
    { rewrite H11; apply MKT4; right.
      unfold Singleton; apply AxiomII; split; unfold Ensemble; eauto. }
    apply H7 in H12; assert(N ⊂ K /\ K ⊂ N); auto.
    apply MKT27 in H13; contradiction.
Qed.

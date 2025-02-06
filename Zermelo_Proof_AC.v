(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Zermelo_Postulate.


(** The proof of AC **)

Definition En_p X : Class :=
  \{ λ z, exists A, A ∈ (pow(X)~[Φ]) /\ z = (A × [A]) \}.

Theorem Zermelo_AC : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  assert (exists D, forall p, p ∈ (En_p X) -> exists x, p ∩ D = [x]).
  { assert (Ensemble (En_p X) /\ Φ ∉ (En_p X)).
    { assert ((En_p X) ⊂ pow(X × (pow(X)~[Φ]))).
      { unfold Included; intros; unfold En_p in H0; apply AxiomII in H0.
        destruct H0, H1 as [A H1], H1; rewrite H2 in *; clear H2.
        apply AxiomII; split; auto; unfold Included; intros.
        PP H2 a b; destruct H4.
        unfold Setminus in H1; apply AxiomII in H1; destruct H1, H5; New H5.
        unfold PowerClass in H7; apply AxiomII in H7; destruct H7 as [_ H7].
        unfold Cartesian; apply AxiomII' ; repeat split; auto.
        unfold Singleton in H4; apply AxiomII in H4; destruct H4.
        rewrite H8 in *; try apply MKT19; unfold Ensemble; eauto; clear H8.
        unfold Setminus; apply MKT4'; split; auto. }
      assert (Ensemble (pow( X × (pow( X) ~ [Φ])))).
      { apply MKT38a; auto; apply MKT74; auto.
        unfold Setminus; apply MKT38a in H; auto.
        apply MKT33 with (x:= pow(X)); auto.
        unfold Included; intros; apply MKT4' in H1; apply H1. }
      apply MKT33 in H0; auto; clear H1; split; auto.
      intro; unfold En_p in H1; apply AxiomII in H1; destruct H1.
      destruct H2 as [A H2], H2; unfold Setminus in H2.
      apply MKT4' in H2; destruct H2; unfold Complement in H4.
      apply AxiomII in H4; destruct H4.
      generalize (classic (A = Φ)); intros; destruct H6.
      - rewrite H6 in H5; destruct H5; apply AxiomII; unfold Ensemble; eauto.
      - apply NEexE in H6; destruct H6.
        assert ([x,A] ∈ Φ).
        { rewrite H3; unfold Cartesian; apply AxiomII'.
          repeat split;assert (Ensemble x); unfold Ensemble; eauto. }
          feine ([x,A]); auto. }
    destruct H0; apply Zermelo in H0; try destruct H0 as [D H0], H0; 
    unfold Ensemble; eauto.
    intros; unfold En_p in H2; destruct H2; apply AxiomII in H2.
    apply AxiomII in H4; destruct H2, H4, H5 as [A H5], H6 as [B H6], H5, H6.
    rewrite H7, H8 in *; clear H7 H8; apply AxiomI; split; intros.
    - apply MKT4' in H7; destruct H7; PP H7 a b.
      apply AxiomII' in H8; destruct H8, H9, H8, H10.
      unfold Singleton in H11, H12; apply AxiomII in H11; apply AxiomII in H12.
      destruct H11 as [_ H11], H12 as [_ H12].
      assert (Ensemble A); unfold Ensemble; eauto.
      assert (Ensemble B); unfold Ensemble; eauto.
      apply MKT19 in H13; apply MKT19 in H14; apply H12 in H13.
      apply H11 in H14. rewrite H13 in H14; rewrite H14 in H3;
      destruct H3; unfold Ensemble; eauto.
    - feine z; auto. }
  destruct H0 as [D H0].
  set (fc := \{\ λ A B, A ∈ (pow(X) ~ [Φ]) /\ B = First( ∩((A×[A]) ∩ D)) \}\).
  assert (Function (fc)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H1 a b; unfold Ensemble; eauto.
    - apply AxiomII' in H1; apply AxiomII' in H2.
      destruct H1, H2, H3, H4; rewrite H5, H6; auto. }
  exists fc; unfold Choice_Function; repeat split; try apply H1; intros.
  - clear H1; unfold Included, Range; intros; apply AxiomII in H1.
    destruct H1, H2; apply AxiomII' in H2; clear H1; destruct H2, H2.
    apply MKT49b in H1; destruct H1.
    assert ((x × [x]) ∈ (En_p X)).
    { unfold En_p; apply AxiomII; split; unfold Ensemble; eauto.
      apply MKT74; try apply MKT42; auto. }
    assert (Ensemble (x × [x])); unfold Ensemble; eauto.
    apply H0 in H5; destruct H5; rewrite H5 in H3.
    assert (Ensemble x0).
    { apply MKT42'; rewrite <- H5.
      apply MKT33 with (x:= x × [x]); auto; unfold Included; intros.
      apply MKT4' in H7; apply H7. }
    clear H6; New H7; apply MKT44 in H7; destruct H7 as [H7 _].
    rewrite H7 in H3; clear H7.
    assert (x0 ∈ (x × [x] ∩ D)).
    { rewrite H5; unfold Singleton; apply AxiomII; unfold Ensemble; eauto. }
    apply MKT4' in H7; destruct H7 as [H7 _]. 
    apply AxiomII in H7 as [? [a [b []]]]; rewrite H8 in *.
    clear H7 H8; destruct H9;apply MKT49b in H6. 
    destruct H6; apply (MKT54a a) in H9; auto.
    rewrite H9 in H3; rewrite H3 in *; unfold Setminus, PowerClass in H2.
    apply MKT4' in H2;destruct H2 as [H2 _].
    apply AxiomII in H2; apply H2 in H7; auto.
  - clear H1; apply AxiomI; split; intros.
    + unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
      apply AxiomII' in H2; apply H2.
    + unfold Domain; apply AxiomII; split; unfold Ensemble; eauto.
      assert ((z × [z]) ∈ (En_p X)).
      { unfold En_p; apply AxiomII; split.
        - apply MKT74; try apply MKT42; unfold Ensemble; eauto.
        - exists z; split; auto. }
      assert (Ensemble (z × [z])); unfold Ensemble; eauto.
      apply H0 in H2; destruct H2.
      assert (Ensemble x).
      { apply MKT42'; rewrite <- H2.
        apply MKT33 with (x:= z × [z]); auto; unfold Included; intros.
        apply MKT4' in H4; apply H4. }
      assert (x ∈ (z × [z] ∩ D)); clear H3.
      { rewrite H2; unfold Singleton; apply AxiomII; unfold Ensemble; eauto. }
      apply MKT4' in H5; destruct H5 as [H3 _]; PP H3 a b.
      apply MKT49b in H4; elim H4; intros; clear H6.
      destruct H4; apply (MKT54a a) in H6; auto.
      exists a. apply AxiomII' ; repeat split; auto.
      * apply MKT49a; unfold Ensemble; eauto.
      * rewrite H2. apply MKT44 in H3; destruct H3 as [H3 _].
        rewrite H3, H6; auto.
  - apply Property_Value in H2; auto; apply AxiomII' in H2; destruct H2, H3.
    assert ((A × [A]) ∈ (En_p X)).
    { unfold En_p; apply AxiomII; split.
      - apply MKT74; try apply MKT42; unfold Ensemble; eauto.
      - exists A; split; auto. }
    assert (Ensemble (A × [A])); unfold Ensemble; eauto.
    apply H0 in H5; destruct H5.
    assert (Ensemble x).
    { apply MKT42'; rewrite <- H5.
      apply MKT33 with (x:= A × [A]); auto; unfold Included; intros.
      apply MKT4' in H7; apply H7. }
    assert (x ∈ (A × [A] ∩ D)); clear H6.
    { rewrite H5; unfold Singleton; apply AxiomII; unfold Ensemble; eauto. }
    apply MKT4' in H8; destruct H8 as [H6 _]; PP H6 a b.
    apply MKT49b in H7; destruct H7; apply (MKT54a a) in H8; auto.
    rewrite H5 in H4; apply MKT44 in H6; destruct H6 as [H6 _]; destruct H9.
    rewrite H6, H8 in H4; rewrite H4; auto.
Qed.

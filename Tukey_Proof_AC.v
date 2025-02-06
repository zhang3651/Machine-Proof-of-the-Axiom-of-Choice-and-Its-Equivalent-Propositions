(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Tukey_Lemma.

(* The Proof of Axiom of Choice *)

(* Special form of Choice Function *)

Definition Choice_Function' ε u : Prop :=
  Ensemble u /\ Function ε /\ dom(ε) = u /\ ran(ε) ⊂ ∪u
  /\ (forall x, x ∈ dom(ε) -> ε[x] ∈ x).

(* Hypotheses *)

Definition En_f X :=
  \{ λ g, exists A, A ⊂ (pow(X)~[Φ]) /\ Choice_Function' g A \}.

(* Properties *)

Lemma Property_CF x : Ensemble x -> Choice_Function' Φ Φ.
Proof.
  intros.
  unfold Choice_Function'; repeat split; intros.
  - generalize (MKT26 x); intros.
    apply MKT33 in H0; auto.
  - unfold Relation; intros.
    apply MKT16 in H0; contradiction.
  - apply MKT16 in H0; contradiction.
  - apply AxiomI; split; intros.
    + unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
      apply MKT16 in H1; contradiction.
    + apply MKT16 in H0; contradiction.
  - unfold Included; intros; unfold Range in H0.
    apply AxiomII in H0; destruct H0, H1.
    apply MKT16 in H1; contradiction.
  - unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
    apply MKT16 in H1; contradiction.
Qed.

Lemma Included_Function : forall (g f: Class),
  Function g /\ Function f /\ g ⊂ f -> (dom(g) ⊂ dom(f))
  /\ (forall x, x ∈ dom(g) -> g[x] = f[x]).
Proof.
  intros.
  destruct H, H0.
  unfold Included in H1; split.
  - unfold Included; intros.
    unfold Domain in H2; apply AxiomII in H2; destruct H2, H3.
    unfold Domain; apply AxiomII; split; auto.
    exists x; apply H1 in H3; auto.
  - intros; apply Property_Value in H2; auto.
    apply H1 in H2; apply MKT70 in H0; auto.
    rewrite H0 in H2; apply AxiomII' in H2; apply H2.
Qed.

(* Lemma *)

Lemma Lemma_Fin_not_Em : forall X,
  Ensemble X -> FiniteSet (En_f X) /\ (En_f X) ≠ Φ.
Proof.
  intros.
  assert ((En_f X) ≠ Φ).
  { apply NEexE; auto.
    exists Φ; unfold En_f; apply AxiomII; split.
    - assert (Φ ⊂ X); try apply MKT26.
      apply MKT33 in H0; auto.
    - exists Φ; split; try apply MKT26.
      apply (Property_CF X); auto. }
  split; auto; unfold FiniteSet; repeat split; intros.
  - assert (En_f X ⊂ pow(pow(X) × (∪pow(X)))).
    { unfold Included; intros.
      unfold En_f in H1; apply AxiomII in H1; destruct H1.
      destruct H2 as [A H2]; destruct H2.
      assert (pow(X) ~ [Φ] ⊂ pow(X)).
      { unfold Setminus, Included; intros.
        apply MKT4' in H4; apply H4. }
        New H4.
      apply (MKT28 H2) in H4. clear H2; rename H4 into H2; rename H5 into H4.
      unfold Choice_Function' in H3; destruct H3, H5, H6, H7.
      unfold PowerClass at 1; apply AxiomII; split.
      - rewrite <- H6 in H3; apply MKT75; auto.
      - unfold Included; intros; unfold Cartesian; New H9.
        apply H5 in H10; destruct H10 as [a [b H10]]; rewrite H10 in *.
        clear H10; apply AxiomII' ; repeat split; unfold Ensemble; eauto.
        + apply Property_dom in H9; rewrite H6 in H9.
          unfold Included in H2; apply H2; auto.
        + apply Property_ran in H9.
          unfold Included in H7; apply H7 in H9.
          apply MKT31 in H2; destruct H2.
          unfold Included in H2; apply H2; auto. }
    apply MKT38a in H; auto; New H; apply AxiomVI in H2.
    apply (MKT74 H) in H2. apply MKT38a in H2; auto.
    apply MKT33 in H1; auto.
  - destruct H2; unfold En_f in H1; unfold En_f.
    apply AxiomII in H1; apply AxiomII; destruct H1.
    destruct H4 as [D H4], H4; unfold Choice_Function' in H5.
    destruct H5, H6, H7, H8; split.
    + apply MKT33 in H2; auto.
    + generalize (classic (z=Φ)); intros; destruct H10.
      * exists Φ; split; try apply MKT26.
        rewrite H10; apply (Property_CF X); auto.
      * assert (Function z).
        { unfold Function in H6; destruct H6.
          unfold Function; split; intros.
          - unfold Relation in H6; unfold Relation; intros.
            unfold Included in H2; apply H2 in H12.
            apply H6 in H12; destruct H12, H12; exists x, x0; auto.
          - unfold Included in H2.
            apply H2 in H12; apply H2 in H13.
            apply (H11 x y z0); auto. }
        New H11; assert(Function z /\ Function F /\ z⊂F); auto. 
        clear H11; rename H13 into H11.
        apply Included_Function in H11; destruct H11.
        exists (dom(z)); split.
        -- rewrite H7 in H11; apply (MKT28 H11) in H4; auto.
        -- { unfold Choice_Function'; repeat split; try apply H12; auto.
             - rewrite H7 in H11; apply MKT33 in H11; auto.
             - unfold Included; intros.
               unfold Element_U; apply AxiomII.
               unfold Range in H14; apply AxiomII in H14.
               destruct H14, H15; New H15; split; auto.
               apply MKT70 in H12; auto.
               rewrite H12 in H15; apply AxiomII' in H15.
               apply Property_dom in H16; destruct H15.
               exists x; split; auto; rewrite H17; New H16.
               unfold Included in H11; apply H11 in H16.
               apply H9 in H16; apply H13 in H18; rewrite H18; auto.
             - intros; New H14; unfold Included in H11; apply H11 in H14.
               apply H9 in H14; apply H13 in H15; rewrite H15; auto. }
  - intros; destruct H1.
    unfold En_f; apply AxiomII; split; auto.
    assert (F ⊂ ∪(En_f X) /\ ∪(En_f X) ⊂ ((pow( X) ~ [Φ]) × X)).
    { split.
      - unfold Included; intros; assert (Ensemble z); unfold Ensemble; eauto.
        unfold Element_U; apply AxiomII; split; auto.
        exists [z]; split.
        + unfold Singleton; apply AxiomII; split; auto.
        + apply H2; split; try apply finsin; auto.
          unfold Included; intros; unfold Singleton in H5; apply AxiomII in H5.
          destruct H5; apply MKT19 in H4; apply H6 in H4; rewrite H4; auto.
      - unfold Included; intros.
        unfold Element_U in H3; apply AxiomII in H3.
        destruct H3, H4 as [f1 H4], H4.
        assert (exists a b, z = [a,b]).
        { unfold En_f in H5; apply AxiomII in H5; destruct H5, H6, H6.
          unfold Choice_Function' in H7; apply H7 in H4; apply H4. }
        destruct H6 as [a [b H6]]; unfold Cartesian.
        rewrite H6; rewrite H6 in H3; rewrite H6 in H4.
        apply AxiomII'; split; auto.
        unfold En_f in H5; apply AxiomII in H5.
        destruct H5, H7 as [A H7], H7.
        unfold Choice_Function' in H8.
        destruct H8, H9, H10, H11; split.
        + apply Property_dom in H4; rewrite H10 in H4.
          unfold Included in H7; apply H7 in H4; auto.
        + apply Property_ran in H4.
          unfold Included in H11; apply H11 in H4.
          unfold Element_U in H4; apply AxiomII in H4.
          destruct H4, H13, H13.
          unfold Included in H7; apply H7 in H14.
          unfold Setminus in H14; apply MKT4' in H14; destruct H14.
          unfold PowerClass in H14; apply AxiomII in H14; destruct H14.
          unfold Included in H16; apply H16 in H13; auto. }
    elim H3; intros; New H5; apply (MKT28 H4) in H6; clear H3.
    rename H6 into H3; generalize (classic (F = Φ)); intros; destruct H6.
    + exists Φ; split; try apply MKT26.
      rewrite H6; apply (Property_CF X); auto.
    + assert (Function F).
      { unfold Function, Relation; split; intros.
        - unfold Included in H3; apply H3 in H7.
          PP H7 a b; unfold Ensemble; eauto.
        - assert ([[x,y]|[x,z]] ⊂ F /\ Finite ([[x,y]|[x,z]])).
          { unfold Included, Unordered; split; intros.
            - apply AxiomII in H9; destruct H9, H10.
              + unfold Singleton in H10; apply AxiomII in H10.
                destruct H10; rewrite H11; auto.
                apply MKT19; unfold Ensemble; eauto.
              + unfold Singleton in H10; apply AxiomII in H10.
                destruct H10; rewrite H11; auto.
                apply MKT19; unfold Ensemble; eauto.
            - apply MKT168; apply finsin; unfold Ensemble; eauto. }
          apply H2 in H9; unfold En_f in H9; apply AxiomII in H9.
          destruct H9, H10, H10; unfold Choice_Function' in H11.
          destruct H11, H12, H13; unfold Function in H12.
          apply H12 with (x0:=x); unfold Unordered; apply AxiomII.
          + split; try left; unfold Ensemble; eauto; 
            unfold Singleton; apply AxiomII; unfold Ensemble; eauto.
          + split; try right; unfold Ensemble; eauto; 
            unfold Singleton; apply AxiomII; unfold Ensemble; eauto. }
      exists dom(F); split.
      * unfold Included; intros; apply Property_Value in H8; auto.
        unfold Included in H3; apply H3 in H8.
        unfold Cartesian in H8; apply AxiomII' in H8; apply H8.
      * { unfold Choice_Function'; repeat split; try apply H7; auto; intros.
          - assert (dom(F) ⊂ pow(X)).
            { unfold Included; intros.
              unfold Domain in H8; apply AxiomII in H8; destruct H8, H9.
              unfold Included in H3; apply H3 in H9.
              unfold Cartesian in H9; apply AxiomII' in H9; destruct H9, H10.
              unfold Setminus in H10; apply MKT4' in H10; apply H10. }
            apply MKT33 in H8; apply MKT38a in H; auto.
          - unfold Included; intros; apply AxiomII; split; 
            unfold Ensemble; eauto.
            unfold Range in H8; apply AxiomII in H8; destruct H8, H9.
            New H9; exists x; apply Property_dom in H9; split; auto.
            unfold Element_U in H4; apply H4 in H10.
            apply AxiomII in H10; destruct H10, H11 as [f H11], H11.
            unfold En_f in H12; apply AxiomII in H12; destruct H12, H13, H13.
            unfold Choice_Function' in H14; destruct H14, H15, H16, H17.
            New H11; apply Property_dom in H19; New H19.
            apply Property_Value in H20; auto; apply H18 in H19.
            unfold Function in H15; destruct H15.
            assert(f[x] = z). { apply (H21 x f[x] z); auto. }
            rewrite H22 in H19; auto.
          - apply Property_Value in H8; auto; apply H4 in H8.
            unfold Element_U in H8; apply AxiomII in H8.
            destruct H8, H9 as [f H9], H9; unfold En_f in H10.
            apply AxiomII in H10; destruct H10, H11, H11.
            unfold Choice_Function' in H12; destruct H12, H13, H14, H15.
            New H9; apply Property_dom in H17; New H17.
            apply H16 in H17; apply Property_Value in H18; auto.
            unfold Function in H13; destruct H13.
            assert(f[x] = F[x]). { apply (H19 x f[x] F[x]); auto. }
            rewrite H20 in H17; auto. }
Qed.

Theorem Tukey_AC : forall X,
  Ensemble X -> exists ε, Choice_Function ε X.
Proof.
  intros.
  New H; apply Lemma_Fin_not_Em in H0.
  apply Tukey in H0; destruct H0 as [F H0]; exists F.
  assert ((En_f X) ≠ Φ).
  { apply NEexE; exists Φ; unfold En_f; apply AxiomII; split.
    - assert (Φ ⊂ X); try apply MKT26; apply MKT33 in H1; auto.
    - exists Φ; split; try apply MKT26; apply (Property_CF X); auto. }
  unfold MaxMember in H0; apply H0 in H1; clear H0.
  assert (Ensemble (En_f X)).
  { assert (En_f X ⊂ pow(pow(X) × (∪pow(X)))).
    { clear H1; unfold Included; intros; unfold En_f in H0.
      apply AxiomII in H0; destruct H0, H1 as [A H1]; destruct H1.
      assert (pow(X) ~ [Φ] ⊂ pow(X)).
      { unfold Setminus, Included; intros; apply MKT4' in H3; apply H3. }
      apply (MKT28 H1) in H3.
      unfold Choice_Function' in H2; destruct H2, H4, H5, H6.
      unfold PowerClass at 1; apply AxiomII; split.
      - rewrite <- H5 in H2; apply MKT75; auto.
      - unfold Included; intros; unfold Cartesian; New H8.
        apply H4 in H9; destruct H9 as [a [b H9]]; rewrite H9 in *.
        clear H9; apply AxiomII'; repeat split; unfold Ensemble; eauto.
        + apply Property_dom in H8; rewrite H5 in H8; apply H3; auto.
        + apply Property_ran in H8; unfold Included in H6; apply H6 in H8.
          apply MKT31 in H3; destruct H3; apply H3; auto. }
    apply MKT38a in H; auto; New H; apply AxiomVI in H2.
    apply (MKT74 H) in H2;apply MKT38a in H2; auto. apply MKT33 in H0; auto. }
  destruct H1; New H1; unfold En_f in H3; apply AxiomII in H3.
  destruct H3, H4 as [D H4], H4;
  apply Property_ProperIncluded in H4; destruct H4.
  - New H4; apply Property_ProperIncluded' in H6; destruct H6 as [E H6], H6.
    New H6; unfold Setminus in H8; apply MKT4' in H8; destruct H8.
    clear H8; unfold Complement in H9; apply AxiomII in H9; destruct H9.
    unfold NotIn in H9; assert (E ∈ [Φ] <-> Ensemble E /\ (E=Φ)).
    { split; intros.
      - unfold Singleton in H10; apply AxiomII in H10; destruct H10.
        split; auto; apply H11; apply MKT19.
      - destruct H10; unfold Singleton; apply AxiomII; split; auto. }
    assert(forall A B, (A<->B) -> (~ A) -> (~ B)). 
    { unfold not; intros; apply H11 in H13; apply H12 in H13; auto. }
    apply H11 in H10; auto; clear H9; clear H11.
    apply notandor in H10; destruct H10; try contradiction.
    apply NEexE in H9; destruct H9 as [e H9].
    cut ((F ∪ [[E,e]])∈ (En_f X) /\ F ⊊ (F ∪ [[E,e]])); intros.
    { destruct H10; apply H2 in H10; contradiction. }
    assert (Ensemble ([E,e])). { apply MKT49a; unfold Ensemble; eauto. }
    unfold Choice_Function' in H5; destruct H5, H11, H12, H13.
    assert (F ⊊ (F ∪ [[E,e]])).
    { unfold ProperIncluded; split.
      - unfold Included; intros; apply MKT4; left; auto.
      - intro; rewrite <- H12 in H7; assert ([E,e]∈F).
        { rewrite H15; apply MKT4; right.
          unfold Singleton; apply AxiomII; split; auto. }
        apply Property_dom in H16; contradiction. }
    split; auto; unfold En_f; apply AxiomII; split.
    + apply AxiomIV; auto; apply MKT42; auto.
    + { exists (D ∪ [E]); split.
        - unfold Included; intros. apply MKT4 in H16; destruct H16.
          + unfold ProperIncluded in H4; destruct H4.
            unfold Included in H4; apply H4 in H16; auto.
          + unfold Singleton in H16; apply AxiomII in H16.
            destruct H8; destruct H16; rewrite H17; auto.
            apply MKT19; unfold Ensemble; eauto.
        - assert (Function (F ∪ [[E,e]])).
          { unfold Function; split.
            - unfold Function in H11; destruct H11.
              unfold Relation in H11; unfold Relation; intros.
              apply MKT4 in H17; destruct H17.
              + apply H11 in H17; auto.
              + unfold Singleton in H17; apply AxiomII in H17.
                exists E, e; apply H17; apply MKT19; auto.
            - intros; apply MKT4 in H16.
              apply MKT4 in H17; destruct H16, H17.
              + unfold Function in H11; apply H11 with (x:=x); auto.
              + apply Property_dom in H16; rewrite H12 in H16.
                New H10; unfold Singleton in H17; apply AxiomII in H17.
                destruct H17; apply MKT19 in H18; apply H19 in H18.
                apply MKT49b in H10. destruct H10; clear H10; 
                rename H20 into H10; symmetry in H18; apply MKT55 in H18;
                destruct H18.
                rewrite H18 in H7; contradiction. auto. auto.
              + apply Property_dom in H17; rewrite H12 in H17; New H10; 
                unfold Singleton in H16; apply AxiomII in H16; destruct H16; 
                apply MKT19 in H18; apply H19 in H18; apply MKT49b in H10; 
                destruct H10; clear H10; rename H20 into H10; symmetry in H18; 
                apply MKT55 in H18; destruct H18.
                rewrite H18 in H7; contradiction. auto. auto.
              + unfold Singleton in H16, H17; apply AxiomII in H16; 
                apply AxiomII in H17; destruct H16, H17; New H10; 
                apply MKT19 in H20; New H20; apply H18 in H20; 
                apply H19 in H21; New H10; apply MKT49b in H10; 
                destruct H10; clear H10; rename H20 into H10. 
                apply MKT49b in H22; destruct H22; clear H20. 
                symmetry in H10. apply MKT55 in H10. destruct H10.
                symmetry in H21. apply MKT55 in H21. destruct H21.
                rewrite <- H20, <- H24; auto. auto. auto. auto. auto. }
          assert (dom((F ∪ [[E,e]])) = D ∪ [E]).
          { apply AxiomI; split; intros.
            - unfold Domain in H17; apply AxiomII in H17.
              destruct H17, H18; apply MKT4 in H18; destruct H18.
              + apply Property_dom in H18; rewrite H12 in H18.
                apply MKT4; tauto.
              + unfold Singleton in H18; apply AxiomII in H18; New H10.
                destruct H18; apply MKT19 in H10; apply H20 in H10.
                apply MKT49b in H19. destruct H19.
                symmetry in H10. apply MKT55 in H10. destruct H10.
                apply MKT4; right; unfold Singleton.
                apply AxiomII; split; auto. auto. auto.
            - unfold Domain; apply AxiomII; split; unfold Ensemble; eauto.
              apply MKT4 in H17; destruct H17.
              + exists F[z]; apply MKT4; left.
                rewrite <- H12 in H17; apply Property_Value in H17; auto.
              + exists e; apply MKT4; right; unfold Singleton in H17.
                apply AxiomII in H17; destruct H17.
                rewrite H18; try (apply MKT19; unfold Ensemble; eauto).
                unfold Singleton; apply AxiomII; split; auto. }
          unfold Choice_Function'; repeat split; try apply H16; auto.
          + apply AxiomIV; try apply MKT42; unfold Ensemble; eauto.
          + unfold Included; intros.
            unfold Range in H18; apply AxiomII in H18; destruct H18, H19.
            apply MKT4 in H19; destruct H19.
            * unfold Element_U; apply AxiomII; split; auto.
              apply Property_ran in H19.
              unfold Included in H13; apply H13 in H19.
              unfold Element_U in H19; apply AxiomII in H19.
              destruct H19, H20, H20; exists x0; split; auto.
              apply MKT4; tauto.
            * unfold Singleton in H10; apply AxiomII in H19.
              New H10; apply MKT19 in H20; destruct H19.
              apply H21 in H20.
              
              apply MKT49b in H10. destruct H10. 
              symmetry in H20. apply MKT55 in H20. destruct H20.
              unfold Element_U.
              apply AxiomII; split; auto; exists E; rewrite <- H23.
              split; auto; apply MKT4; right.
              unfold Singleton; apply AxiomII; split; unfold Ensemble; eauto.
              auto. auto.
          + intros; unfold ProperIncluded in H15; destruct H15.
            assert(Function F /\ Function (F ∪ [[E, e]]) /\ 
            F ⊂ (F ∪ [[E, e]])); auto; clear H11; rename H20 into H11.
            apply Included_Function in H11; destruct H11.
            rewrite H17 in H18; apply MKT4 in H18; destruct H18.
            * rewrite <- H12 in H18; New H18; apply H14 in H18.
              apply H20 in H21; rewrite <- H21; auto.
            * unfold Singleton in H18; apply AxiomII in H18; destruct H18.
              assert (Ensemble E); unfold Ensemble; eauto.
              apply MKT19 in H22; apply H21 in H22.
              assert (E ∈ dom(F ∪ [[E, e]])).
              { rewrite H17; apply MKT4; right.
                unfold Singleton; apply AxiomII; auto. }
              apply Property_Value in H23; auto.
              assert ([E,e] ∈ (F ∪ [[E, e]])).
              { apply MKT4; right.
                unfold Singleton; apply AxiomII; auto. }
              pattern E at 3 in H23; rewrite <- H22 in H23.
              assert([E, (F ∪ [[E, e]]) [x]] ∈ F ∪ [[E, e]] /\ 
              [E, e] ∈ (F ∪ [[E, e]])); auto; clear H23; rename H25 into H23.
              unfold Function in H16; destruct H16, H23.
              apply (H25 E ((F ∪ [[E, e]]) [x])  e) in H26.
              rewrite H26; rewrite H22; auto.
              auto. }
  - rewrite H4 in H5.
    unfold Choice_Function' in H5; unfold Choice_Function.
    destruct H5, H6, H7, H8; repeat split; try apply H6; auto.
    unfold Included; intros; unfold Included in H8.
    apply H8 in H10; unfold Element_U in H10.
    apply AxiomII in H10; destruct H10, H11, H11.
    unfold Setminus in H12; apply MKT4' in H12.
    destruct H12; unfold PowerClass in H12.
    apply AxiomII in H12; destruct H12.
    unfold Included in H14; apply H14 in H11; auto.
Qed.

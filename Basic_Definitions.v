(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export MK_Theorems1.

(** Some necessary and additional definitions for the proof **)

(* Nest *)

Definition Nest f : Prop := forall A B, A∈f /\ B∈f -> A⊂B \/ B⊂A.



(* Finite Characteristic Set *)

Definition FiniteSet f : Prop :=
  Ensemble f /\ (forall F, F∈f -> (forall z, z ⊂ F /\ Finite z -> z∈f))
  /\ (forall F, Ensemble F /\ (forall z, z ⊂ F /\ Finite z -> z∈f) -> F∈f).


(* Property of Finite Characteristic Set *)

Proposition Property_FinSet : forall f: Class,
  FiniteSet f /\ f ≠ Φ -> (forall A B, A ∈ f /\ B ⊂ A -> B ∈ f)
  /\ (forall φ, φ ⊂ f /\ Nest φ -> (∪φ) ∈ f).
Proof.
  intros; destruct H.
  unfold FiniteSet in H; destruct H; split; intros.
  - destruct H2; apply H1; intros; split.
    + apply MKT33 in H3; unfold Ensemble; eauto.
    + intros; destruct H4; apply H1 with (z:=z) in H2; auto.
      split; try ( apply MTK28 with (y:=B); split); auto.
      apply (MKT28 H4 H3).
  - destruct H2; apply H1.
    split;try (apply AxiomVI; apply MKT33 in H2); auto.
    intro A; intros; destruct H4; unfold Finite in H5.
    generalize (classic (φ = Φ)); intros; destruct H6.
    + rewrite H6 in *; clear H6; rewrite MKT24' in H4.
      assert(H8: A ⊂ Φ /\ Φ ⊂ A). {split; auto; apply MKT26. }
      try apply (MKT26 A); apply MKT27 in H8.
      rewrite H8 in *; clear H4; apply NEexE in H0.
      destruct H0; generalize (MKT26 x); intros.
      apply H1 with (z:= Φ) in H0; auto.
    + assert (Ensemble A).
      { apply MKT33 in H2; auto; apply AxiomVI in H2.
        apply MKT33 in H4; auto. }
      New H7. apply MKT153 in H8; apply MKT146 in H8.
      assert (forall D, D ∈ \{ λ D, D ≈ P [A] /\ D ⊂ ∪ φ \} ->
              exists B, B ∈ φ /\ D ⊂ B).
      { apply Mathematical_Induction with (n:= P[A]); auto; intros.
        - apply AxiomII in H9; destruct H9, H10.
          generalize (classic (D = Φ)); intros; destruct H12.
          + rewrite H12 in *; apply NEexE in H6; destruct H6.
            exists x; split; auto; apply MKT26.
          + unfold Equivalent in H10; destruct H10 as [g H10], H10, H13, H10.
            apply NEexE in H12; destruct H12; rewrite <- H13 in H12.
            apply Property_Value in H12; auto; apply Property_ran in H12.
            rewrite H14 in H12; apply MKT16 in H12; contradiction.
        - clear H H0 H2 H4 H5 H6 H7 H8 A.
          apply AxiomII in H11; destruct H11, H0.
          unfold Equivalent in H0; destruct H0 as [g H0], H0, H0, H4.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply MKT4; right; unfold Singleton.
            apply AxiomII; split; unfold Ensemble; eauto. }
          rewrite <- H6 in H7; unfold Range in H7; apply AxiomII in H7.
          destruct H7, H8; New H8; apply Property_dom in H11.
          rewrite H4 in H11.
          assert ((D ~ [x]) ∈ \{ λ D0, D0 ≈ k /\ D0 ⊂ ∪ φ \}).
          { apply AxiomII; repeat split.
            - unfold Setminus; apply MKT33 with (x:= D); auto.
              unfold Included; intros; apply MKT4' in H12; apply H12.
            - clear H10 H1; unfold Equivalent; exists (g | (D ~ [x])).
              repeat split; unfold Relation; intros.
              + unfold Restriction in H1; apply MKT4' in H1.
                destruct H1; PP H10 a b; unfold Ensemble; eauto.
              + apply MKT4' in H1; apply MKT4' in H10.
                destruct H1 as [H1 _], H10 as [H10 _].
                apply H0 with (x:= x0); auto.
              + PP H1 a b; unfold Ensemble; eauto.
              + apply AxiomII' in H1; apply AxiomII' in H10.
                destruct H1, H10; apply MKT4' in H12; apply MKT4' in H13.
                destruct H12 as [H12 _], H13 as [H13 _]; apply H5 with (x:=x0).
                apply AxiomII'; unfold Ensemble; eauto.
                apply AxiomII'; unfold Ensemble; eauto.
              + apply AxiomI; split; intros.
                * unfold Domain in H1; apply AxiomII in H1; destruct H1, H10.
                  unfold Restriction in H10; apply MKT4' in H10; destruct H10.
                  unfold Cartesian in H12; apply AxiomII' in H12; apply H12.
                * unfold Domain; apply AxiomII; split; unfold Ensemble; eauto.
                  New H1; unfold Setminus in H10; apply MKT4' in H10.
                  destruct H10 as [H10 _]; rewrite <- H4 in H10.
                  apply Property_Value in H10; auto; exists g[z].
                  unfold Restriction; apply MKT4'; split; auto.
                  unfold Cartesian; apply AxiomII'; repeat split; unfold Ensemble; eauto.
                  assert (Ensemble ([z,g[z]])); unfold Ensemble; eauto.
                  apply MKT49b in H12; destruct H12.
                  apply MKT19; auto.
              + apply AxiomI; split; intros.
                * unfold Range in H1; apply AxiomII in H1; destruct H1, H10.
                  unfold Restriction in H10; apply MKT4' in H10.
                  destruct H10; unfold Cartesian in H12; apply AxiomII' in H12.
                  destruct H12, H13 as [H13 _]; unfold Setminus in H13.
                  apply MKT4' in H13; destruct H13; New H10.
                  apply Property_ran in H15; rewrite H6 in H15.
                  apply MKT4 in H15; destruct H15; auto; clear H1.
                  unfold Singleton in H15; apply AxiomII in H15; destruct H15.
                  rewrite H15 in H10; try apply MKT19; unfold Ensemble; eauto; clear H1 H12 H15.
                  assert ([k,x] ∈ g⁻¹ /\ [k,x0] ∈ g⁻¹).
                  { split; apply AxiomII'; split; try apply MKT49a; unfold Ensemble; eauto. }
                  assert(x = x0).
                  { destruct H1. apply H5 with (x:= k); auto. 
                  }  clear H1.
                  (*等价于destruct H1, H5. apply (H15 k x x0 H1) in H12.*)
                  rewrite <- H12 in H14; apply AxiomII in H14.
                  destruct H14, H14; apply AxiomII; auto.
                * unfold Range; apply AxiomII; split; unfold Ensemble; eauto.
                  assert (z ∈ ran(g)). { rewrite H6; apply MKT4; tauto. }
                  apply AxiomII in H10; destruct H10, H12; exists x0.
                  unfold Restriction; apply MKT4'; split; auto.
                  unfold Cartesian; apply AxiomII'; split; unfold Ensemble; eauto.
                  split; try apply MKT19; auto; unfold Setminus.
                  New H12; apply Property_dom in H13; rewrite H4 in H13.
                  apply MKT4'; split; auto; unfold Complement.
                  apply AxiomII; split; unfold Ensemble; eauto; intro; apply AxiomII in H14.
                  destruct H14; rewrite H15 in H12; try apply MKT19; unfold Ensemble; eauto.
                  assert(k = z).
                  { apply H0 with (x:= x); auto. 
                  } clear H8.
                  (*same up*)
                  rewrite H16 in H1.
                  generalize (MKT101 z); intros; contradiction.
            - unfold Included, Setminus; intros; apply MKT4' in H12.
              destruct H12; apply H2 in H12; auto. }
          apply H10 in H12; clear H10; destruct H12 as [B H12]; apply H2 in H11.
          clear H4 H6 H0 H5 H7 H8; apply AxiomII in H11; destruct H11.
          destruct H4 as [C H4], H4, H12; assert (B ∈ φ /\ C ∈ φ); auto.
          unfold Nest in H3; apply H3 in H8; destruct H8.
          + pose proof @MKT28 (D ~ [x]) B C. eapply H10 in H7; eauto.
            (*assert(D ~ [x] ⊂ C).
                  { apply (MKT28 H7 H8). }*)
            clear H8.
            exists C; split; auto; unfold Included; intros.
            generalize (classic (z = x)); intros; destruct H11.
            * rewrite H11; auto.
            * apply H7. unfold Setminus; apply MKT4'; split; auto.
              unfold Complement; apply AxiomII; split; unfold Ensemble; eauto; intro.
              destruct H11; apply AxiomII in H12; apply H12.
              apply MKT19; auto.
          + apply H8 in H4; clear H8; exists B; split; auto; unfold Included.
            intros; generalize (classic (z = x)); intros; destruct H10.
            * rewrite H10; auto.
            * apply H7; unfold Setminus; apply MKT4'; split; auto.
              unfold Complement; apply AxiomII; split; unfold Ensemble; eauto; intro.
              destruct H10; apply AxiomII in H11; apply H11.
              apply MKT19; auto. }
    assert (A ∈ \{ λ D0, D0 ≈ P [A] /\ D0 ⊂ ∪ φ \}).
    { apply AxiomII; repeat split; auto. }
    apply H9 in H10; clear H9; destruct H10 as [B H10], H10.
    apply H2 in H9; apply H1 with (z:= A) in H9; auto.
Qed.

(* MKT A.3 Proper Subset *)

Definition ProperIncluded x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperIncluded x y) (at level 70).

Corollary Property_ProperIncluded : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperIncluded; auto.
Qed.



Proposition imply_to_and : ∀ P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros; split. apply NNPP; red.
  intro; apply H; intro; absurd P; trivial. tauto.
Qed.

(*pre有*)
Proposition not_ex_all_not :
 ∀ U P, ~ (∃ n : U, P n) -> ∀ n : U, ~ P n.
Proof.
  intros. intro. elim H; eauto.
Qed.

(* ∀ U (P : U -> Prop) 对； ∀ U P 错*)
Proposition not_all_ex_not :
∀ U (P : U -> Prop), ~ (∀ n : U, P n) -> ∃ n : U, ~ P n.
Proof.
  intros U P H; apply NNPP; intro H0; apply H; intro n.
  apply NNPP; intro H1; apply H0; exists n; apply H1.
Qed.

Corollary Property_ProperIncluded' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperIncluded in H; destruct H.
  generalize (MKT27 x y); intros.
  assert( ~ (x ⊂ y /\ y ⊂ x) ). 
  { unfold not; intros; destruct H1; apply H1 in H2; auto. }
  apply notandor in H2; destruct H2; try tauto.
  unfold Included in H2. apply not_all_ex_not in H2. destruct H2.
  apply imply_to_and in H2; unfold Ensemble; eauto.
Qed.

Corollary Property_ProperIncluded'' : forall (x y: Class),
  x ⊂ y \/ y ⊂ x -> ~ (x ⊂ y) -> y ⊊ x.
Proof.
  intros; destruct H.
  - elim H0; auto.
  - unfold ProperIncluded; split; auto.
    intro; rewrite H1 in H.
    pattern x at 2 in H; rewrite <- H1 in H.
    contradiction.
Qed.

(* Maximial Member : F is a maximal member of f iff no member of f is properly contained in F. [K55] *)

Definition MaxMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ F ⊊ x).



(* Minimial Member : Similarly F is a minimal member of f iff no member of f is properly contained in F. [K55] *)

Definition MinMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ x ⊊ F).



(* Choice Function *)

Definition Choice_Function ε X : Prop :=
  Function ε /\ ran(ε) ⊂ X /\ dom(ε) = pow(X)~[Φ] /\ 
  (forall A, A ∈ dom(ε) -> ε[A] ∈ A).


(** Order **)

(* Partial Order, Partially Ordered Set *)

Definition Reflexivity le X := forall a, a∈X -> Rrelation a le a.

Definition Antisymmetry le X :=
  forall x y, x∈X /\ y∈X -> (Rrelation x le y /\ Rrelation y le x -> x = y).

Definition Transitivity r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x) /\
  (Rrelation u r v /\ Rrelation v r w) -> Rrelation u r w.

Definition PartialOrder le X : Prop :=
  Ensemble X /\ (Relation le /\ le ⊂ X × X) /\
  Reflexivity le X /\ Antisymmetry le X /\ Transitivity le X.

Definition PartialOrderSet X le := PartialOrder le X.



(* Upper Bound, Lower Bound *)

Definition BoundU x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation a le x).

Definition BoundD x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation x le a).


(* Maximal Element : We say that x∈X is a maximal element if *)

Definition MaxElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation x le y /\ x ≠ y)).

(* Minimal Element *)

Definition MinElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation y le x /\ x ≠ y)).



(* Total Order, Totally Ordered Set *)

Definition TotalOrder le X := 
  PartialOrder le X /\ (forall x y, x∈X /\ y∈X ->
  (x ≠ y -> Rrelation x le y \/ Rrelation y le x)).

Definition TotalOrderSet X le := TotalOrder le X.


(* Chain *)

Definition Chain A X le : Prop :=
  PartialOrder le X -> (A ⊂ X /\ A ≠ Φ) /\ TotalOrder (le ∩ (A × A)) A.


(* Well Order Set *)

Definition WellOrder le X :=
  TotalOrder le X /\ (forall A, A⊂X /\ A≠Φ -> exists z, MinElement z A le).

Definition WellOrderSet X le := WellOrder le X.


(* Initial_Segment *)

Definition Initial_Segment Y X le := Y ⊂ X /\ WellOrder le X /\
  (forall u v, (u ∈ X /\ v ∈ Y /\ Rrelation u le v ) -> u ∈ Y).





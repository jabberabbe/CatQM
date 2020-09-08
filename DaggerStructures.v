Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
From mathcomp.ssreflect Require Import ssrnat fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Structure.Monoidal.Symmetric.
Require Export CatQM.Notation.
Require Export CatQM.Dagger.
Require Import CatQM.Monoidal.
Require Import CatQM.Biproduct.
Require Import CatQM.Superposition.
Require Import CatQM.Zero.
Require Import CatQM.BigOps.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section DaggerStructures.
Context {C : Category}.

Class DaggerMonoidal := {
    dagger_structure :> @Dagger C;
    monoidal_structure :> @Monoidal C;
    dagger_tensor {A B X Y : C} (f : A ~> B) (g : X ~> Y) : dagger (f ⨂ g) ≈ (dagger f) ⨂ (dagger g);
    tensor_assoc_unitary {X Y Z : C} : unitary (tensor_assoc (x:=X) (y:=Y) (z:=Z));
    unit_left_unitary {X : C} : unitary (unit_left (x:=X));
    unit_right_unitary {X : C} : unitary (unit_right (x:=X))
}.

Class DaggerSymMonoidal := {
    dagger_monoidal_structure :> DaggerMonoidal;
    symmetric_monoidal_structure :> SymmetricMonoidal;
    twist_unitary {X Y : C} : unitary (twist (x:=X) (y:=Y))
}.

Class DaggerBiproduct := {
    dagger_biprod_structure :> DaggerSymMonoidal;
    superpos_structure :> @Superposition C;
    zero_structure :> @Zero C;
    biproduct_structure :> @Biproduct C superpos_structure zero_structure;
    inj_l_dagger {X Y : C} : dagger (inj_l (X:=X) (Y:=Y)) ≈ proj_l;
    inj_r_dagger {X Y : C} : dagger (inj_r (X:=X) (Y:=Y)) ≈ proj_r
}.

Lemma adj_row `{_ : DaggerBiproduct} {A B D : C} (f : A ~> B) (g : A ~> D) :
    (inj_l ∘ f ⨥ inj_r ∘ g)† ≈ ((f† ∘ proj_l) ⨥ (g† ∘ proj_r)).
Proof.
    rewrite <- id_right, -> id_biprod, <- inj_l_dagger, <- inj_r_dagger.
    rewrite -> sum_comp_r.
    rewrite <- (dagger_involutive (inj_l ∘ inj_l †)), <- (dagger_involutive (inj_r ∘ inj_r †));
    rewrite <- !dagger_compose;
    rewrite -> (dagger_compose (inj_l †) (inj_l)), -> dagger_involutive, -> inj_l_dagger;
    rewrite -> (dagger_compose (inj_r †) (inj_r)), -> dagger_involutive, -> inj_r_dagger.
    rewrite <- !comp_assoc, -> !sum_comp_r;
    rewrite -> !(comp_assoc proj_l inj_l f), -> !(comp_assoc proj_l inj_r g),
        -> !(comp_assoc proj_r inj_l f), -> !(comp_assoc proj_r inj_r g);
    rewrite <- proj_inj_l, <- proj_inj_r, <- proj_inj_lr, <- proj_inj_rl, -> !id_left.
    rewrite -> !comp_through_zero_l, -> !comp_through_zero_r, <- !zero_unit_iso,
        -> sum_unit, -> (sum_comm (Superposition.unit)), sum_unit.
    reflexivity.
Qed.

Lemma adj_col `{_ : DaggerBiproduct} {A B D : C} (f : A ~> D) (g : B ~> D) :
    (f ∘ proj_l ⨥ g ∘ proj_r)† ≈ (inj_l ∘ f†) ⨥ (inj_r ∘ g†).
Proof.
    rewrite <- (dagger_involutive f), <- (dagger_involutive g).
    rewrite <- adj_row. rewrite -> !dagger_involutive. reflexivity.
Qed.

Lemma adj_superpos `{_ : DaggerBiproduct} {A B : C} (f g : A ~> B) : (f ⨥ g)† ≈ f† ⨥ g†.
Proof.
    have hyp : (f ∘ id ⨥ g ∘ id) ≈ (f ∘ proj_l ⨥ g ∘ proj_r) ∘ (inj_l ∘ id ⨥ inj_r ∘ id) by
        symmetry; apply biprod_compose.
    rewrite <- (id_right f), <- (id_right g), -> hyp.
    rewrite -> dagger_compose, -> adj_row, -> adj_col.
    rewrite -> biprod_compose. rewrite -> !dagger_id, -> !id_left, -> !id_right.
    reflexivity.
Qed.

Definition prob `{_ : DaggerMonoidal} {A : C} (st : I ~> A) (ef : A ~> I) : scalar := st† ∘ ef† ∘ ef ∘ st.

Definition completeEffects `{_ : DaggerBiproduct} {A : C} {maxn : nat} (f : ordinal (maxn.+1)%N -> A ~> I) :=
    isometry (bigsum f).

Definition dagger_kernel `{_ : @Dagger C} `{_ : @Zero C} {A B K : C} (k : K ~> A) (f : A ~> B) := (isometry k) *
    (f ∘ k ≈ through_zero) *
    (forall (X : C) (x : X ~> A), f ∘ x ≈ through_zero -> existsT (m : X ~> K), x ≈ k ∘ m). (* x factors through k *)

Lemma kernel_of_isometry `{_ : @Dagger C} `{_ : @Zero C} {A B : C} (f : A ~> B) (f_isometry : isometry f) : dagger_kernel from_zero f.
Proof.
    do 2! construct.
    + unfold isometry; rewrite -> (to_zero_unique _ id); reflexivity.
    + apply zero_unique.
    + exact to_zero.
    + rewrite <- id_left, <- f_isometry, <- comp_assoc, -> X0. unfold through_zero.
      rewrite -> comp_assoc, -> (zero_unique _ from_zero); reflexivity.
Qed.

Class DaggerKernels := {
    ker_dagger_structure :> Dagger;
    ker_zero_structure :> Zero;
    ker {A B : C} (f : A ~> B) : existsT (K : C) (k : K ~> A), dagger_kernel k f
}.

Lemma nondegeneracy `{kernels : DaggerKernels} {A B : C} (f : A ~> B) : f† ∘ f ≈ through_zero -> f ≈ through_zero.
Proof.
    move => H.
    set p := ker f†; move: p => [K [k [[ker_isom ker_zero] ker_factor]]].
    move: (ker_factor _ _ H) => [m m_H].
    rewrite -> m_H, <- (id_left m), <- ker_isom.
    rewrite <- comp_assoc, <- m_H.
    rewrite <- (dagger_involutive (k † ∘ f)), -> dagger_compose, -> dagger_involutive.
    rewrite -> ker_zero, -> adjoint_zero, -> comp_through_zero_r.
    reflexivity.
Qed.

End DaggerStructures.


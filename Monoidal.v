Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context {C : Category}.
Context `{M : @Monoidal C}.

Lemma ex_1_6_2_c : (@unit_right _ _ I) ∘ (@unit_right _ _ (I ⨂ I)) << (I ⨂ I) ⨂ I ~~> I >>  (@unit_right _ _ I) ∘ ((@unit_right _ _ I) ⨂ id[I]).
Proof.
    exact (to_unit_right_natural (unit_right)).
Qed.

Lemma interchange_law {a b c d e l} {f : a ~> b} {g : b ~> c} {h : d ~> e} {j : e ~> l} : (g ∘ f) ⨂ (j ∘ h) ≈ (g ⨂ j) ∘ (f ⨂ h).
Proof.
    rewrite -> bimap_comp.
    reflexivity.
Qed.

Lemma from_unit_identity : (unit_left (x:=I))⁻¹ ≈ (unit_right (x:=I))⁻¹.
Proof.
    have H : (unit_left (x:=I))⁻¹ ∘ unit_left ≈ (unit_right (x:=I))⁻¹ ∘ unit_right.
        by rewrite -> !iso_from_to; reflexivity.
    rewrite -> unit_identity in H.
    by apply epic in H.
Qed.

Definition scalar := I ~> I.

Lemma unit_left_id_tensor {X Y} (b : X ~> Y) : b ≈ unit_left ∘ (id[I] ⨂ b) ∘ (from unit_left).
Proof.
    have H : b ∘ unit_left ≈ unit_left ∘ (id{C} ⨂ b) by
        exact: to_unit_left_natural b.
    pose tmp_term1 := (unit_left ∘ id{C} ⨂ b);
    rewrite -/(@tmp_term1 M).
    do 2 (rewrite <- id_right; symmetry).
    rewrite <- (iso_to_from unit_left).
    rewrite -> comp_assoc; symmetry.
    pose rhs_lock := b ∘ unit_left ∘ unit_left⁻¹;
    rewrite -/(@rhs_lock M).
    rewrite <- comp_assoc, -> (comp_assoc _ unit_left _).
    rewrite -> (iso_from_to unit_left), id_left.
    rewrite /tmp_term1 /rhs_lock.
    rewrite -> H. reflexivity.
Qed.

Lemma scalars_commute {a b : scalar} : a ∘ b ≈ b ∘ a.
Proof.
    have commute_bottom : (a ⨂ id[I]) ∘ (id[I] ⨂ b) ≈ (id[I] ⨂ b) ∘ (a ⨂ id[I]).
        rewrite <- !interchange_law.
        rewrite -> !id_left, !id_right; reflexivity.
    have commute_side_a_front : a ∘ (@unit_right _ _ I) ≈ (@unit_right _ _ I) ∘ (a ⨂ id[I])
        by rewrite -> to_unit_right_natural; reflexivity.
    have commute_side_a_back : from (@unit_right _ _ I) ∘ a ≈ (a ⨂ id[I]) ∘ from (@unit_right _ _ I)
        by rewrite -> from_unit_right_natural; reflexivity.
    rewrite -> (@unit_left_id_tensor I I b), -> !comp_assoc.
    rewrite -> !unit_identity, commute_side_a_front.
    rewrite <- (comp_assoc unit_right _ _ ), -> commute_bottom.
    pose lhs_lock := unit_right ∘ (id{C} ⨂ b ∘ a ⨂ id{C}) ∘ unit_left⁻¹;
    rewrite -/lhs_lock.
    rewrite <- !comp_assoc, -> from_unit_identity, -> commute_side_a_back, <- from_unit_identity.
    rewrite /lhs_lock; rewrite -> !comp_assoc; reflexivity.
Qed.

Definition scalar_mul {X Y} (a : scalar) (f : X ~> Y) := unit_left ∘ (a ⨂ f) ∘ unit_left⁻¹.
Notation "f ⋅ h" := (@scalar_mul _%object _%object f%morphism h%morphism)
    (at level 38, left associativity) : morphism_scope.

Lemma id_scalar_mul {X Y} (f : X ~> Y) : id[I] ⋅ f ≈ f.
Proof.
    rewrite /scalar_mul. rewrite <- unit_left_id_tensor; reflexivity.
Qed.

Lemma scalar_mul_scalars (a b : scalar) : a ⋅ b ≈ a ∘ b.
Proof.
    rewrite /scalar_mul.
    pose lhs_lock := unit_left ∘ a ⨂ b ∘ unit_left⁻¹; rewrite -/lhs_lock.
    rewrite -> (unit_left_id_tensor b), -> !comp_assoc.
    have H : a ∘ (@unit_right _ _ I) ≈ (@unit_right _ _ I) ∘ (a ⨂ id[I])
        by rewrite -> to_unit_right_natural; reflexivity.
    rewrite <- !unit_identity in H; rewrite -> H.
    rewrite <- (comp_assoc unit_left), <- interchange_law, -> id_left, -> id_right.
    rewrite -/lhs_lock; reflexivity.
Qed.

Lemma comp_mul_scalar {X Y Z} (a b : scalar) (f : X ~> Y) (g : Y ~> Z) : (b ⋅ g) ∘ (a ⋅ f) ≈ (b ∘ a) ⋅ (g ∘ f).
Proof.
    rewrite /scalar_mul.
    rewrite -> !comp_assoc, <- (comp_assoc _ _ unit_left), -> iso_from_to, -> id_right.
    rewrite -> interchange_law, -> !comp_assoc. reflexivity.
Qed.

Lemma triangle_identity_inv {x y} : unit_right⁻¹ ⨂ id << (x ⨂ y) ~~> (x ⨂ I) ⨂ y >> tensor_assoc⁻¹ ∘ (id ⨂ unit_left⁻¹).
Proof.
    have tri_ident : bimap unit_right id << (x ⨂ I) ⨂ y ~~> x ⨂ y >> bimap id unit_left ∘ tensor_assoc
        by rewrite -> (triangle_identity (x:=x) (y:=y)); reflexivity.
    have H1 : unit_right ⨂ id{C} ∘ (tensor_assoc  (x:=x) (y:=I) (z:=y))⁻¹ ≈ id{C} ⨂ unit_left
        by rewrite -> tri_ident, <- !comp_assoc, -> iso_to_from, -> id_right; reflexivity.
    have H2 : unit_right ⨂ id{C} ∘ (tensor_assoc  (x:=x) (y:=I) (z:=y))⁻¹ ∘ (id ⨂ unit_left⁻¹) ≈ id.
        rewrite -> tri_ident, <- (comp_assoc _ tensor_assoc _).
        rewrite -> iso_to_from, -> id_right, <- interchange_law.
        rewrite -> id_right, -> iso_to_from, -> bimap_id_id; reflexivity.
    rewrite <- id_right.
    rewrite <- H2. 
    rewrite -> !comp_assoc, <- interchange_law, -> iso_from_to, -> id_right.
    rewrite -> bimap_id_id, -> id_left; reflexivity.
Qed.

Lemma tensor_assoc_naturality {X Y Z X' Y' Z'} (f : X ~> X') (g : Y ~> Y') (h : Z ~> Z') : f ⨂ (g ⨂ h) ≈ tensor_assoc ∘ (f ⨂ g) ⨂ h ∘ tensor_assoc⁻¹.
Proof.
    have H : f ⨂ g ⨂ h ∘ tensor_assoc ≈ tensor_assoc ∘ (f ⨂ g) ⨂ h
        by apply to_tensor_assoc_natural.
    rewrite <- id_right, <- (iso_to_from tensor_assoc), -> comp_assoc.
    rewrite -> H; reflexivity.
Qed.

Lemma scalar_mul_assoc {X Y} (a b : scalar) (f : X ~> Y) : a ⋅ (b ⋅ f) ≈ (a ⋅ b) ⋅ f.
Proof.
    rewrite {1}/scalar_mul.
    have H : a ⨂ (unit_left  ∘ b ⨂ f ∘ unit_left⁻¹) ≈ (unit_left ∘ a ⨂ b ∘ unit_left⁻¹) ⨂ f; last first.
        by rewrite -> H; reflexivity.
    pose rhs_lock := (unit_left ∘ a ⨂ b ∘ unit_left⁻¹) ⨂ f; rewrite -/(rhs_lock M).
    rewrite <- (id_right a), <- (id_left a).
    do 2 (rewrite -> interchange_law).
    pose lhs_lock := id{C} ⨂ unit_left ∘ a ⨂ b ⨂ f ∘ id{C} ⨂ unit_left⁻¹; rewrite -/(lhs_lock M) /rhs_lock.
    rewrite <- (id_right f), <- (id_left f).
    do 2 (rewrite -> interchange_law).
    rewrite /lhs_lock.
    rewrite -> tensor_assoc_naturality.
    (* qui viene il bello *)
    rewrite -> !comp_assoc; rewrite <- triangle_identity.
    rewrite <- !comp_assoc; rewrite <- triangle_identity_inv.
    rewrite -> from_unit_identity, -> unit_identity. reflexivity.
Qed.

End Monoidal.

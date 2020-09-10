Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import CatQM.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Zero.

Context {C : Category}.

Class Zero := {
    terminal :> @Terminal C;
    initial :> @Initial C;
    terminal_initial_iso : 0 ≈ 1
}.

End Zero.

Definition from_zero `{T : @Zero C} {X} : 0 ~{C}~> X := @zero C initial _.
Definition to_zero `{T : @Zero C} {X} : X ~> 0 := terminal_initial_iso⁻¹ ∘ one.
Definition through_zero `{T : @Zero C} {X Y : C} : X ~{C}~> Y := (from_zero (X:=Y)) ∘ (to_zero (X:=X)).

Lemma to_zero_unique `{T : @Zero C} {X : C} (f g : X ~> 0) : f ≈ g.
Proof.
     have H : (terminal_initial_iso ∘ f ≈ terminal_initial_iso ∘ g).
        by apply one_unique.
    by exact (@monic _ _ _ _(iso_to_monic terminal_initial_iso) X f g H).
Qed.

Global Program Definition zero_tensor_zero `{M : @Monoidal C} `{T : @Zero C} : 0 ⨂ 0 ≅ (0 : C) := {|
    to := (unit_left (x:=0)) ∘ ((from_zero (X:=I)) ⨂ id{C});
    from := ((to_zero (X:=I)) ⨂ id{C}) ∘ (unit_left (x:=0))⁻¹
|}.
Next Obligation.
    rewrite <- comp_assoc, -> (comp_assoc _ unit_left _).
    rewrite -> iso_from_to, -> id_left.
    rewrite <- interchange_law.
    rewrite -> id_right, -> (to_zero_unique (to_zero ∘ from_zero) id).
    rewrite -> bimap_id_id; reflexivity.
Defined.

Lemma comp_through_zero_r `{T : @Zero C} {X Y Z : C} (f : Y ~> Z) : f ∘ through_zero ≈ (through_zero (X:=X) (Y:=Z)).
Proof.
    rewrite /through_zero; rewrite -> comp_assoc.
    rewrite -> (zero_unique (f ∘ from_zero)); reflexivity.
Qed.

Lemma comp_through_zero_l `{T : @Zero C} {X Y Z : C} (f : X ~> Y) : through_zero ∘ f ≈ (through_zero (X:=X) (Y:=Z)).
Proof.
    rewrite /through_zero; rewrite <- comp_assoc.
    rewrite -> to_zero_unique; reflexivity.
Qed.


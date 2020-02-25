Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import CatQM.Zero.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "⨥" (at level 50, left associativity).

Section Superposition.

Context {C : Category}.

Class Superposition := {
    sum {X Y : C} (f : X ~> Y) (g : X ~> Y) : X ~> Y
        where "f + g" := (sum f g);
    sum_comm {X Y} (f g : X ~> Y) : f + g ≈ g + f;
    sum_assoc {X Y} (f g h : X ~> Y) : (f + g) + h ≈ f + (g + h);
    unit {X Y} : X ~> Y;
    sum_unit {X Y} (f : X ~> Y) : f + unit ≈ f;
    sum_comp_l {X Y Z} (f : X ~> Y) (g g' : Y ~> Z) : (g + g') ∘ f ≈ (g ∘ f) + (g' ∘ f);
    sum_comp_r {X Y Z} (f f' : X ~> Y) (g : Y ~> Z) : g ∘ (f + f') ≈ (g ∘ f) + (g ∘ f');
    unit_comp {X Y Z} : (unit (X:=Y) (Y:=Z)) ∘ (unit (X:=X) (Y:=Y)) ≈ (unit (X:=X) (Y:=Z));
    sum_proper {X Y : C} :> Proper (equiv ==> equiv ==> equiv) (sum (X:=X) (Y:=Y))
}.

Lemma zero_unit_iso `{S : Superposition} `{T : @Zero C} {X Y : C} : (unit (X:=X) (Y:=Y)) ≈ (through_zero (X:=X) (Y:=Y)).
Proof.
    rewrite <- (unit_comp (Y:=0)).
    rewrite /through_zero.
    have H1 : (unit (X:=0) (Y:=Y)) ≈ from_zero.
        by apply (zero_unique unit from_zero).
    have H2 : (unit (X:=X) (Y:=0)) ≈ to_zero.
        by apply to_zero_unique.
    by rewrite -> H1, -> H2; reflexivity.
Qed.

End Superposition.

Notation "a ⨥ b" := (@sum _ _ _ _ a b).

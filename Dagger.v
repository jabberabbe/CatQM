Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Functor.Opposite.
Require Import CatQM.Zero.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Dagger.
Context {C : Category}.

Class Dagger := {
    dagger {X Y : C} : (X ~> Y) -> (Y ~> X);
    dagger_involutive {X Y : C} (f : X ~> Y) : dagger (dagger f) ≈ f;
    dagger_id {X : C} : dagger id[X] ≈ id;
    dagger_compose {X Y Z : C} (f : X ~> Y) (g : Y ~> Z) : dagger (g ∘ f) ≈ (dagger f) ∘ (dagger g);
    dagger_respects {X Y : C} :> Proper (equiv ==> equiv) (dagger (X:=X) (Y:=Y))
}.

Program Definition dagger_functor `{D : Dagger} : C^op ⟶ C := {|
    fobj a := a;
    fmap _ _ := dagger
|}.
Next Obligation. exact dagger_id. Defined.
Next Obligation. apply dagger_compose. Defined.

(*
Lemma contravariant_iso {X Y : C} {F : C^op ⟶ C} (f : Isomorphism X Y) : (fmap (op f) ∘ fmap (op f⁻¹) ≈ id) * (fmap (op f⁻¹) ∘ fmap (op f) ≈ id).
Proof.
    construct.
    rewrite <- fmap_comp, <- compose_in_opposite; rewrite /op; rewrite -> iso_from_to, -> (@fmap_id _ _ F); reflexivity.
    rewrite <- fmap_comp, <- compose_in_opposite; rewrite /op; rewrite -> iso_to_from, -> (@fmap_id _ _ F); reflexivity.
Qed.
(*
Proof.
    construct.
    exact (fmap (op f)).
    exact (fmap (op (from f))).
    rewrite <- fmap_comp, <- compose_in_opposite; unfold op.
    rewrite -> iso_from_to; rewrite -> (@fmap_id _ _ F); reflexivity.
    rewrite <- fmap_comp, <- compose_in_opposite; unfold op.
    rewrite -> iso_to_from; rewrite -> (@fmap_id _ _ F); reflexivity.
Qed.
*)

Definition dagger `{D : Dagger} {X Y} (f : X ~> Y) : (Y ~> X) := dagger_id_obj ∘ (contramap (F:=dagger_f) f) ∘ dagger_id_obj⁻¹.
Lemma dagger_involutive `{D : Dagger} {X Y} (f : X ~> Y) : (dagger (dagger f)) ≈ f.
Proof.
    rewrite /dagger. rewrite /contramap. rewrite -> compose_in_opposite.
    Check dagger_id_obj⁻¹.
    Check dagger_id_obj ∘ fmap[dagger_f] f.
    rewrite -> fmap_comp, -> compose_in_opposite, -> fmap_comp; rewrite /op.
    destruct dagger_f_involutive.
*)

Definition unitary `{D : Dagger} {X Y} (f : X ~> Y) := (f ∘ dagger f ≈ id) * (dagger f ∘ f ≈ id).
Definition isometry `{D : Dagger} {X Y} (f : X ~> Y) := dagger f ∘ f ≈ id.
Definition self_adjoint `{D : Dagger} {X : C} (f : X ~> X) := f ≈ dagger f.
Definition positive `{D : Dagger} {X : C} (f : X ~> X) := exists (Z : C) (g : X ~> Z), f ≈ dagger g ∘ g.

Lemma adjoint_zero `{Z : @Zero C} `{D : Dagger} {X Y : C} : dagger (through_zero (X:=X) (Y:=Y)) ≈ through_zero (X:=Y) (Y:=X).
Proof.
    rewrite /through_zero; rewrite -> dagger_compose.
    rewrite -> (zero_unique (dagger to_zero) from_zero);
    rewrite -> (to_zero_unique (dagger from_zero) to_zero).
    reflexivity.
Qed.

End Dagger.

Notation "f †" := (@dagger _ _ _ _ f) (at level 7).

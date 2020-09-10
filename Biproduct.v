Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import CatQM.Zero.
Require Import CatQM.Superposition.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "⨁" (at level 42, left associativity).

Section Biproduct.

Context {C : Category}.
Context `{S' : @Superposition C}.
Context `{Z : @Zero C}.

Class Biproduct := {
    biprod (X Y : C) : obj[C]
        where "x ⨁ y" := (biprod x y);
    inj_l {X Y} : X ~> X ⨁ Y;
    inj_r {X Y} : Y ~> X ⨁ Y;
    proj_l {X Y} : X ⨁ Y ~> X;
    proj_r {X Y} : X ⨁ Y ~> Y;

    proj_inj_l {X Y} : id[X] ≈ (@proj_l X Y) ∘ (@inj_l X Y);
    proj_inj_r {X Y} : id[Y] ≈ (@proj_r X Y) ∘ (@inj_r X Y); 
    proj_inj_lr {X Y} : through_zero ≈ (@proj_l X Y) ∘ (@inj_r X Y);
    proj_inj_rl {X Y} : through_zero ≈ (@proj_r X Y) ∘ (@inj_l X Y);

    id_biprod {X Y} : id[X ⨁ Y] ≈ (inj_l ∘ proj_l) ⨥ (inj_r ∘ proj_r)
}.

Lemma proj_lr_comp_eq_uniq `{B : Biproduct} {X : C} : forall (h : X ~> (biprod X X)), proj_l ∘ h ≈ proj_r ∘ h -> proj_l ∘ h ≈ id -> h ≈ (sum inj_l inj_r).
Proof.
    move => h hyp0 hyp1.
    rewrite <- id_left.
    rewrite -> id_biprod. rewrite -> sum_comp_l.
    rewrite <- !comp_assoc. rewrite <- hyp0, -> !hyp1.
    by rewrite -> !id_right; reflexivity.
Qed.

Lemma comp_inj_lr_eq_uniq `{B : Biproduct} {X Y : C} (f g : X ~> Y) : forall h : (biprod X X) ~> Y, h ∘ inj_l ≈ f -> h ∘ inj_r ≈ g -> h ≈ sum (f ∘ proj_l) (g ∘ proj_r).
Proof.
    move => h hyp0 hyp1.
    rewrite <- id_right, -> id_biprod.
    rewrite -> sum_comp_r, -> !comp_assoc.
    rewrite -> hyp0, -> hyp1.
    reflexivity.
Qed.

Lemma biprod_compose `{_ : Biproduct} {X A B Y : C} (f : X ~> A) (g : X ~> B) (h : A ~> Y) (i : B ~> Y) : (h ∘ proj_l ⨥ i ∘ proj_r) ∘ (inj_l ∘ f ⨥ inj_r ∘ g) ≈ h ∘ f ⨥ i ∘ g.
Proof.
    rewrite -> sum_comp_l, -> !sum_comp_r, <- !comp_assoc, -> !(comp_assoc proj_l _ _), -> !(comp_assoc proj_r _ _).
    rewrite <- proj_inj_l, <- proj_inj_r, <- proj_inj_lr, <- proj_inj_rl.
    rewrite -> !id_left, -> !comp_through_zero_l, -> !comp_through_zero_r, <- !zero_unit_iso, -> (sum_comm unit), -> !sum_unit.
    reflexivity.
Qed.

End Biproduct.

Notation "a ⨁ b" := (@biprod _ _ _ _ a b).

Lemma stupid_identity `{B : Biproduct} {S : Superposition} {X Y : C} (f g : X ~> Y) : (@sum _ S _ _ (f ∘ proj_l) (g ∘ proj_r)) ∘ (@sum _ S _ _ inj_l inj_r) ≈ sum f g.
Proof.
    rewrite -> sum_comp_l.
    rewrite <- !comp_assoc, -> (sum_comp_r _ _ proj_l), -> (sum_comp_r _ _ proj_r).
    rewrite <- proj_inj_l, <- proj_inj_r, <- proj_inj_lr, <- proj_inj_rl.
    rewrite <- zero_unit_iso, -> (sum_comm unit _), -> sum_unit.
    rewrite -> !id_right. reflexivity.
Qed.

Lemma unique_superposition `{B : Biproduct} {S'' : @Superposition C} :
    forall (X Y : C) (f g : X ~> Y),  (@sum C S' X Y f g) ≈ (@sum C S'' X Y f g).
Proof.
    move => X Y f g.
    rewrite <- stupid_identity.
    have H0 : (@sum C S' X (X ⨁ X) inj_l inj_r) ≈ (@sum C S'' X (X ⨁ X) inj_l inj_r).
        symmetry; apply proj_lr_comp_eq_uniq.

        rewrite -> !sum_comp_r.
        rewrite <- proj_inj_l, <- proj_inj_r, <- proj_inj_lr, <- proj_inj_rl.
        rewrite <- zero_unit_iso, -> (sum_comm unit _), -> sum_unit; reflexivity.

        rewrite -> !sum_comp_r.
        rewrite <- proj_inj_l, <- proj_inj_lr.
        rewrite <- zero_unit_iso, -> sum_unit; reflexivity.
    
    have H1 : (@sum C S' _ _ (f ∘ proj_l) (g ∘ proj_r)) ≈ (@sum C S'' _ _ (f ∘ proj_l) (g ∘ proj_r)).
        symmetry; apply comp_inj_lr_eq_uniq.

        rewrite -> !sum_comp_l.
        rewrite <- !comp_assoc, <- proj_inj_l, <- proj_inj_rl.
        rewrite -> id_right; rewrite /through_zero; rewrite -> !comp_assoc;
        rewrite -> (zero_unique _ from_zero); rewrite -/through_zero.
        rewrite <- zero_unit_iso, -> sum_unit; reflexivity.

        rewrite -> !sum_comp_l.
        rewrite <- !comp_assoc, <- proj_inj_r, <- proj_inj_lr.
        rewrite -> id_right; rewrite /through_zero; rewrite -> !comp_assoc;
        rewrite -> (zero_unique _ from_zero); rewrite -/through_zero.
        rewrite -> sum_comm, <- zero_unit_iso, -> sum_unit; reflexivity.

    rewrite -> H0, -> H1.
    rewrite -> stupid_identity.
    reflexivity.
Qed.


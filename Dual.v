Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Structure.Monoidal.Proofs.
Require Export CatQM.Dagger.
Require Import CatQM.Monoidal.

Section Dual.
Context {C : Category} `{M : @Monoidal C}.

Class Dual (L R : C) := {
    eta : I ~> R ⨂ L;
    eps : L ⨂ R ~> I;
    dual_id_l : (eps ⨂ id) ∘ tensor_assoc⁻¹ ∘ (id ⨂ eta) ≈ unit_left⁻¹ ∘ unit_right;
    dual_id_r : (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ≈ unit_right⁻¹ ∘ unit_left
}.

Definition name   {A B A' B' : C} {dual_a : Dual A A'} {dual_b : Dual B B'} (f : A ~> B) : I ~> (A' ⨂ B) := (id ⨂ f) ∘ eta.
Definition coname {A B A' B' : C} {dual_a : Dual A A'} {dual_b : Dual B B'} (f : A ~> B) : (A ⨂ B') ~> I := eps ∘ (f ⨂ id).

Lemma double_snake_r {L R R' : C} {dual : Dual L R} {dual' : Dual L R'} : unit_right ∘ id{C} ⨂ eps ∘ tensor_assoc ∘ eta ⨂ id{C} ∘ unit_left⁻¹ ∘ (unit_right ∘ id{C} ⨂ eps ∘ tensor_assoc ∘ eta ⨂ id{C} ∘ unit_left⁻¹) ≈ (id : R ~{C}~> R).
Proof.
    do 3! [rewrite <- comp_assoc]; [rewrite -> (comp_assoc unit_left⁻¹ _ _)].
    rewrite <- from_unit_left_natural, -> !(comp_assoc (eta ⨂ id) _ _), <- interchange_law.
    rewrite -> id_right, -> id_left.
    rewrite <- (id_left eta), <- (id_right (_ ∘ (eta ⨂ id))), -> interchange_law.
    rewrite <- bimap_id_id, <- (comp_assoc _ tensor_assoc (eta ⨂ id{C})).
    rewrite <- (id_right (id{C} ⨂ id{C})), -> interchange_law, -> !(comp_assoc tensor_assoc _ _).
    rewrite <- to_tensor_assoc_natural, -> !comp_assoc, <- (comp_assoc unit_right (id ⨂ eps) _), <- interchange_law, -> id_left.
    rewrite <- (id_left id[L]), -> interchange_law, -> triangle_identity_right, -> !(comp_assoc eps _ _).

    rewrite -> to_unit_right_natural.
    rewrite <- (comp_assoc _ tensor_assoc⁻¹ _), <- from_tensor_assoc_natural.
    rewrite -> bimap_id_id, -> (comp_assoc (unit_right ∘ eps ⨂ id{C}) _ _);
    rewrite <- (comp_assoc _ (eps ⨂ id{C}) _), <- interchange_law.
    rewrite -> id_left, -> id_right. rewrite <- (id_left eps), <- (id_right (@eps _ _ dual)), -> interchange_law.
    rewrite <- !bimap_id_id.
    rewrite <- (comp_assoc _ _ tensor_assoc), <- (comp_assoc _ _ ((id{C} ⨂ id{C}) ⨂ (tensor_assoc ∘ eta ⨂ id{C}))),
    <- (comp_assoc _ tensor_assoc _). rewrite <- to_tensor_assoc_natural.
    rewrite -> (comp_assoc _ _ tensor_assoc), <- interchange_law.
    rewrite -> id_right, <- (id_right id[L]), -> interchange_law, -> (comp_assoc _ (id{C} ⨂ tensor_assoc) _), <- (comp_assoc _ tensor_assoc⁻¹ _).
    have by_pentagon_identity : tensor_assoc⁻¹ ∘ id{C} ⨂ tensor_assoc ≈ tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id ∘ tensor_assoc⁻¹.
        move => a b c d. symmetry.
        rewrite <- id_left, <- (iso_from_to tensor_assoc).
        rewrite -> !comp_assoc, <- (comp_assoc _ tensor_assoc tensor_assoc), <- pentagon_identity, -> comp_assoc.
        rewrite <- (comp_assoc _ (tensor_assoc ⨂ id)), <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        rewrite -> comp_assoc, <- (comp_assoc _ tensor_assoc _), -> iso_to_from, -> id_right.
        reflexivity.
    rewrite -> by_pentagon_identity, <- !(comp_assoc _ _ (id{C} ⨂ eta ⨂ id{C})), <- from_tensor_assoc_natural.
    rewrite -> id_right, -> !comp_assoc, <- (comp_assoc _ (eps ⨂ id{C} ⨂ id{C}) tensor_assoc).
    rewrite -> to_tensor_assoc_natural, <- (comp_assoc _ _ (tensor_assoc⁻¹ ⨂ id{C})), <- (comp_assoc _ _ ((id{C} ⨂ eta) ⨂ id{C})).
    do 2! rewrite <- (comp_assoc tensor_assoc _ _), <- interchange_law.
    rewrite -> dual_id_l.

    rewrite -> interchange_law, <- !(comp_assoc _ _ tensor_assoc⁻¹), -> (comp_assoc tensor_assoc _ _ ), -> id_right.
    rewrite <- inverse_triangle_identity, -> !comp_assoc, <- (id_right id[R]), -> interchange_law.
    rewrite -> comp_assoc. rewrite <- (comp_assoc _ (id{C} ⨂ id{C} ⨂ unit_left) tensor_assoc).
    rewrite -> to_tensor_assoc_natural, -> bimap_id_id.
    rewrite -> comp_assoc. rewrite <- (comp_assoc _ (id{C} ⨂ unit_left)).
    rewrite <- interchange_law, -> id_left, bimap_id_id, -> id_right, -> id_left, <- (id_right eta), <- (id_left unit_left).
    rewrite -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ (id{C} ⨂ unit_left) unit_left⁻¹).
    rewrite -> from_unit_left_natural, -> iso_from_to, -> id_right.
    have by_triangle_identity : tensor_assoc ∘ (unit_left⁻¹ ⨂ id) ≈ unit_left⁻¹.
        move => o1 o2.
        rewrite <- id_left, <- (iso_from_to unit_left), -> comp_assoc, <- (comp_assoc _ unit_left tensor_assoc).
        rewrite <- triangle_identity_left, <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        reflexivity.
    rewrite <- (comp_assoc _ tensor_assoc (unit_left⁻¹ ⨂ id{C})), -> by_triangle_identity.
    rewrite <- (comp_assoc _ (id ⨂ eps) unit_left⁻¹), -> from_unit_left_natural, -> comp_assoc.
    rewrite <- (id_right id[R]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ (id{C} ⨂ eps) _), -> id_right, <- (comp_assoc _ _ (eta ⨂ id)).
    rewrite -> dual_id_r.

    rewrite <- unit_identity, -> iso_to_from, -> bimap_id_id, -> id_right, -> !comp_assoc.
    rewrite -> iso_to_from, -> id_left, -> iso_to_from. reflexivity.
Qed.

Lemma right_dual_unique {L R R' : C} {dual : Dual L R} {dual' : Dual L R'} : R ≈ R'.
Proof.
    construct.
    exact (unit_right ∘ (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ∘ unit_left⁻¹).
    exact (unit_right ∘ (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ∘ unit_left⁻¹).
    all: apply double_snake_r.
Qed.

Lemma double_snake_l {L L' R : C} {dual : Dual L R} {dual' : Dual L' R} : unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹ ∘ (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹) ≈ (id : L ~> L).
Proof.
    do 3! [rewrite <- comp_assoc]; [rewrite -> (comp_assoc unit_right⁻¹ _ _)].
    rewrite <- from_unit_right_natural, -> !(comp_assoc (id ⨂ eta) _ _), <- interchange_law.
    rewrite -> id_left, -> id_right.
    set tmp_var := (id ⨂ eta); rewrite  <- (id_right (_ ∘ tmp_var)), <- (id_left eta), -> interchange_law; unfold tmp_var; move: tmp_var => _.
    rewrite <- bimap_id_id, <- (comp_assoc _ tensor_assoc⁻¹ (id ⨂ eta)).
    rewrite <- (id_right (id ⨂ id)), -> interchange_law, -> !(comp_assoc tensor_assoc⁻¹ _ _).
    rewrite <- from_tensor_assoc_natural, -> !comp_assoc, <- (comp_assoc unit_left (eps ⨂ id)), <- interchange_law, -> id_left.
    rewrite <- (id_left id[R]), -> interchange_law, -> triangle_identity_left, -> !(comp_assoc eps).

    rewrite -> to_unit_left_natural.
    rewrite <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural.
    rewrite -> bimap_id_id, -> (comp_assoc (unit_left ∘ id ⨂ eps)).
    rewrite <- (comp_assoc _ (id ⨂ eps) _), <- interchange_law.
    rewrite -> id_left, -> id_right. rewrite <- (id_right eps), <- (id_left (@eps _ _ dual')), -> interchange_law.
    rewrite <- !bimap_id_id.
    rewrite <- (comp_assoc _ _ tensor_assoc⁻¹), <- (comp_assoc _ _ ((tensor_assoc⁻¹ ∘ id{C} ⨂ eta) ⨂ id{C} ⨂ id{C})),
        <- (comp_assoc _ tensor_assoc⁻¹ _). rewrite <- from_tensor_assoc_natural.
    rewrite -> (comp_assoc _ _ tensor_assoc⁻¹). rewrite <- interchange_law.
    rewrite -> id_right, <- (id_right id[R]), -> interchange_law, -> (comp_assoc _ (tensor_assoc⁻¹ ⨂ id) _), <- (comp_assoc _ tensor_assoc _).
    have by_pentagon_identity : tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id ≈ tensor_assoc⁻¹ ∘ id ⨂ tensor_assoc ∘ tensor_assoc.
        move => a b c d. symmetry.
        rewrite <- id_left, <- (iso_to_from tensor_assoc).
        rewrite -> !comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc⁻¹), <- inverse_pentagon_identity.
        rewrite -> (comp_assoc _ _ (id ⨂ tensor_assoc⁻¹)), <- (comp_assoc _ (id ⨂ tensor_assoc⁻¹) (id ⨂ tensor_assoc)),
            <- interchange_law, -> iso_from_to, -> id_left, -> bimap_id_id, -> id_right.
        rewrite -> comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc), -> iso_from_to, -> id_right.
        reflexivity.
    rewrite -> by_pentagon_identity, <- !(comp_assoc _ _ ((id{C} ⨂ eta) ⨂ id{C})), <- to_tensor_assoc_natural.
    rewrite -> !id_right, -> !comp_assoc, <- (comp_assoc _ ((id ⨂ id) ⨂ eps) tensor_assoc⁻¹).
    rewrite -> from_tensor_assoc_natural, <- (comp_assoc _ _ (id ⨂ tensor_assoc)), <- (comp_assoc _ _ (id ⨂ eta ⨂ id)).
    do 2! rewrite <- (comp_assoc tensor_assoc⁻¹ _ _), <- interchange_law.
    rewrite -> dual_id_r.

    rewrite -> interchange_law, <- !(comp_assoc _ _ tensor_assoc), -> (comp_assoc tensor_assoc⁻¹ _ _), -> id_right.
    rewrite <- triangle_identity, -> !comp_assoc. rewrite <- (id_right id[L]), -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ ((unit_right ⨂ id{C}) ⨂ id{C}) tensor_assoc⁻¹).
    rewrite -> from_tensor_assoc_natural, -> bimap_id_id.
    rewrite -> comp_assoc, <- (comp_assoc _ (unit_right ⨂ id)), <- interchange_law.
    rewrite -> id_left, bimap_id_id, -> id_right, -> id_left.
    rewrite <- (id_right eta), <- (id_left unit_right), -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ (unit_right ⨂ id) unit_right⁻¹).
    rewrite -> from_unit_right_natural, -> iso_from_to, -> id_right.
    have by_triangle_identity : tensor_assoc⁻¹ ∘ id ⨂ unit_right⁻¹ ≈ unit_right⁻¹.
        move => o1 o2.
        rewrite <- id_left, <- (iso_from_to unit_right), -> comp_assoc, <- (comp_assoc _ unit_right _), <- triangle_identity_right.
        rewrite <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        reflexivity.
    rewrite <- (comp_assoc _ tensor_assoc⁻¹ (id{C} ⨂ unit_right⁻¹)), -> by_triangle_identity.
    rewrite <- (comp_assoc _ (eps ⨂ id) _), -> from_unit_right_natural, -> comp_assoc.
    rewrite <- (id_right id[L]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ (eps ⨂ id) _), -> id_right, <- (comp_assoc _ _ (id ⨂ eta)).
    rewrite -> dual_id_l.

    rewrite -> unit_identity, -> iso_to_from, -> bimap_id_id, -> id_right, -> !comp_assoc.
    rewrite -> iso_to_from, -> id_left, -> iso_to_from. reflexivity.
Qed.

Lemma left_dual_unique {L L' R : C} {dual : Dual L R} {dual' : Dual L' R} : L ≈ L'.
Proof.
    construct.
    exact (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹).
    exact (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹).
    all: apply double_snake_l.
 Qed.

(*
Open Scope object.
Lemma left_dual_unique {L L' R : C} {dual : Dual L R} {dual' : Dual L' R} : L ≈ L'.
Proof.
    have q : (id ⨂ tensor_assoc⁻¹) ∘ (id ⨂ tensor_assoc) ≈ id
        by move => o'1 o'2 o'3 o'4; rewrite <- interchange_law, -> id_right, -> iso_from_to, -> bimap_id_id; reflexivity.
    have inv_pentagon_identity : (id ⨂ tensor_assoc⁻¹) ∘ tensor_assoc ≈ tensor_assoc ∘ (tensor_assoc ⨂ id) ∘ tensor_assoc⁻¹.
        move => o1 o2 o3 o4.
        rewrite <- id_right, <- (iso_to_from tensor_assoc), -> !comp_assoc. symmetry.
        rewrite <- id_left, <- q. rewrite -> comp_assoc, <- (comp_assoc _ (id ⨂ tensor_assoc) _), -> (comp_assoc _ tensor_assoc _).
        rewrite -> pentagon_identity, -> !comp_assoc; reflexivity.
    construct.
    + exact (unit_left ∘ unit_right ∘ (eps ⨂ id) ⨂ id ∘ tensor_assoc⁻¹ ⨂ id ∘ (id ⨂ eta) ⨂ id ∘ unit_right⁻¹ ∘ unit_right⁻¹).
    + exact (unit_left ∘ unit_left ∘ id ⨂ (eps ⨂ id) ∘ id ⨂ tensor_assoc⁻¹ ∘ tensor_assoc ∘ (id ⨂ id) ⨂ eta ∘ unit_right⁻¹ ∘ unit_left⁻¹).
    +  have iso : exists (f : (L ⨂ I) ⨂ I ~> (I ⨂ L') ⨂ I) (g : (I ⨂ L') ⨂ I ~> I ⨂ I ⨂ L),
        (g ∘ f ≈ unit_left⁻¹ ∘ unit_left⁻¹ ∘ unit_right ∘ unit_right) *
        (f ∘ unit_right⁻¹ ∘ unit_right⁻¹ ∘ unit_left ∘ unit_left ∘ g ≈ id); last first.
        - destruct iso. destruct s. destruct p. move: x x0 e e0 => f g h h'.
        + exact (unit_left ∘ unit_right ∘ f ∘ unit_right⁻¹ ∘ unit_right⁻¹).
        + exact (unit_left ∘ unit_left ∘ g ∘ unit_right⁻¹ ∘ unit_left⁻¹).
        + admit.
        + admit.
    - construct; last construct; last construct. Open Scope morphism.
        + exact (((eps ⨂ id) ⨂ id) ∘ (tensor_assoc⁻¹ ⨂ id) ∘ ((id ⨂ eta) ⨂ id)).
        + exact (id ⨂ (eps ⨂ id) ∘ (id ⨂ tensor_assoc⁻¹) ∘ tensor_assoc ∘ (id ⨂ id) ⨂ eta).
        + have h1 : (id{C} ⨂ id{C}) ⨂ (@eta _ _ dual) ∘ (eps ⨂ id{C}) ⨂ id{C} ∘ tensor_assoc⁻¹ ⨂ id{C} ≈
          (((eps ⨂ id) ⨂ id ∘ (tensor_assoc⁻¹ ⨂ id) ∘ (id ⨂ id) ⨂ eta) : (L ⨂ (R ⨂ L')) ⨂ I ~> (I ⨂ L') ⨂ (R ⨂ L)).
            rewrite <- !interchange_law, -> !bimap_id_id, -> !id_right, -> !id_left; reflexivity.
        rewrite <- !comp_assoc, -> (comp_assoc ((id{C} ⨂ id{C}) ⨂ eta) _ _), -> (comp_assoc _ (tensor_assoc⁻¹ ⨂ id{C}) _).
        rewrite -> h1.
        have h2 : (id{C} ⨂ id{C}) ⨂ eta ∘ (id{C} ⨂ eta) ⨂ id{C} ≈
          ((id ⨂ eta) ⨂ id ∘ (id ⨂ id) ⨂ eta : (L ⨂ I) ⨂ I ~> (L ⨂ (R ⨂ L')) ⨂ (R ⨂ L)).
            rewrite <- !interchange_law, -> !id_right, -> !id_left; reflexivity.
        rewrite <- (comp_assoc _ ((id ⨂ id) ⨂ eta) _). rewrite -> h2.
        have h3 : (id{C} ⨂ eps ⨂ id{C} ∘ id{C} ⨂ tensor_assoc⁻¹ ∘ tensor_assoc ∘ (eps ⨂ id{C}) ⨂ id{C} ∘ tensor_assoc⁻¹ ⨂ id{C}) ≈
          (tensor_assoc ∘ (eps ⨂ eps ∘ tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id{C}) ⨂ id{C} ∘ tensor_assoc⁻¹ : ((L ⨂ (R ⨂ L')) ⨂ (R ⨂ L)) ~> I ⨂ I ⨂ L).
            rewrite <- (comp_assoc _ _ tensor_assoc).
            rewrite -> inv_pentagon_identity.
            rewrite <- (comp_assoc tensor_assoc), -> (comp_assoc _ tensor_assoc _), -> to_tensor_assoc_natural.
            rewrite <- !comp_assoc, -> (comp_assoc tensor_assoc⁻¹ _ _ ).
            rewrite <- bimap_id_id. Check from_tensor_assoc_natural. rewrite <- from_tensor_assoc_natural.
            rewrite <- !comp_assoc. rewrite <- from_tensor_assoc_natural.
            rewrite -> (comp_assoc _ (tensor_assoc ⨂ id) _), <- interchange_law.
            rewrite -> (comp_assoc _ (((eps ⨂ id{C}) ⨂ id{C}) ⨂ id{C}) _), <- interchange_law.
            rewrite -> (comp_assoc _ _ tensor_assoc⁻¹), <- interchange_law.
            rewrite <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural.
            rewrite -> bimap_id_id, -> !comp_assoc, <- interchange_law, -> id_left, -> !id_right. reflexivity.
          (*
          rewrite <- (comp_assoc _ _ ((id{C} ⨂ id{C} ⨂ eps) ⨂ id{C})), <- interchange_law, <- from_tensor_assoc_natural.
          rewrite <- bimap_id_id, -> to_tensor_assoc_natural.
          rewrite <- (comp_assoc _ ((id{C} ⨂ tensor_assoc) ⨂ id{C}) _), <- interchange_law.
          rewrite <- (comp_assoc (tensor_assoc ∘ (eps ⨂ id{C}) ⨂ id{C}) _ _ ), <- interchange_law.
          rewrite <- (comp_assoc tensor_assoc _ _), <- interchange_law, -> !comp_assoc, -> !id_left, -> bimap_id_id.
          have inv_pentagon_identity' : tensor_assoc⁻¹ ∘ id{C} ⨂ tensor_assoc ∘ tensor_assoc ≈ tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id{C}.
              admit.
          rewrite <- interchange_law, <- (comp_assoc _ tensor_assoc⁻¹ _), <- (comp_assoc _ _ tensor_assoc).
          rewrite -> inv_pentagon_identity', -> !comp_assoc, -> id_left, id_right. reflexivity. 
          *)

        rewrite -> !comp_assoc. rewrite -> h3.
        rewrite <- comp_assoc, <- !interchange_law.
        rewrite <- (comp_assoc tensor_assoc _ _ ). rewrite <- (id_right id[L]). rewrite -> (interchange_law).
        rewrite <- (comp_assoc _ _ tensor_assoc⁻¹).
        rewrite -> from_tensor_assoc_natural.
        rewrite -> (comp_assoc _ tensor_assoc⁻¹), -> !(comp_assoc tensor_assoc _ _ ). rewrite <- (id_right id).
        rewrite -> interchange_law, -> comp_assoc, <- to_tensor_assoc_natural.
        have inv_pentagon_identity' : tensor_assoc ∘ tensor_assoc ⨂ id{C} ∘ tensor_assoc⁻¹ ≈ id ⨂ tensor_assoc⁻¹ ∘ tensor_assoc.
            move => o0 o1 o2 o3;
            rewrite <- id_left, <- q, <- comp_assoc, -> !(comp_assoc (id{C} ⨂ tensor_assoc)).
            rewrite -> pentagon_identity.
            rewrite <- comp_assoc, -> iso_to_from, -> id_right; reflexivity.
        rewrite <- (comp_assoc _ tensor_assoc _), <- (comp_assoc _ _ tensor_assoc⁻¹).
        rewrite <- (comp_assoc tensor_assoc _ _), -> (comp_assoc _ tensor_assoc _), <- (comp_assoc _ _ (tensor_assoc⁻¹ ⨂ id{C} ⨂ (id{C} ∘ id{C}))).
        rewrite -> to_tensor_assoc_natural.
        rewrite <- (comp_assoc _ tensor_assoc⁻¹ _), <- from_tensor_assoc_natural.
        rewrite -> !comp_assoc, -> !id_right.
        Require Import Category.Structure.Monoidal.Proofs.
        symmetry. rewrite <- comp_assoc, <- comp_assoc, -> (comp_assoc _ unit_right _).
        rewrite <- dual_id_l. rewrite <- bimap_id_id.
        rewrite <- id_unit_right.
        rewrite <- id_unit_right.
        rewrite <- from_tensor_assoc_natural.
        rewrite -> inv_pentagon_identity'.
        rewrite <- (comp_assoc (eps ⨂ eps ⨂ id{C}) _ _), <- (comp_assoc _ tensor_assoc _).
        rewrite <- to_tensor_assoc_natural.
        admit.
        rewrite <- !interchange_law, -> !id_left, -> !id_right. rewrite -> dual_id_l.
        + admit.
Admitted.
*)

End Dual.

Class Compact `{C : Category} := {
    monoidal_witness :> @Monoidal C;
    dual : C -> C;
    dual_witness : forall X : C, Dual X (dual X)
}.
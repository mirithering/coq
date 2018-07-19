Require Import Utf8.
Require Import Coq.Program.Basics Setoid RelationClasses ProofIrrelevance FunctionalExtensionality.

(* Note : Remember to use eq_rect for equality between morphisms
  if necessary *)
Import EqNotations.

(* identity is unique, not sure if composition is, so I'll leave it as a parameter *)

Class Category 
  (obj : Type) 
  (hom : obj -> obj -> Type)
  (comp : forall {A B C} (f : hom B C) (g : hom A B), hom A C) := {
  cid : forall A, hom A A;
  
  idLeft: forall {A B} (f: hom A B), comp (cid B) f = f;
  idRight: forall {A B} (f : hom B A), comp f (cid B) = f;
  compAssoc: forall {A B C D} (f : hom A B) (g : hom B C) (h : hom C D),
    comp h (comp g f) = comp (comp h g) f
}.

Generalizable Variables obj hom comp.

Definition homOp `{Category} := hom.
Definition compOp `{Category obj hom comp} := comp.

Notation "a --> b" := (homOp a b).
Notation "1" := (cid _).
Notation "f '•' g" := (compOp _ _ _ f g) (at level 50).

(*** Dualization *)
Instance Dual `(Category obj hom comp) : Category obj (fun A B => B --> A)
  (fun {A B C} f g => comp _ _ _ g f):= {}.
Proof.
  - intros. apply 1.
  - intros A B f. simpl. apply idRight.
  - intros A B f. apply idLeft.
  - intros A B C D f g h. simpl. rewrite compAssoc. reflexivity.
Defined.

(* If we don't remove this typclass instance search might not terminate *)
Remove Hints Dual : typeclass_instances.

Notation "C ¯" := (Dual C) (at level 20, left associativity).

(** EXAMPLES **)

Instance Category_Set : Category Type (fun A B => A -> B)
  (fun A B C f g => compose f g) := {}.
  - intros. apply X.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. unfold compose. reflexivity.
Defined.

Class Poset {A : Type} (R : relation A) := {
  Poset_Reflexive :> Reflexive R;
  Poset_Transitive :> Transitive R;
  Poset_Antisymmetric :> Antisymmetric A eq R;
}.

Instance Category_Poset (A : Type) (lt : relation A) (P : Poset lt) : Category A 
  (fun (a1 a2 : A) => lt a1 a2)
  (fun (a1 a2 a3 : A) p1 p2 => @transitivity A lt (Poset_Transitive) a1 a2 a3 p2 p1)
  := {}.
  - apply reflexivity.
  - intros; apply proof_irrelevance.
  - intros; apply proof_irrelevance.
  - intros; apply proof_irrelevance.
Defined.
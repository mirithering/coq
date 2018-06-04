Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Init.Specif.


(*Require Import Category.*)

(* In order to avoid intersecting classes but still have notations,
  I am splitting the group class *)

(*Class GroupOps (A : Type) := {
  unit : A;
  mult : A -> A -> A;
  inv : A -> A;
}.*)

Generalizable Variables a b c.

Class Group (A : Type) (gunit : A) (ginv : A -> A) (gmult : A -> A -> A) := {
    multAssoc: forall a b c : A, gmult a (gmult b c) = gmult (gmult a b) c;
    unitLeft: forall a : A, gmult gunit a = a;
    unitRight: forall a : A, gmult a gunit = a;
    invLeft: forall a : A, gmult (ginv a) a = gunit;
    invRight: forall a : A, gmult a (ginv a) = gunit;
}.

Definition unitOp {A gunit ginv gmult} {G : Group A gunit ginv gmult} := gunit.
Definition multOp {A gunit ginv gmult} {G : Group A gunit ginv gmult} := gmult.
Definition invOp {A gunit ginv gmult} {G : Group A gunit ginv gmult} := ginv.

Infix "*" := multOp : group_scope.
Notation "! a" := (invOp a) (right associativity, at level 30) : group_scope.
Notation "1" := (unitOp) (at level 10): group_scope.

Local Open Scope group_scope.

Definition isInverse {A} `{Group A} (a b : A) := (a * b = 1 /\ b * a = 1).

Definition isUnit `{Group} u := forall a, (u * a = a /\ a * u = a).

Corollary inverseUnique `{Group}: `(unique (isInverse a) (! a)).
Proof.
  unfold unique. intros a. unfold isInverse. split.
  - split.
    + apply invRight.
    + apply invLeft.
  - intros b I. destruct I as [I1 I2]. replace (! a) with (! a * 1).
    + rewrite <- I1. rewrite multAssoc. rewrite invLeft. apply unitLeft.
    + apply unitRight.
Qed.

Corollary unitUnique `{Group} : unique isUnit 1.
Proof.
  unfold isUnit; split.
  - intro a. split; [apply unitLeft | apply unitRight].
  - intros b U. edestruct U as [U1 U2]. rewrite <- U1. apply unitRight.
Qed.

Corollary inverseMult `{Group} : `(!(a * b) = !b * !a).
Proof.
  intros a b. apply inverseUnique. unfold isInverse. split.
  - replace (a * b * ((! b) * (! a))) with (a * (b * !b) * (!a)).
    + rewrite invRight. rewrite (unitRight a). apply invRight.
    + rewrite multAssoc. rewrite multAssoc. reflexivity.
  - replace (!b * !a * (a * b)) with (!b * (!a * a) * b).
    + rewrite invLeft. rewrite (unitRight (! b)). apply invLeft.
    + repeat (rewrite multAssoc). reflexivity.
Qed.

Corollary inverseInvolutive `{Group} : `(!!a = a).
Proof.
  intros a. apply inverseUnique. split.
  - apply invLeft.
  - apply invRight.
Qed.

Corollary unitInverse {A} `{Group A} : 1 = ! 1.
Proof.
  apply unitUnique. intro a. rewrite <- (inverseInvolutive a). split.
  - rewrite <- inverseMult. rewrite unitRight. reflexivity.
  - rewrite <- inverseMult. rewrite unitLeft. reflexivity.
Qed.

Class GroupMorphism {A B} `{Group A} `{Group B} (f : A -> B) := {
  groupMorphism_unit : f 1 = 1;
  groupMorphism_mult : `(f (a * b) = f a * f b);
  (* this one does follow from the others, but it's more convenient to have it here *)
  groupMorphism_inv : `(f (! a) = ! (f a));
}.

Definition groupIsomorphism {A B} `{Group A} `{Group B} (f : A -> B) :=
  (exists g : B -> A, GroupMorphism g /\ compose f g = id /\ compose g f = id).

Definition groupIsomorphic (A B : Type) `{G1 : Group A} `{G2 : Group B} :=
  exists f : A -> B, groupIsomorphism f.

(** GSets *)

Class GSet A X `{Group A} (gSet_action : A -> X -> X) := {
  gSet_composition : forall a b x, gSet_action a (gSet_action b x) = gSet_action (a * b) x;
  gSet_unit : forall x, gSet_action 1 x = x;
}.

Print GSet.

Arguments GSet (A X) {gunit ginv gmult} (H) (gSet_action).

Print GSet.

Definition gSetOp {A X} `{GSet A X} := gSet_action.

Notation "g '•' x" := (gSetOp g x) (at level 61, left associativity) : group_scope.

Class Equivariant {X Y} (F : X -> Y)
    {A action1 action2} `{G : Group A} (G1 : GSet A X G action1) 
  (G2 : GSet A Y G action2) := {
  equivariance : forall (a : A) x, F (a • x) = a • (F x);
}.

Print Equivariant.

(* G-Sets and equivariant functions form a category *)

Instance EquivariantCompose {A X Y Z opX opY opZ} `{HG : Group A} 
  {G1 : GSet A X HG opX} {G2 : GSet A Y HG opY} {G3 : GSet A Z HG opZ} 
    (f : Y -> Z) (g : X -> Y)
  (E1 : Equivariant f G2 G3) (E2 : Equivariant g G1 G2) : (Equivariant (compose f g) G1 G3).
Proof.
  constructor. intros a x. unfold compose. rewrite (equivariance a x).
  rewrite (equivariance a (g x)). reflexivity.
Defined.

Instance equivariantId `{G : GSet} : Equivariant (fun x => x) G G.
  constructor. intros a x. reflexivity.
Defined.

Instance simpleGSet' A `{HG : Group A} : GSet A A HG (fun a b => a * b).
Proof.
  constructor.
  - apply multAssoc.
  - apply unitLeft.
Defined.

Instance simpleGSet A `{HG : Group A} : GSet A A HG (fun a b => a * b * !a).
Proof.
  constructor.
  - intros a b c. rewrite inverseMult. repeat (rewrite multAssoc). reflexivity.
  - intros a. rewrite <- unitInverse. rewrite (unitRight (1 * a)). apply unitLeft.
Defined.

Instance trivialGroup : Group Coq.Init.Datatypes.unit tt (fun u => tt) (fun u u' => tt).
Proof with auto.
  constructor ; (try intros [])...
Defined.

Print GroupMorphism.

Lemma exercise13 A `{HG : Group A} (f : A -> A) (P : GroupMorphism f)
  (E : Equivariant f (simpleGSet A) (simpleGSet' A)): groupIsomorphic A Coq.Init.Datatypes.unit.
Proof.
  exists (fun _ => tt). exists (fun _ => 1). split; try split.
  - reflexivity.
  - intros. rewrite unitRight. reflexivity.
  - intros. apply unitInverse.
  - extensionality a. destruct a. reflexivity.
  - extensionality a. unfold compose.
    replace 1 with (f a * ! (f a)). 2: { apply invRight. }
    pose proof (@equivariance A A f A _ _ _ _ _ HG (simpleGSet A) (simpleGSet' A) E).
    unfold gSetOp in H.
    rewrite <- groupMorphism_inv.
    assert( forall a : A, f (a) = a * (f a)).
    { intros b. rewrite <- H. rewrite <- multAssoc. rewrite invRight. rewrite unitRight. reflexivity. }
    rewrite H0. rewrite <- multAssoc. rewrite <- groupMorphism_mult. rewrite invRight.
    replace (f gunit) with (f 1) by reflexivity. rewrite groupMorphism_unit.
    rewrite unitRight. reflexivity.
Qed.
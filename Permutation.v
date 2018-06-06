Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Specif.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Group.

Section Permutation.

Variable A : Set.

Axiom atDec : forall (a b : A), {a = b} + {a <> b}.

Class Permutation (f : A -> A) (g : A -> A):= {
  permInvRight : forall a : A, f (g a) = a;
  permInvLeft : forall a : A, g (f a) = a;
}.

Axiom permUnique : forall f g (H1 : Permutation f g) (H2 : Permutation f g), H1 = H2.

(*Corollary permutationsEqual : forall p1 p2, p1 = p2 -> (@f p1 = @f p2).
Proof.
  intros. destruct p1, p2. inversion H. subst; auto.
Qed.*)

Instance permInverse f g {P : Permutation f g} : Permutation g f.
Proof.
  constructor.
  - destruct P. auto.
  - destruct P. auto.
Defined.

Instance permCompose f1 g1 f2 g2 `{Permutation f1 g1} `{Permutation f2 g2} : 
    Permutation (compose f1 f2) (compose g2 g1).
Proof.
  constructor.
  - intros a. unfold compose. rewrite (permInvLeft (g1 a)). rewrite permInvRight. reflexivity.
  - intros a. unfold compose. rewrite (permInvRight (f2 a)). rewrite permInvLeft. reflexivity.
Defined.

(* Remove those two instances from inference to avoid loops in instance search *)
Remove Hints permInverse permCompose : typeclass_instances.

Corollary permInverseInvolutive f g (P : Permutation f g) : 
  @permInverse g f (permInverse f g) = P.
Proof.
  apply permUnique.
Qed.

Instance permId : Permutation id id.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
Defined.

(** Permutations form a Group *)

Inductive permType : Set := | C : forall f g, Permutation f g -> permType.

Definition getPermutation (p : permType) : A -> A.
  destruct p. apply f.
Defined.

Coercion getPermutation : permType >-> Funclass.

Lemma permTypeUnique : forall f1 g1 f2 g2 p1 p2, f1 = f2 
  -> g1 = g2 -> C f1 g1 p1 = C f2 g2 p2.
Proof.
  intros. subst. apply f_equal. apply permUnique.
Qed.

Definition permTypeId : permType := C id id permId.
Definition permTypeInv : permType -> permType.
  intros P. destruct P. apply (C g f). apply permInverse. apply p.
Defined.
Definition permTypeCompose : permType -> permType -> permType.
  intros [f1 g1 p1] [f2 g2 p2]. apply (C (compose f1 f2) (compose g2 g1)).
  apply permCompose; auto.
Defined.

Instance Sym : Group permType permTypeId permTypeInv permTypeCompose.
Proof.
  constructor; unfold permTypeCompose, permTypeId, permTypeInv.
  - intros [f1 g1 P1] [f2 g2 P2] [f3 g3 P3].
    apply permTypeUnique; reflexivity.
  - intros [f g P]. apply permTypeUnique; reflexivity.
  - intros [f g P]. apply permTypeUnique; reflexivity.
  - intros [f g P]. apply permTypeUnique; extensionality a; apply permInvLeft.
  - intros [f g P]. apply permTypeUnique; extensionality a; apply permInvRight.
Defined.

Local Open Scope group_scope.

(** Finite Permutations *)

Require Import List.


(* A finite permutation only changes finitely many variabels *)

Definition isFinite (p : A -> Prop) := exists l : list A, forall a, p a -> In a l.

Class FinPerm (f : A -> A) (g : A -> A) := {
  perm :> Permutation f g;
  finite : isFinite (fun a => f a <> a);
}.

Axiom finiteUnique : forall (p : A -> Prop) (H1 : isFinite p) (H2 : isFinite p),
  H1 = H2.

Lemma finPermUnique : forall f g (P1 : FinPerm f g) (P2 : FinPerm f g), P1 = P2.
Proof.
  intros f g [P1 F1] [P2 F2].
  assert (P1 = P2) by apply permUnique.
  subst. assert (F1 = F2) by apply finiteUnique.
  apply f_equal. apply H.
Qed.
(*
Lemma permIdIsFinite : isFinite (fun a => (permId a) <> a).
Proof with auto.
  exists nil. intros a []...
  (* exists nil. split.
  - intros []. reflexivity.
  - intros [].*)
Qed.

Instance finPermId : FinPerm := {
  perm := permId;
  finite := permIdIsFinite;
}.

Lemma permInverseFinite : forall (P : FinPerm), isFinite (λ a : A, (permInverse perm) a ≠ a).
Proof.
  intros [p [l P3]]. simpl in *.
  exists l. intros a I. apply P3. intros H. apply I. rewrite <- H at 1. apply permCompRight.
Qed.
  (* intros [[f g P1 P2] [l P3]]. simpl in *.
  exists l. intros a. rewrite <- P3. compute. split.
  - intros H1 H2. apply H1. rewrite <- H2 at 1. replace (g (f a)) with ((compose g f) a) by reflexivity.
    rewrite P2. reflexivity.
  - intros H1 H2. apply H1. rewrite <- H2 at 1. replace (f (g a)) with ((compose f g) a) by reflexivity.
    rewrite P1. reflexivity. *)

Instance finPermInverse (P : FinPerm) : FinPerm := {
  perm := permInverse (@perm P);
  finite := permInverseFinite P;
}.

Lemma permComposeFinite : forall (P1 P2 : FinPerm), 
  isFinite (λ a : A, (permCompose (@perm P1) (@perm P2)) a ≠ a).
Proof with (subst; auto).
  intros [p1 [l1 F1]] [p2 [l2 F2]]. simpl in *. exists (l1 ++ l2).
  intros a C. unfold compose in C.
  destruct (dec (p2 a) a).
  - rewrite e in C. apply F1 in C. apply in_or_app. left...
  - apply F2 in n. apply in_or_app. right...
Qed.

Instance finPermCompose (P1 P2 : FinPerm) : FinPerm := {
  perm := permCompose (@perm P1) (@perm P2);
  finite := permComposeFinite P1 P2;
}.

(* Finally, finite permutations form a group *)

Instance Perm: Group := {
  A := FinPerm;

  unit := finPermId;
  inv := finPermInverse;
  mult := finPermCompose;
}.
Proof.
  - intros [P1 F1] [P2 F2] [P3 F3]. apply proofIrrelevanceFinPerm. simpl. apply (@multAssoc (Sym) P1 P2 P3).
  - intros [P F]. apply proofIrrelevanceFinPerm. apply (@unitLeft  (Sym)).
  - intros [P F]. apply proofIrrelevanceFinPerm. apply (@unitRight (Sym)).
  - intros [P F]. apply proofIrrelevanceFinPerm. apply (@invLeft (Sym)).
  - intros [P F]. apply proofIrrelevanceFinPerm. apply (@invRight (Sym)).
Defined.

End Permutations.

Module permNotation.

(* TODO scope *)

Notation "g '•' x" := (@action (Perm _) _ g x) (at level 29, left associativity).

End permNotation.*)

End Permutation.
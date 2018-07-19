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

Lemma permInvRight_compose `{Permutation} : compose f g = id.
Proof.
  extensionality a. unfold compose. rewrite permInvRight. reflexivity.
Qed.

Lemma permInvLeft_compose `{Permutation} : compose g f = id.
Proof.
  extensionality a. unfold compose. rewrite permInvLeft. reflexivity.
Qed.

Lemma perm_double_single `{Permutation} : forall a, f (f a) = f a -> f a = a.
  intros. rewrite <- permInvLeft. rewrite <- H0.
  replace (g (f (f a))) with (f a). apply H0. symmetry.
  apply permInvLeft.
Qed.

Lemma perm_chain `{Permutation} : forall a a', a <> a' -> f a = a' -> f a' <> a'.
Proof.
  intros. intros C. apply H0. subst. symmetry. 
  apply perm_double_single. apply C.
Qed.

Lemma perm_inv_same_domain `{Permutation} : forall a, f a = a <-> g a = a.
Proof.
  intros. split.
  - intros. rewrite <- H0. rewrite permInvLeft. symmetry; auto.
  - intros. rewrite <- H0. rewrite permInvRight. symmetry; auto.
Qed.

Lemma perm_inv_same_domain' `{Permutation} : forall a, f a <> a <-> g a <> a.
Proof.
  intros. apply not_iff_compat. apply perm_inv_same_domain.
Qed.

Axiom permUnique : forall f g (H1 : Permutation f g) (H2 : Permutation f g), H1 = H2.

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

Definition permType := { p | Permutation (fst p) (snd p) }.

Definition getPermFunction (p : permType) : A -> A :=
  match p with
    |exist _ (f,g) _ => f
  end.

Coercion getPermFunction : permType >-> Funclass.

Instance Sym : Group permType
  (exist _ (id, id) permId)
  (fun x => match x with
      | exist _ (f, g) P => exist _ (g, f) (@permInverse f g P) 
    end)
  (fun x1 x2 => match x1, x2 with
      | exist _ (f1, g1) P1, exist _ (f2, g2) P2 =>
        exist _ ((compose f1 f2), (compose g2 g1)) 
        (@permCompose f1 g1 f2 g2 P1 P2)
    end).
  constructor.
  - intros [[f1 g1] P1] [[f2 g2] P2] [[f3 g3] P3].
    apply f_equal. apply permUnique.
  - intros [[f g] P]. apply f_equal. apply permUnique.
  - intros [[f g] P]. apply f_equal. apply permUnique.
  - intros [[f g] P]. assert (compose g f = id). extensionality a; apply permInvLeft.
    apply eq_sig_uncurried. simpl. econstructor. apply permUnique.
  - intros [[f g] P]. assert (compose f g = id). extensionality a; apply permInvRight.
    apply eq_sig_uncurried. simpl. econstructor. apply permUnique.
  
  Unshelve. rewrite H; auto. rewrite H; auto.
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

Lemma finPermUnique : forall f g {P1 : FinPerm f g} {P2 : FinPerm f g}, P1 = P2.
Proof.
  intros f g [P1 F1] [P2 F2].
  assert (P1 = P2) by apply permUnique.
  subst. assert (F1 = F2) by apply finiteUnique.
  apply f_equal. apply H.
Qed.

Lemma permIdIsFinite : isFinite (fun a => (id a) <> a).
Proof with auto.
  exists nil. intros a []...
Qed.

Instance finPermId : FinPerm id id := {
  perm := permId;
  finite := permIdIsFinite;
}.

Lemma permInverseFinite : forall f g {P : FinPerm f g}, isFinite (λ a : A, g a ≠ a).
Proof.
  intros f g [p [l P3]].
  exists l. intros a I. apply P3. intros H. apply I. rewrite <- H at 1. 
  apply permInvLeft.
Qed.

Instance finPermInverse f g {P : FinPerm f g} : FinPerm g f := {
  perm := permInverse f g;
  finite := permInverseFinite f g;
}.

Instance finPermCompose f1 g1 f2 g2 {P1 : FinPerm f1 g1} {P2 : FinPerm f2 g2} : 
  FinPerm (compose f1 f2) (compose g2 g1) := {
    perm := permCompose f1 g1 f2 g2;
}.
  destruct P1 as [p1 [l1 F1]], P2 as [p2 [l2 F2]]. exists (l1 ++ l2).
  intros a C. unfold compose in C.
  destruct (atDec (f2 a) a).
  - rewrite e in C. apply F1 in C. apply in_or_app. left; auto.
  - apply F2 in n. apply in_or_app. right. auto.
Defined.

(* Finally, finite permutations form a group *)

Definition finPermType := {p | FinPerm (fst p) (snd p)}.

Instance Perm : Group finPermType 
  (exist _ (id, id) finPermId)
  (fun x => match x with
      | exist _ (f, g) P => exist _ (g, f) (@finPermInverse f g P) 
    end)
  (fun x1 x2 => match x1, x2 with
      | exist _ (f1, g1) P1, exist _ (f2, g2) P2 =>
        exist _ ((compose f1 f2), (compose g2 g1)) 
        (@finPermCompose f1 g1 f2 g2 P1 P2)
    end) := {}.
Proof.
  - intros [[f1 g1] F1] [[f2 g2] F2] [[f3 g3] F3].
    apply f_equal. apply finPermUnique.
  - intros [[f g] F]. apply f_equal. apply finPermUnique.
  - intros [[f g] F]. apply f_equal. apply finPermUnique.
  - intros [[f g] F]. apply eq_sig_uncurried. simpl. econstructor. apply finPermUnique.
  - intros [[f g] F]. apply eq_sig_uncurried. simpl. econstructor. apply finPermUnique.
  Unshelve.
    + rewrite permInvLeft_compose. reflexivity.
    + rewrite permInvRight_compose. reflexivity.
Defined.

End Permutation.

Definition getFinPermFunction {At} (p : finPermType At) : At -> At :=
  match p with
    |exist _ (f,g) _ => f
  end.

Coercion getFinPermFunction : finPermType >-> Funclass.
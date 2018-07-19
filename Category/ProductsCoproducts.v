Require Import Utf8 Basics Setoid FunctionalExtensionality.

Import EqNotations.

Add LoadPath "Category".
Require Import Category SpecialMorphismsAndObjects.

Generalizable Variables obj hom objA homA objB homB objC homC.

Class Product `{Category obj hom} (A B C : obj) (prA : C --> A) (prB : C --> B) := {
  product_prop: forall (D : obj) (f : D --> A) (g : D --> B), 
    exists ! (h : D --> C), prA • h = f /\ prB • h = g
}.

Class Coproduct `{Category obj hom} (A B C : obj) (inA : A --> C) (inB : B --> C) := {
  coproduct_prop: forall (D : obj) (f : A --> D) (g : B --> D), 
    exists ! (h : C --> D), h • inA = f /\ h • inB = g
}.

Lemma product_dual_coproduct `{Cat : Category obj hom}:
  forall A B C f g, 
  @Product _ _ _ _ Cat A B C f g <-> @Coproduct _ _ _ _ (Dual Cat) A B C f g.
Proof.
  intros. split; intros P; destruct P; constructor; auto.
Qed.

(* TODO DO I NEED TO REMOVE THIS DUALITY FROM TYPECLASS INFERENCE? *)

Lemma product_unique_iso1 `{Category obj hom} : forall A B C1 C2 f1 f2 g1 g2,
  Product A B C1 f1 g1 -> Product A B C2 f2 g2 -> C1 == C2.
Proof.
  intros. 
  pose proof (product_prop C1 f1 g1). 
  pose proof (product_prop C2 f2 g2).
  pose proof (@product_prop _ _ _ _ _ _ _ C1 _ _ H0 C2 f2 g2).
  pose proof (@product_prop _ _ _ _ _ _ _ C1 _ _ H0 C1 f1 g1).
  destruct H2 as [i [Ui1 Ui2]], H4 as [j [Uj1 Uj2]]. 
  exists i. exists j.
  destruct H3 as [ic2 [Uc21 Uc22]], H5 as [ic1 [Uc11 Uc12]].
  assert (ic1 = (cid C1)) as E1. { apply Uc12. split; apply idRight. }
  assert (ic2 = (cid C2)) as E2. { apply Uc22. split; apply idRight. }
  clear Uc21. clear Uc11.
  subst. destruct Ui1, Uj1.
  split.
  - symmetry. unfold "1". apply Uc22. split.
    + rewrite compAssoc. rewrite H2. apply H4.
    + rewrite compAssoc. rewrite H3. apply H5.
  - symmetry. unfold "1". apply Uc12. split; rewrite compAssoc.
    + rewrite H4. apply H2.
    + rewrite H5. apply H3.
Qed.

Lemma product_unique_iso2 `{Category obj hom} : forall A B C1 C2 f1 g1,
  Product A B C1 f1 g1 -> C1 == C2 -> exists f2 g2, Product A B C2 f2 g2.
Proof.
  intros. destruct H1 as [i [j [L R]]]. exists (f1 • j), (g1 • j).
  constructor. intros.
  pose proof (product_prop D f g). destruct H1 as [h [[E1 E2] U2]].
  exists (i • h). split; try split.
  - replace ((f1 • j) • (i • h)) with ((f1 • (j • i) • h)).
    unfold "•" in *. rewrite R. unfold "1". rewrite idRight. apply E1.
    repeat (rewrite compAssoc); reflexivity.
  - replace ((g1 • j) • (i • h)) with ((g1 • (j • i) • h)).
    unfold "•" in *. rewrite R. unfold "1". rewrite idRight. apply E2.
    repeat (rewrite compAssoc); reflexivity.
  - intros h' [H'1 H'2]. assert (h = (j • h')).
    { apply U2. split; rewrite compAssoc; auto. }
    subst. rewrite compAssoc. unfold "•" in *. rewrite L. apply idLeft.
Qed.

Instance idProduct `{Category} A T (HT : isTerminal T) : Product A T A 1 (bang T HT A).
  constructor.
  intros. exists f. split; try split.
  - apply idLeft.
  - pose proof (bang_unique T HT D).
    assert (bang _ HT A • f = bang _ HT D). apply H0.
    rewrite H1. symmetry. apply bang_unique.
  - intros. destruct H0. rewrite <- H0. apply idLeft.
Defined.

Lemma product_commutative `{Category} A B C pr1 pr2 :
  Product A B C pr1 pr2 -> Product B A C pr2 pr1.
Proof.
  intros. constructor. intros.
  pose proof (product_prop D g f). destruct H1. exists x.
  destruct H1 as [[H2 H3] H1]. split.
  - split; auto.
  - intros x' [L R]. apply H1; split; auto.
Qed.

Lemma product_commutative_iso `{Category} A B C1 C2 prA1 prA2 prB1 prB2:
  Product A B C1 prA1 prB1 -> Product B A C2 prB2 prA2 -> C1 == C2.
Proof.
  intros. eapply product_unique_iso1.
  apply H0. apply product_commutative. apply H1.
Qed.

(** EXAMPLES **)

Open Scope type_scope.

Instance Product_Set (A B : Set) : Product A B (A * B) fst snd.
  constructor.
  intros. exists (fun d => ((f d), (g d))). split.
  - split.
    + extensionality d. reflexivity.
    + extensionality d. reflexivity.
  - intros. destruct H. rewrite <- H. rewrite <- H0. extensionality d.
    compute. destruct (x' d). reflexivity.
Defined.
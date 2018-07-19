Add LoadPath "Category".
Require Import Category Epsilon.

Generalizable Variables hom obj.

Definition epimorphism `{Category} {A B} (f : hom A B) :=
  forall C (g1 g2 : B --> C), g1 • f = g2 • f -> g1 = g2.

Definition monomorphism `{Category} {A B} (f : hom A B) :=
  forall C (g1 g2 : hom C A), f • g1 = f • g2 -> g1 = g2.

Definition isInverse `{Category} {A B} (f : hom A B) (f' : hom B A) := f • f' = 1 /\ f' • f = 1.

Definition isomorphism `{Category} {A B} (f : hom A B) :=
  exists (f' : hom B A), isInverse f f'.

Definition isomorphic `{Category} (A B : obj) := exists (f : hom A B), isomorphism f.

Hint Unfold epimorphism monomorphism isInverse isomorphism isomorphic.

Notation "A == B" := (isomorphic A B) (at level 70, right associativity).

Lemma isomorphic_symmertric `{Category} {A B}: A == B <-> B ==  A.
Proof.
  unfold "==". autounfold. split; intros [f [f' [L R]]]; exists f', f; split; auto.
Qed.

Lemma isoIsMono: forall `{Category} {A B} (f : hom A B), isomorphism f -> monomorphism f.
Proof.
  autounfold. intros. inversion H0 as [f' [L R]].
  replace g2 with (1 • g2) by apply idLeft.
  replace g1 with (1 • g1) by apply idLeft.
  rewrite <- R. rewrite <- compAssoc. rewrite H1. apply compAssoc.
Qed.

Lemma isoIsEpi: forall `{Category} {A B} (f :hom A B), isomorphism f -> epimorphism f.
Proof.
  autounfold. intros. inversion H0 as [f' [L R]].
  replace g2 with (g2 • 1) by apply idRight.
  replace g1 with (g1 • 1) by apply idRight.
  unfold "1" in *.
  rewrite <- L. rewrite compAssoc. rewrite H1. rewrite compAssoc. reflexivity.
Qed.

Lemma inverseUnique: forall `{Category} {A B} (f1 f2 : hom A B) (f : hom B A), 
  isInverse f1 f /\ isInverse f2 f -> f1 = f2.
Proof.
  intros obj hom cid comp Cat A B f1 f2 f Inv. 
  destruct Inv as [Inv1 Inv2]. destruct Inv1 as [Inv1L Inv1R].
  destruct Inv2 as [Inv2L Inv2R].
  replace f1 with (f1 • 1) by apply idRight. rewrite <- Inv2R. rewrite compAssoc.
  rewrite Inv1L. apply idLeft.
Qed.

Lemma isomorphism_dual : forall `(C : Category obj hom) {A B} (f : hom A B), 
  @isomorphism _ _ _ _ C _ _ f <->
  @isomorphism _ _ _ _ (Dual C) _ _ f.
Proof.
  intros. autounfold. unfold "1". unfold "•". unfold "-->". 
  split; intros [f' [L R]]; exists f'; split; auto.
Qed.

Lemma isomorphic_dual : forall `(C : Category) {A B},
  @isomorphic _ _ _ _ C A B <-> @isomorphic _ _ _ _ (Dual C) A B.
Proof.
  autounfold. intros.
  split; intros [f [f' [L R]]]; exists f', f; auto. 
Qed.

Lemma monomorphism_compose : forall `{Category obj hom} 
  {A B C} (f : hom B C) (g : hom A B), 
  monomorphism f -> monomorphism g -> monomorphism (f • g).
Proof.
  autounfold. intros. apply H1. apply H0. repeat (rewrite compAssoc).
  apply H2.
Qed.

Lemma monomorphism_decompose : forall `{Category obj hom}
  {A B C} (f : hom B C) (g : hom A B),
  monomorphism (f • g) -> monomorphism g.
Proof.
  autounfold. intros. apply H0. repeat (rewrite <- compAssoc).
  rewrite H1. reflexivity.
Qed.

Lemma epimorphism_compose : forall `{Category obj hom} 
  {A B C} (f : hom B C) (g : hom A B), 
  epimorphism f -> epimorphism g -> epimorphism (f • g).
Proof.
  intros. apply (@monomorphism_compose _ _ _ _ (Dual H)); auto.
Qed.

Lemma epimorphism_decompose : forall `{Category obj hom}
  {A B C} (f : hom B C) (g : hom A B),
  epimorphism (f • g) -> epimorphism f.
Proof.
  intros. eapply (@monomorphism_decompose _ _ _ _ (Dual H)).
  apply H0.
Qed.

(*** Initial and Terminal objects *)

Definition isTerminal `{C : Category} (T : obj) := forall A, exists ! f : hom A T, True.

Definition bang `{Category obj} (T : obj) (TH : isTerminal T) (A : obj) : A --> T.
  unfold isTerminal in TH. specialize TH with A.
  apply constructive_indefinite_description in TH. destruct TH. apply x.
Defined.

Notation "! H A" := (bang _ H A) (at level 30).

Lemma bang_unique `{Category obj} (T : obj) (TH : isTerminal T) :
  forall A (h : A --> T), h = (bang _ TH A).
Proof.
  intros. destruct (TH A). destruct H0. assert (x = h).
  apply H1. constructor. subst. apply H1. constructor.
Qed.

Hint Unfold isTerminal.

Lemma terminalUniqueIso1 `{C : Category} : 
  forall B1 B2, isTerminal B1 /\ isTerminal B2 -> B1 == B2.
Proof.
  autounfold. intros B1 B2 [TermB1 TermB2].
  pose proof TermB1 as TermB1Copy.
  pose proof TermB2 as TermB2Copy.
  destruct TermB1 with B1 as [id1 Uid1]. clear TermB1.
  destruct TermB2 with B2 as [id2 Uid2]. clear TermB2.
  destruct TermB1Copy with B2 as [f1 Uf1]. clear TermB1Copy.
  destruct TermB2Copy with B1 as [f2 Uf2]. clear TermB2Copy.
  exists f2. exists f1. split.
  - inversion Uid2. rewrite <- H0 with (f2 • f1) by constructor. rewrite (H0 1) by 
    constructor. reflexivity.
  - inversion Uid1. rewrite <- H0 with (f1 • f2) by constructor. rewrite (H0 1) by 
    constructor. reflexivity.
Qed.

Lemma terminalUniqueIso2 `{C : Category}: 
  forall B1 B2, isTerminal B1 /\ B1 == B2 -> isTerminal B2.
Proof.
  autounfold. intros B1 B2 Con. 
  destruct Con as [T [f [f' Inv]]].
  intros A. assert (exists ! g : hom A B1, True) by apply T.
  destruct H. exists (f • x). split.
  - apply I.
  - intros g' Top. replace g' with (1 • g') by apply idLeft.
    inversion Inv as [L R]. rewrite <- L. rewrite <- compAssoc. 
    replace (f' • g') with x; try reflexivity.
    + apply H. constructor.
Qed.

Definition isInitial `{C : Category} (I : obj) := forall A, exists ! f : hom I A, True.

Hint Unfold isInitial.

Corollary initialDualTerminal {obj hom cid comp} `(C : Category obj hom cid comp): 
  forall o, @isTerminal _ _ _ _ C o <-> @isInitial _ _ _ _ (Dual C) o.
Proof.
  autounfold. intros. split; [intros hI A | intros hT A].
  - destruct hI with A as [f [[] H]]. 
    exists f. split; try apply I. intros g []. rewrite <- H; auto.
  - destruct hT with A as [f [[] H]]. 
    exists f. split; try apply I. intros g []. rewrite <- H; auto.
Qed.

Lemma initialUniqueIso1 `{C : Category} : forall B1 B2, isInitial B1 /\ isInitial B2 
  -> B1 == B2.
Proof.
  intros.
  rewrite isomorphic_dual. apply terminalUniqueIso1.
  destruct H. split; auto.
Qed.

Lemma initialUniqueIso2 `{C : Category}: forall B1 B2, 
  isInitial B1 /\ B1 == B2 -> isInitial B2.
Proof.
  intros B1 B2 [I E].
  rewrite <- (initialDualTerminal (Dual C) B2). eapply terminalUniqueIso2.
  split.
  - apply I.
  - rewrite isomorphic_symmertric. rewrite isomorphic_dual.
    rewrite isomorphic_symmertric. apply E.
Qed.
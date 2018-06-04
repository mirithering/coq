Require Import Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.
Require Import Coq.Init.Specif.
From mathcomp.ssreflect Require Import ssreflect ssrbool.

Section Swap.

Variable At : Set.

(* Equality on atoms is decidable *)

Axiom atDec : forall a1 a2 : At, {a1 = a2} + {a1 <> a2}.

(*Axiom atEq : At -> At -> bool.

Axiom atBoolTrue : forall a1 a2, atEq a1 a2 = true <-> a1 = a2.
Axiom atBoolFalse : forall a1 a2, atEq a1 a2 = false <-> a1 <> a2.

Lemma atEqRefl : forall a, atEq a a = true.
Proof.
  intros. rewrite atBoolTrue. reflexivity.
Qed.*)

Lemma atDecRefl : forall a, exists H, atDec a a = left H.
  intros. destruct (atDec a a). exists e. reflexivity.
  contradiction.
Qed.

Ltac rewriteAtRefl a := let H := fresh in let E := fresh in pose proof (atDecRefl a); destruct H as [E H];
  rewrite H; clear H; clear E.

(* With decidable equality, we can define a swap operation *)

(* Definition swap a1 a2 a : At :=
  if atEq a a1 then a2 else if atEq a a2 then a1 else a.*)

Definition swap a1 a2 a : At :=
  if atDec a a1 then a2 else if atDec a a2 then a1 else a.

(* TODO this should be automatizable once I am smarter *)

Lemma swapCasesFirst: forall a1 a2 a, (a = a1) -> (swap a1 a2) a = a2.
Proof.
  intros a1 a2 a H. compute; subst. rewriteAtRefl a1. reflexivity.
Qed.

Lemma swapCasesSecond: forall a1 a2 a, (a = a2) -> (swap a1 a2) a = a1.
Proof with (subst; auto).
  intros a1 a2 a H. compute... rewriteAtRefl a2. destruct (atDec a2 a1)...
Qed.

Lemma swapCasesNone: forall a1 a2 a, (a <> a1) -> (a <> a2) -> (swap a1 a2) a = a.
Proof with (try contradiction; auto).
  intros a1 a2 a I1 I2. compute. destruct (atDec a a1)... destruct (atDec a a2)...
Qed.

Lemma swapId : forall a, swap a a = @id At.
Proof with (subst;auto).
  intros. extensionality a'. destruct (atDec a a'). rewrite swapCasesFirst...
  rewrite swapCasesNone...
Qed.

Lemma swapId' : forall a a1, (swap a a) a1 = a1.
Proof.
  intros. replace a1 with (id a1) by reflexivity. rewrite swapId. reflexivity.
Qed.

Lemma swapInvolutive : forall a1 a2, compose (swap a1 a2) (swap a1 a2) = @id At.
Proof with (subst; auto).
  intros a1 a2. extensionality a; unfold compose.
  destruct (atDec a a1) as [e1 | i1]; destruct (atDec a a2) as [e2 | i2].
  - rewrite swapCasesFirst... rewrite swapCasesFirst...
  - rewrite swapCasesSecond... rewrite swapCasesFirst...
  - rewrite swapCasesFirst... rewrite swapCasesSecond...
  - rewrite swapCasesNone. rewrite swapCasesNone...
    + rewrite swapCasesNone...
    + rewrite swapCasesNone...
Qed.

Lemma swapInvolutive' : forall a1 a2 a, (swap a1 a2) ((swap a1 a2) a) = a.
Proof.
  intros. pose proof (swapInvolutive a1 a2). replace a with (id a) at 2 by reflexivity.
  rewrite <- H. reflexivity.
Qed.

Lemma swapComm : forall a1 a2, swap a1 a2 = swap a2 a1.
Proof with (subst; auto).
  intros. extensionality a. destruct (atDec a a1) as [e1 | i1], (atDec a a2) as [e2 | i2]...
  - rewrite swapCasesFirst... rewrite swapCasesSecond...
  - rewrite swapCasesSecond... rewrite swapCasesFirst...
  - rewrite swapCasesNone... rewrite swapCasesNone...
Qed.

Instance swapPerm (a1 a2 : At) : Permutation At := {
  f := swap a1 a2;
  g := swap a1 a2;
}.
Proof.
  - apply swapInvolutive.
  - apply swapInvolutive.
Defined.

Local Open Scope list_scope.

Instance swapFinPerm (a1 a2 : At) : FinPerm At := {
  perm := swapPerm a1 a2;
}.
Proof with (subst; auto).
  destruct (atDec a1 a2).
  - exists nil. intros a. intros H...
    exfalso. apply H. simpl. rewrite swapId...
  - exists (a1 :: a2 :: nil). intros.
    destruct (atDec a a1) as [e1 | i1]...
     + left...
     + right. destruct (atDec a a2) as [e2 | i2]...
        { left... }
        { right. exfalso. apply H. simpl. rewrite swapCasesNone... }
Defined.

(* Every finite permutation can be constructed from a sequence of swaps *)

Fixpoint swapList (l : list (At * At)) (a : At) : At :=
  match l with
    | nil => a
    | (a1, a2) :: l' => swapList l' (swap a1 a2 a)
  end.

Import ListNotations.

Corollary swapListComp : forall a1 a2 l1 l2 a, swapList l2 (swapList (l1 ++ [(a1, a2)]) a) =
  swapList ((a1, a2) :: l2) (swapList l1 a).
Proof. induction l1.
  - simpl. reflexivity.
  - intros. destruct a. simpl. rewrite IHl1. reflexivity.
Qed.

Corollary swapListApp : forall l1 l2 a, swapList (l1 ++ l2) a = swapList l2 ((swapList l1) a).
Proof.
  induction l1.
  - reflexivity.
  - intros. destruct a as [a1 a2]. simpl. rewrite IHl1. reflexivity.
Qed.

Instance swapListPerm (l : list (At * At)) : Permutation At := {
  f := swapList l;
  g := swapList (rev l);
}.
Proof.
  - extensionality a. unfold compose. generalize dependent a. induction l.
    + reflexivity.
    + intros a0. destruct a as [a1 a2]. simpl.
      replace (swapList l (swap a1 a2 (swapList (rev l ++ [(a1, a2)]) a0))) with
        (swapList ((a1, a2) :: l) (swapList (rev l ++ [(a1, a2)]) a0)) by reflexivity.
      rewrite swapListComp. simpl. rewrite swapInvolutive'. apply IHl.
  - extensionality a. unfold compose. generalize dependent a. induction l.
    + reflexivity.
    + intros. destruct a as [a1 a2]. simpl. 
      rewrite swapListApp. simpl. rewrite IHl. unfold id. apply swapInvolutive'.
Defined.

Instance swapListFinPerm (l : list (At * At)) : FinPerm At := {
  perm := swapListPerm l;
}.
Proof with (subst; auto).
  exists (fold_right (fun a l => match a with (a1, a2) => (a1 :: a2 :: l) end) [] l). 
  intros a Ineq. generalize dependent a. induction l; intros.
  - simpl in Ineq. contradiction.
  - destruct a as [a1 a2]. simpl in *. destruct (atDec a1 a0), (atDec a2 a0)...
    right; right. apply IHl. rewrite swapCasesNone in Ineq...
Defined.

Require Import Coq.omega.Omega.

Definition lengthOrder := (fun (l1 l2 : list At) => length l1 < length l2).

Lemma wellFoundedLeq: well_founded lengthOrder.
Proof with (subst; auto).
  unfold lengthOrder. intros l1. constructor. induction (length l1).
  - intros l2 L. inversion L.
  - intros l2 L. induction l2.
    + constructor. intros l3 L2. inversion L2.
    + constructor. intros l3 L3. apply IHn. omega.
Qed.

Check @well_founded_ind.

Check permCompose.

Lemma permutationToSwaps : forall (p : FinPerm At), exists (l : list (At * At)), 
  (@perm At p) = swapListPerm l
   /\ (forall a a', In (a, a') l -> (a <> a' /\ p a <> a /\ p a' <> a' /\ p a <> p a'))
   /\ (NoDup (fold_right (fun p l2 => match p with (a1, a2) =>  a1 :: a2 :: l2 end) [] l)).
Proof with (subst; auto).
  intros [p [l I]]. generalize dependent p. generalize dependent l. 
  apply (@well_founded_ind (list At) lengthOrder wellFoundedLeq
    ((fun l => forall (p : Permutation At) (I : ∀ a : At, p a ≠ a -> In a l),
∃ l0 : list (At * At), (perm (A:=At)) = swapListPerm l0 /\ 
  (forall a a', In (a, a') l0 -> (a <> a' /\ p a <> a /\ p a' <> a' /\ p a <> p a') ) 
     /\ (NoDup (fold_right (fun p l2 => match p with (a1, a2) =>  a1 :: a2 :: l2 end) [] l0))))).
  - intros l1 H p I. destruct l1.
    + exists nil. split; try split...
      * apply proofIrrelevancePerm. 
        extensionality a. simpl. destruct (atDec (p a) a); auto. apply I in n. inversion n.
      * constructor.
    + remember (permCompose p (swapPerm a ((permInverse p) a))) as p' eqn:P'.
      destruct p as [p pi comp1 comp2].
      assert (p' a = a).
      { subst. simpl. unfold compose. rewrite swapCasesFirst... pose proof comp1.
      replace (p (pi a)) with ((compose p pi) a ) by reflexivity. rewrite H0... }
      assert (forall a', a' <> a -> p a' = a' -> p' a' = a').
      { intros a' IA PA. rewrite P'. simpl in *. destruct (atDec (pi a) a').
        { subst. unfold compose. exfalso. apply IA. rewrite <- PA. replace (p (pi a)) with ((compose p pi) a)...
          rewrite comp1... }
        { unfold compose. rewrite swapCasesNone... }
      }
    assert (lengthOrder l1 (a :: l1)). { unfold lengthOrder. constructor. }
    assert(∀ a0 : At, p' a0 ≠ a0 -> In a0 l1). 
    { intros a' H3.
      assert (a <> a'). { intros C... }
      assert (p a' <> a'). { intros P... }
      apply I in H5. destruct H5; try contradiction...
    }
    pose proof (H l1 H2 p' H3). destruct H4 as [t H4],H4 as [S Eq].
    destruct (atDec a (pi a)).
    * exists t. split ; (try split).
      { apply proofIrrelevancePerm. simpl. extensionality b. 
        apply permutationsEqual in S. simpl in S.
        rewrite <- S. compute. rewrite P'. simpl.
        rewrite <- e. rewrite swapId. compute. reflexivity. }
      { intros a1 a2 IN. apply Eq in IN. destruct IN as [I1 [I2 I3]]. split...
        simpl in *. rewrite <- e in I3, I2. rewrite swapId in I3, I2. compute in I3, I2. split... }
      { destruct Eq as [Eq1 Eq2]. apply Eq2... }
    * exists (((a, (pi a)) :: t)). split; try split.
      { apply proofIrrelevancePerm. simpl. extensionality b.
        apply permutationsEqual in S. simpl in S.
        rewrite <- S. simpl. rewrite P'. simpl.
        replace (compose p (swap a (pi a)) (swap a (pi a) b)) 
          with (compose p (compose (swap a (pi a)) (swap a (pi a))) b) by reflexivity.
        rewrite swapInvolutive. reflexivity. }
      { intros a1 a2 IN. destruct IN.
        { inversion H4. subst. split... split; try split.
          { simpl in *. intros K. apply n. rewrite <- K at 2.
            replace (pi (p a1)) with ((compose pi p) a1) by reflexivity. rewrite comp2. reflexivity. }
          { intros C. apply n. rewrite <- C. simpl.
            replace (p (pi a1)) with ((compose p pi) a1) by reflexivity. rewrite comp1... }
          { simpl in *. replace (p (pi a1)) with ((compose p pi) a1) by reflexivity.
            rewrite comp1. unfold id. intros C. apply n.
            replace a1 with (id a1) at 1 by reflexivity. rewrite <- comp2. unfold compose. rewrite C...  }
        }
        { apply Eq in H4. destruct H4 as [A1 [A2 [A4 A5]]]. split... simpl in *. 
          destruct (atDec a a1)... destruct (atDec a a2)...
          split... split...
          destruct (atDec (pi a) a1), (atDec (pi a) a2)...
          { intros C. apply n2. replace a2 with (id a2) by reflexivity. rewrite <- comp2.
            unfold compose. rewrite <- C. replace (p (pi a)) with (compose p pi a) by reflexivity.
            rewrite comp1. reflexivity. }
          { replace (p (pi a)) with (compose p pi a) by reflexivity. rewrite comp1. unfold id. intros C.
            apply n2. rewrite <- C. replace (pi (p a1)) with (compose pi p a1) by reflexivity.
            rewrite comp2... }
          { unfold compose in A4, A2, A5. rewrite swapCasesNone in A4, A2, A5...
            rewrite swapCasesNone in A5... }
        }
      }
      { simpl. destruct Eq as [Eq1 Eq2]. rewrite NoDup_cons_iff. split.
          intros In. destruct In...
          assert (exists a', In (a, a') t). admit. (* wlog *)
          inversion H5. apply Eq1 in H6. 
          simpl in *. destruct H6, H7. apply H7.
          unfold compose. rewrite swapCasesFirst... 
 replace (p (pi a)) with (compose p pi a) by reflexivity.
          rewrite comp1...
          constructor.
          intros H4.
          assert (exists a' : At, In (a, a') t). admit. (* wlog *)
          inversion H5. apply Eq1 in H6. 
          rewrite P' in *. simpl in *. destruct H6, H7. apply H7.
          unfold compose. rewrite swapCasesFirst... 
 replace (p (pi a)) with (compose p pi a) by reflexivity.
          rewrite comp1...
          apply Eq2.
          apply NoDup_cons_iff. split.
          intros C. destruct C...
          Focus 2.
          apply Eq in C. destruct C as [C1 [C2 [C3 C4]]]. subst. simpl in *.
          apply C2. unfold compose. rewrite swapCasesFirst...
          replace (p (pi a)) with (compose p pi a) by reflexivity.
          rewrite comp1...
        }
        { destruct Eq... }
      }
Admitted.

Lemma permutationToFinSwaps : forall (p : FinPerm At), exists (l : list (At * At)),
  p = swapListFinPerm l
   /\ (forall a a', In (a, a') l -> (a <> a' /\ p a <> a /\ p a' <> a' /\ p a <> p a') /\ (NoDup l)).
Proof. intros. pose proof (permutationToSwaps p). destruct H as [l H]. exists l. split; try split.
  - apply proofIrrelevanceFinPerm. destruct H. auto.
  - destruct H, H1. auto.
  - destruct H, H1. auto.
Qed.

End Swap.
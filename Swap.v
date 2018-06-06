Require Import Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.
Require Import Coq.Init.Specif.

Section Swap.

Variable At : Set.

(* Equality on atoms is decidable *)

Axiom eqAtDec : forall a1 a2 : At, {a1 = a2} + {a1 <> a2}.

Lemma atDecRefl : forall a, exists H, eqAtDec a a = left H.
  intros. destruct (eqAtDec a a). exists e. reflexivity.
  contradiction.
Qed.

Ltac rewriteAtRefl a := let H := fresh in let E := fresh in pose proof (atDecRefl a); destruct H as [E H];
  rewrite H; clear H; clear E.

Definition swap (a1 a2 a : At) : At :=
  if eqAtDec a a1 then a2 else if eqAtDec a a2 then a1 else a.

(* TODO this should be automatizable once I am smarter *)

Lemma swapCasesFirst: forall a1 a2 a, (a = a1) -> (swap a1 a2) a = a2.
Proof.
  intros a1 a2 a H. compute; subst. rewriteAtRefl a1. reflexivity.
Qed.

Lemma swapCasesSecond: forall a1 a2 a, (a = a2) -> (swap a1 a2) a = a1.
Proof with (subst; auto).
  intros a1 a2 a H. compute... rewriteAtRefl a2. destruct (eqAtDec a2 a1)...
Qed.

Lemma swapCasesNone: forall a1 a2 a, (a <> a1) -> (a <> a2) -> (swap a1 a2) a = a.
Proof with (try contradiction; auto).
  intros a1 a2 a I1 I2. compute. destruct (eqAtDec a a1)... destruct (eqAtDec a a2)...
Qed.

Lemma swapId : forall a, swap a a = @id At.
Proof with (subst;auto).
  intros. extensionality a'. destruct (eqAtDec a a'). rewrite swapCasesFirst...
  rewrite swapCasesNone...
Qed.

Lemma swapId' : forall a a1, (swap a a) a1 = a1.
Proof.
  intros. replace a1 with (id a1) by reflexivity. rewrite swapId. reflexivity.
Qed.

Local Hint Rewrite swapCasesFirst swapCasesSecond swapCasesNone.

(* Solves if the goal requires one case analysis *)

Ltac swapCases := 
  auto;
  try (rewrite swapCasesFirst; [ swapCases | solve [swapCases]]); 
  try (rewrite swapCasesSecond; [ swapCases | solve [swapCases]]); 
  try (rewrite swapCasesNone; [ swapCases | solve [swapCases] | solve [swapCases]]).

Lemma swapSelfInverse : forall a1 a2, compose (swap a1 a2) (swap a1 a2) = @id At.
Proof with (subst; auto).
  intros a1 a2. extensionality a; unfold compose.
  destruct (eqAtDec a a1) as [e1 | i1]; subst; swapCases.
  destruct (eqAtDec a a2) as [e2 | i2]; subst; swapCases.
Qed.

Lemma swapSelfInverse' : forall a1 a2 a, (swap a1 a2) ((swap a1 a2) a) = a.
Proof.
  intros a1 a2 a. 
  replace a with (id a) at 2 by reflexivity.
  erewrite <- swapSelfInverse. reflexivity.
Qed.

Lemma swapComm : forall a1 a2, swap a1 a2 = swap a2 a1.
Proof with (subst; auto).
  intros. extensionality a. destruct (eqAtDec a a1) as [e1 | i1], 
    (eqAtDec a a2) as [e2 | i2]; subst; swapCases.
Qed.

Instance swapPerm (a1 a2 : At) : 
  Permutation At (swap a1 a2) (swap a1 a2) := {}.
Proof.
  - apply swapSelfInverse'.
  - apply swapSelfInverse'.
Defined.

Local Open Scope list_scope.
Import ListNotations.

Instance swapFinPerm (a1 a2 : At) : 
  FinPerm At (swap a1 a2) (swap a1 a2) := {
  perm := swapPerm a1 a2;
}.
Proof with (subst; auto).
  destruct (eqAtDec a1 a2).
  - exists nil. intros a. intros H...
    exfalso. apply H. simpl. rewrite swapId...
  - exists (a1 :: a2 :: nil). intros.
    destruct (eqAtDec a a1) as [e1 | i1]...
     + left...
     + right. destruct (eqAtDec a a2) as [e2 | i2]...
        { left... }
        { right. exfalso. apply H. simpl. rewrite swapCasesNone... }
Defined.

(* Every finite permutation can be constructed by a sequence of swaps *)

Fixpoint swapList (l : list (At * At)) (a : At) : At :=
  match l with
    | [] => a
    | (a1, a2) :: l' => swapList l' (swap a1 a2 a)
  end.

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

Instance swapListPerm (l : list (At * At)) : Permutation At (swapList l) (swapList (rev l)):= {}.
Proof.
  - induction l.
    + reflexivity.
    + intros a0. destruct a as [a1 a2].
      replace (rev ((a1, a2) :: l)) with ((rev l) ++ [(a1, a2)]) by reflexivity.
      rewrite swapListComp. simpl. rewrite swapSelfInverse'. apply IHl.
  - induction l.
    + reflexivity.
    + intros. destruct a as [a1 a2]. simpl. 
      rewrite swapListApp. simpl. rewrite IHl. apply swapSelfInverse'.
Defined.

Instance swapListFinPerm (l : list (At * At)) : FinPerm At (swapList l) (swapList (rev l)):= {
  perm := swapListPerm l;
}.
Proof with (subst; auto).
  exists (fold_right (fun a l => match a with (a1, a2) => (a1 :: a2 :: l) end) [] l). 
  intros a Ineq. generalize dependent a. induction l; intros.
  - simpl in Ineq. contradiction.
  - destruct a as [a1 a2]. simpl in *. destruct (eqAtDec a1 a0), (eqAtDec a2 a0)...
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

Lemma permutationToSwaps : forall f g `(FinPerm At f g), exists (l : list (At * At)), 
  f = swapList l
   /\ (forall a a', In (a, a') l -> (a <> a' /\ f a <> a /\ f a' <> a' /\ f a <> f a'))
   /\ (NoDup (fold_right (fun p l2 => match p with (a1, a2) =>  a1 :: a2 :: l2 end) [] l)).
Proof with (subst; auto).
  intros f g [P [l I]]. generalize dependent g. generalize dependent f. generalize dependent l.

  apply (@well_founded_ind (list At) lengthOrder wellFoundedLeq
    (fun l => 
      ∀ (f : At → At),(∀ a : At, f a ≠ a → In a l) → ∀ g : At → At, Permutation At f g
        → ∃ l0 : list (At * At), 
          f = swapList l0
           ∧ (∀ a a' : At, In (a, a') l0  → a ≠ a' ∧ f a ≠ a ∧  f a' ≠ a' ∧ f a ≠ f a')
           ∧ NoDup (fold_right (λ (p : At * At) (l2 :  list At), let (a1, a2) := p in a1 :: a2 :: l2) [] l0))).

  - intros l H f I g P. destruct l.
    + exists nil. split; try split...
      * extensionality a. destruct (eqAtDec (f a) a); auto. apply I in n. inversion n.
      * constructor.
    + remember (compose f (swap a (g a))) as f' eqn:F'.

      assert (f' a = a). { 
        subst. unfold compose. swapCases. rewrite swapCasesFirst... pose proof comp1.
      replace (p (pi a)) with ((compose p pi) a ) by reflexivity. rewrite H0... }
      assert (forall a', a' <> a -> p a' = a' -> p' a' = a').
      { intros a' IA PA. rewrite P'. simpl in *. destruct (atDec (pi a) a').
        { subst. unfold compose. exfalso. apply IA. rewrite <- PA. replace (p (pi a)) with ((compose p pi) a)...
          rewrite comp1... }
        { unfold compose. rewrite swapCasesNone... }
      }

      specialize H with l f' (compose (swap a (g a)) g).
      assert (lengthOrder l (a :: l)). { unfold lengthOrder. constructor. }
      apply H in H0; clear H.

      2 : { rewrite F'. unfold compose. intros a' H3.
      specialize I with a'. simpl in I.
      assert (a <> a'). { intros C. apply H3. rewrite C. swapCases. apply permInvRight... }
      
      assert (f a' <> a'). { intros C. subst. apply H. }
      apply I in H5. destruct H5; try contradiction...
    }
     
   
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
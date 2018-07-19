Require Import Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Utf8 Omega.
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
    | (a1, a2) :: l' => swap a1 a2 (swapList l' a)
  end.

Corollary swapList_cons: 
  forall a1 a2 l1 l2 a, swapList l2 (swapList ((a1, a2) :: l1) a) =
    swapList (l2 ++ [(a1, a2)]) (swapList l1 a).
Proof. induction l2.
  - simpl. reflexivity.
  - intros. destruct a. simpl. rewrite <- IHl2. reflexivity.
Qed.

Corollary swapList_app: forall l1 l2 a, swapList (l1 ++ l2) a = 
  swapList l1 ((swapList l2) a).
Proof.
  induction l1.
  - simpl. reflexivity.
  - intros. destruct a as [a1 a2]. simpl. rewrite IHl1. reflexivity.
Qed.

Instance swapListPerm (l : list (At * At)) : 
  Permutation At (swapList l) (swapList (rev l)):= {}.
Proof.
  - induction l.
    + reflexivity.
    + intros a0. destruct a as [a1 a2].
      replace (rev ((a1, a2) :: l)) with ((rev l) ++ [(a1, a2)]) by reflexivity.
      rewrite swapList_app. simpl. rewrite IHl. apply swapSelfInverse'.
  - induction l.
    + reflexivity.
    + intros. destruct a as [a1 a2]. simpl. 
      rewrite swapList_app. simpl. rewrite swapSelfInverse'. apply IHl. 
Defined.

Instance swapListFinPerm (l : list (At * At)) : FinPerm At (swapList l) (swapList (rev l)):= {
  perm := swapListPerm l;
}.
Proof with (subst; auto).
  exists (fold_right (fun a l => match a with (a1, a2) => (a1 :: a2 :: l) end) [] l). 
  intros a Ineq. generalize dependent a. induction l; intros.
  - simpl in Ineq. contradiction.
  - destruct a as [a1 a2]. simpl in *. destruct (eqAtDec a1 a0), (eqAtDec a2 a0)...
    right; right. apply IHl. intros C. rewrite C in Ineq. 
    apply Ineq. apply swapCasesNone...
Defined.

Definition lengthOrder := (fun (l1 l2 : list At) => length l1 < length l2).

Lemma wellFoundedLeq: well_founded lengthOrder.
Proof with (subst; auto).
  unfold lengthOrder. intros l1. constructor. induction (length l1).
  - intros l2 L. inversion L.
  - intros l2 L. induction l2.
    + constructor. intros l3 L2. inversion L2.
    + constructor. intros l3 L3. apply IHn. omega.
Qed.

Definition swapList_noDup (l : list (At * At)) := 
  (NoDup (fold_right (fun p l2 => match p with (a1, a2) =>  a1 :: a2 :: l2 end) [] l)).

Definition swapList_useful (p : finPermType At) (l : list (At * At)) :=
  (forall a a', In (a, a') l -> (a <> a' /\ p a <> a /\ p a' <> a' /\ p a <> p a')).

Lemma permutationToSwaps : forall p : finPermType At, exists (l : list (At * At)), 
  getFinPermFunction  p = swapList l /\ swapList_noDup l /\ swapList_useful p l.
Proof with (subst; auto).
  intros [[f g] [P [l I]]]. simpl. 
  generalize dependent f. generalize dependent g. generalize dependent l. simpl.
  
  apply (@well_founded_ind (list At) lengthOrder wellFoundedLeq 
   (fun l => 
      forall (g f : At → At) (P : Permutation At f g) (I : ∀ a : At, f a ≠ a → In a l), 
          ∃ l0 : list (At * At), f = swapList l0
            ∧ swapList_noDup l0
            ∧ swapList_useful (exist (λ p : (At → At) * (At → At), 
              FinPerm At (fst p) (snd p)) (f, g) {| perm := P; 
                finite := ex_intro 
                  (λ l1 : list At, ∀ a : At, f a ≠ a → In a l1) l I |}) l0)).
  - intros l H g f P I. destruct l.
    (* Base case *)
    + exists nil. split; try split...
      * extensionality a. destruct (eqAtDec (f a) a); auto. apply I in n. inversion n.
      * constructor.
      * intros a a' IA. simpl. inversion IA.
    (* Induction step *)
    + (* This will be the reduced permutation *)
      remember (compose f (swap a (g a))) as f' eqn:F'.

      (* Firt prove three auxiliary facts *)
      assert (f' a = a). { 
        subst. unfold compose. swapCases. apply permInvRight. apply P. }

      assert (forall a', a' <> a -> f a' = a' -> f' a' = a').
      { intros a' IA PA. rewrite F'. autounfold. simpl in *. 
        destruct (eqAtDec a' (g a)).
        { swapCases. subst. exfalso. apply IA. rewrite <- PA. rewrite permInvLeft...
          apply permInverse. apply P. }
        { swapCases. }
      }

      assert (lengthOrder l (a :: l)) as L. { unfold lengthOrder. constructor. }
      destruct (eqAtDec (g a) a).
      * eapply H in L. clear H. destruct L as [l1 [IH1 [IH2 IH3]]].
        unfold swapList_noDup in IH2. unfold swapList_useful in IH3. simpl in *.
        exists l1. split; [apply IH1| clear IH1]. split...
        Unshelve.
        apply g. apply P.
        intros. assert (a0 <> a). rewrite <- perm_inv_same_domain with (f := f) in e... 
        intros C... apply I in H. destruct H. symmetry in H. contradiction. apply H.
      * eapply H with (f := f') in L. clear H. destruct L as [l1 [IH1 [IH2 IH3]]].
        exists (l1 ++ [(a, g a)]). split; try split.
        { extensionality a'. rewrite swapList_app. rewrite <- IH1.
          simpl. rewrite F'. unfold compose. rewrite swapSelfInverse'. reflexivity. }
        { admit. }
        { unfold swapList_useful in *. simpl in *. intros.
          apply in_app_or in H. destruct H.
          { admit. }
          { destruct H; try inversion H.
            split; repeat try split...
            { rewrite perm_inv_same_domain'. apply n. apply P. }
            { rewrite permInvLeft... apply permInverse... }
            { rewrite permInvRight... rewrite perm_inv_same_domain'.
              apply n. apply P. }
          }
        Unshelve. apply (compose (swap a (g a)) g). 
        constructor. intros. subst. unfold compose. rewrite swapSelfInverse'.
        apply permInvRight... intros. subst... unfold compose.
        replace (g (f (swap a (g a) a0))) with ((swap a (g a) a0)).
        apply swapSelfInverse'. rewrite permInvLeft...
        intros. subst. assert (a <> a0). intros C. subst.
        unfold compose in H. rewrite swapCasesFirst in H. apply H. apply permInvRight...
        reflexivity. destruct (eqAtDec (g a) a0).
        unfold compose in H. eapply perm_chain in e. 
        rewrite perm_inv_same_domain' with (g := f) in e. apply I in e.
        destruct e. contradiction. apply H3. apply permInverse...
         apply permInverse. apply P. apply H2.
        unfold compose in H. rewrite swapCasesNone in H...
        apply I in H. destruct H. contradiction. apply H.
Admitted.

End Swap.
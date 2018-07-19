Require Import Group.
Require Import Permutation.
Require Import Swap.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Utf8.
Require Import Coq.Program.Basics.


Require Import Coq.Logic.Classical_Prop.

Section Nominal.

Parameter At : Set.

(* Equality on atoms is decidable *)

Axiom atEqDec : forall a1 a2 : At, {a1 = a2} + {a1 <> a2}.

Local Open Scope group_scope.

Definition PermA_Set X action :=  GSet (finPermType At) X (Perm At) action.

Set Typeclasses Debug.

(* A nominal set is a perm A - set in which every element has finite support *)

Definition isSupport {X action} {G : PermA_Set X action} (x : X) (s : At -> Prop) :=
  forall p : finPermType At, (forall a : At, s a -> p a = a) -> p • x = x.

(* The support of an element of a Perm At-set is defined to be the
  intersection of all supports, i.e. if a is in supp, it is in all supports *)

Inductive supp {X} `{GSet (finPermType At) X} (x : X) (a : At) : Prop := 
  | intersect: (forall (s : At -> Prop), isSupport x s -> s a) -> supp x a.

Lemma suppSwap : forall X `{GSet (finPermType At) X} (x : X) (S : At -> Prop),
  isSupport x S <-> (forall a1 a2, ~ S a1 -> ~ S a2 -> 
  (exist _ ((swap At a1 a2), (swap At a1 a2)) (swapFinPerm At a1 a2)) • x = x).
Proof with (subst; (try contradiction); auto).
  intros. split.
  - intros I a1 a2 N1 N2.
    apply I. intros a N3.
    compute. destruct (atDec a a1)... destruct (atDec a a2)...
  - intros H p A. pose proof (@permutationToFinSwaps _ p) as Swap. destruct Swap as [l [EList LProp]].
    generalize dependent x. generalize dependent p. unfold getFinPerm in *; simpl.
    induction l.
    + (* p is id *)admit.
    + intros. (* intros [[f g c1 c2] F] H1 H2 H3; unfold getFinPerm in *; simpl in *. *)
      destruct a as [a1 a2].
      assert (swapListFinPerm ((a1, a2) :: l) =  finPermCompose (swapListFinPerm l) (swapFinPerm a1 a2)).
      { apply proofIrrelevanceFinPerm. apply proofIrrelevancePerm. extensionality a... }
      simpl in *. subst. rewrite H0.
      replace (finPermCompose (swapListFinPerm l) (swapFinPerm a1 a2) • x) with
        ((swapListFinPerm l) • ((swapFinPerm a1 a2) • x)).
      Focus 2. pose proof (@isGroupAction  (Perm At) X). unfold groupAction in H1. destruct H1.
      rewrite H1. reflexivity.

      assert ((a1, a2) = (a1, a2)) by reflexivity.
      eapply or_introl in H1. apply LProp in H1.
      destruct H1 as [[H1 [H2 [H3 H4]]] H5]. simpl in *.

      assert ( ~ S a1). { intros C... }
      assert ( ~ S a2). { intros C... }

      rewrite IHl; simpl in *.
      * apply H...
      (** intros. rewrite H... *)
      * intros. pose proof H6. apply A in H8.
        destruct (atDec a a1), (atDec a a2)...
        rewrite swapCasesNone in H8...
      * reflexivity.
      * intros. pose proof H8 as AIn. 
        eapply or_intror in H8. apply LProp in H8. destruct H8 as [[H9 [H10 [H11 H12]]] D].
        inversion D...
        split... split...
        destruct (atDec a1 a), (atDec a2 a')...
        { 

Class NominalSet := {
  X :> GSet (Perm At);

  finiteSupport : forall x : X, isFinite (supp X x);
}.

End Nominal.

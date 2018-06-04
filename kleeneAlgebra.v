Require Import Utf8.

Add LoadPath "/home/miri/coq".
Require Import order.

Delimit Scope kleeneAlgebraScope with A.

Open Scope kleeneAlgebraScope.

Reserved Notation "a '•' b" (at level 40, left associativity).
Reserved Notation "a '*'" (at level 30).

Record KleeneAlgebra :=
  BuildKleeneAlgebra {
    A :> Type;
    zero : A where "0" := zero;
    one : A where "1" := one;

    plus : A -> A -> A where "a '+' b" := (plus a b);
    dot : A -> A -> A where "a '•' b" := (dot a b);
    star : A -> A where "a '*'" := (star a);

    assocPlus: forall a b c : A, (a + b) + c = a + (b + c);
    assocDot: forall a b c : A, (a • b) • c = a • (b • c);

    commPlus: forall a b : A, a + b = b + a;

    distRight: forall a b c, a • (b + c) = (a • b) + (a • c);
    distLeft: forall a b c, (a + b) • c = (a • c) + (b • c);

    idPlusLeft: forall a, a + 0 = a;
    idDotLeft: forall a, a • 1 = a;
    idDotRight: forall a, 1 • a = a;

    annihilationLeft: forall a, a • 0 = 0;
    annihilationRight: forall a, 0 • a = 0;

    idemPlus : forall a, a + a = a;

    leq1: forall a, (1 + a • (a*)) + a = a;
    leq2: forall a, (1 + (a*) • a) + a = a;
    leq3: forall a x, (a • x) + x = x -> a* • x + x = x;
    leq4: forall a x, (x • a) + x = x -> x • (a*) + x = x;
}.

Arguments zero {k}.
Arguments one {k}.
Arguments plus {k} a b.
Arguments dot {k} a b.
Arguments star {k} a.

Notation "1" := one : kleeneAlgebraScope.
Notation "0" := zero : kleeneAlgebraScope.
Notation "a '*'" := (star a) : kleeneAlgebraScope.
Notation "a '+' b" := (plus a b) : kleeneAlgebraScope.
Notation "a '•' b" := (dot a b) : kleeneAlgebraScope.

Definition lessOrEqual {k : KleeneAlgebra} (a b : A k) : Prop := 
  a + b = b.

Notation "a '≤' b" := (lessOrEqual a b) : kleeneAlgebraScope.

Lemma isPoset {k : KleeneAlgebra} : BuildPoset (A k) lessOrEqual.

Section properties.

Parameter K : KleeneAlgebra.

Corollary zeroBottom: forall a : A K, 0 ≤ a.
Proof.
  intros. unfold lessOrEqual.
  rewrite commPlus. apply idPlusLeft.
Qed.

Corollary plusLeastUpperBound: forall a b : A K, a ≤ a + b /\ b ≤ a + b /\
  (forall c, a ≤ c /\ b ≤ c → a + b ≤ c).
Proof.
  intros. split; [|split; intros].
  - unfold lessOrEqual. rewrite <- assocPlus. rewrite idemPlus. reflexivity.
  - unfold lessOrEqual. rewrite <- commPlus. rewrite assocPlus. rewrite idemPlus. reflexivity.
  - unfold lessOrEqual in *. destruct H. rewrite assocPlus. rewrite H0. rewrite H. reflexivity.
Qed.

Corollary plusMon: forall a b : A K, a ≤ b → forall c, a + c ≤ b + c.
Proof.
  unfold lessOrEqual. intros.
  replace (a + c + (b + c)) with (a + b + c).
  - rewrite H. reflexivity.
  - replace (a + c + (b + c)) with (a + b + (c + c)).
    + rewrite idemPlus. reflexivity.
    + rewrite <- assocPlus. rewrite commPlus. replace (a + b + c) with (a + (b + c)).
      * rewrite <-assocPlus. replace (c + a) with (a + c).
        reflexivity. apply commPlus.
      * symmetry. apply assocPlus.
Qed.

Corollary dotMonRight: forall a b : A K, a ≤ b → forall c, a • c ≤ b • c.
Proof.
  unfold lessOrEqual. intros.
  rewrite <- distLeft. rewrite H. reflexivity.
Qed.

Corollary dotMonLeft: forall a b : A K, a ≤ b → forall c, c • a ≤ c • b.
Proof.
  unfold lessOrEqual. intros.
  rewrite <- distRight. rewrite H. reflexivity.
Qed.
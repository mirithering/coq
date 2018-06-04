Parameter object : Type.
Parameter arrow : Type.
Parameter source : arrow -> object -> Prop.
Parameter target : arrow -> object -> Prop.

Notation "f ':' A '~>' B" := ((source f A) /\ (target f B)) (at level 40). 

Axiom R1a: forall A, exists u, u: A ~> A.
Axiom R1b: forall A B C f g, f:A ~> B /\ g: B ~> C -> exists gf, gf: A ~> C.

Parameter top : object.
Axiom R2: forall A, exists bang, bang: A ~> top.

Parameter conj : object -> object -> object.
Notation "A 'and' B" := (conj A B) (at level 25).

Axiom R3a: forall A B, exists prA, prA : A and B ~> A.
Axiom R3b: forall A B, exists prB, prB : A and B ~> B.
Axiom R3c: forall A B C f g, f: C ~> A /\ g: C ~> B -> exists h, h: C ~> A and B.

Lemma andComm: forall A B, exists swap, swap: A and B ~> B and A.
Proof.
  intros.
  pose proof (R3b A B). destruct H.
  pose proof (R3a A B). destruct H0.
  eapply R3c. split.
  - apply H.
  - apply H0.
Qed.
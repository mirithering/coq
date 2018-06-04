Require Import Utf8.

Delimit Scope posetScope with P.

Open Scope posetScope.

Record Poset :=
  BuildPoset {
    P :> Type;

    leq: P -> P -> Prop where "a '≤' b" := (leq a b);

    reflexivity: forall p : P, p ≤ p;
    antisymmetry: forall p q : P, p ≤ q /\ q ≤ p → p = q;
    transitivity: forall p q r : P, p ≤ q /\ q ≤ r → p ≤ r;
}.

Arguments leq {p} a b.

Notation "p '≤' q" := (leq p q) : posetScope.
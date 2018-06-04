Class Category (obj: Type) (hom: obj -> obj -> Type) := {
  id: forall {A}, hom A A;
  comp: forall {A B C} (f : hom B C) (g : hom A B), hom A C;
  idLeft: forall {A B} (f: hom A B), comp id f = f;
  idRight: forall {A B} (f : hom B A), comp f id = f;
  compAssoc: forall {A B C D} (f : hom A B) (g : hom B C) (h : hom C D),
    comp h (comp g f) = comp (comp h g) f
}. 

Section universal.

Variable obj : Type.
Variable hom : obj -> obj -> Type.
Variable isCat : Category obj hom.

Definition epimorphism {A B} (f : hom A B) :=
  forall C (g1 g2 : hom B C), comp g1 f = comp g2 f -> g1 = g2.

Definition monomorphism {A B} (f : hom A B) :=
  forall C (g1 g2 : hom C A), comp f g1 = comp f g2 -> g1 = g2.

Definition inverse {A B} (f : hom A B) (f' : hom B A) := comp f f' = id /\ comp f' f = id.

Definition isomorphism {A B} (f : hom A B) :=
  exists (f' : hom B A), inverse f f'.

Definition objIso (A B : obj) := exists (f : hom A B), isomorphism f.

Lemma isoMono: forall {A B} (f : hom A B), isomorphism f -> monomorphism f.
Proof.
  unfold monomorphism. intros A B f Iso C g1 g2 Comp. inversion Iso as [f' H]. destruct H as [L R].
  replace g2 with (comp id g2) by apply idLeft. 
  replace g1 with (comp id g1) by apply idLeft.
  rewrite <- R. rewrite <- compAssoc. rewrite Comp. apply compAssoc.
Qed.

Lemma isoEpi: forall {A B} (f :hom A B), isomorphism f -> epimorphism f.
Proof.
  unfold epimorphism. intros A B f Iso C g1 g2 Comp. inversion Iso as [f' H]. destruct H as [L R].
  replace g2 with (comp g2 id) by apply idRight.
  replace g1 with (comp g1 id) by apply idRight.
  rewrite <- L. rewrite compAssoc. rewrite Comp. rewrite compAssoc. reflexivity.
Qed.

Lemma isoUnique: forall {A B} (f1 f2 : hom A B) (f : hom B A), inverse f1 f /\ inverse f2 f -> f1 = f2.
Proof.
  intros A B f1 f2 f Inv. destruct Inv as [Inv1 Inv2]. destruct Inv1 as [Inv1L Inv1R].
  destruct Inv2 as [Inv2L Inv2R].
  replace f1 with (comp f1 id) by apply idRight. rewrite <- Inv2R. rewrite compAssoc.
  rewrite Inv1L. apply idLeft.
Qed.

Definition terminal (B : obj) := forall A, exists ! f : hom A B, True.

Lemma terminalUniqueIso1 : forall B1 B2, terminal B1 /\ terminal B2 -> objIso B1 B2.
Proof.
  unfold objIso. intros B1 B2 Term. destruct Term as [TermB1 TermB2].
  pose proof TermB1 as TermB1Copy.
  pose proof TermB2 as TermB2Copy.
  destruct TermB1 with B1 as [id1 Uid1].
  destruct TermB2 with B2 as [id2 Uid2].
  destruct TermB1Copy with B2 as [f1 Uf1].
  destruct TermB2Copy with B1 as [f2 Uf2].
  exists f2. unfold isomorphism. exists f1.
  unfold inverse. split.
  - inversion Uid2. rewrite <- H0 with (comp f2 f1) by constructor. rewrite (H0 id) by constructor. reflexivity.
  - inversion Uid1. rewrite <- H0 with (comp f1 f2) by constructor. rewrite (H0 id) by constructor. reflexivity.
Qed.  

Lemma terminalUniqueIso2: forall B1 B2, terminal B1 /\ objIso B1 B2 -> terminal B2.
Proof.
  intros B1 B2 Con. destruct Con as [T Iso]. destruct Iso as [f fIso]. inversion fIso as [f' Inv].
  unfold terminal. intros A. unfold terminal in T. assert (exists ! g : hom A B1, True) by apply T.
  destruct H. exists (comp f x). split.
  - constructor.
  - intros g' Top. replace g' with (comp id g') by apply idLeft.
    inversion Inv as [L R]. rewrite <- L. rewrite <- compAssoc. replace (comp f' g') with x; try reflexivity.
    + apply H. constructor.
Qed.
     
End universal.


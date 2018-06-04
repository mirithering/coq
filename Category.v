Require Import Utf8.
Require Import Coq.Program.Basics.

Class Category := {
  obj :> Type;
  hom : obj -> obj -> Type;

  id: forall {A}, hom A A;
  comp: forall {A B C} (f : hom B C) (g : hom A B), hom A C;

  idLeft: forall {A B} (f: hom A B), comp id f = f;
  idRight: forall {A B} (f : hom B A), comp f id = f;
  compAssoc: forall {A B C D} (f : hom A B) (g : hom B C) (h : hom C D),
    comp h (comp g f) = comp (comp h g) f
}.

Coercion obj: Category >-> Sortclass.

Bind Scope morphism_scope with hom.
Bind Scope object_scope with obj.
Bind Scope category_scope with Category.
Local Open Scope category_scope.
Local Open Scope morphism_scope.
Local Open Scope object_scope.

Notation "1" := id : morphism_scope.
Notation "f '•' g" := (comp f g) (at level 30) : morphism_scope.

(*** Dualization *)

Instance Dual (Cat : Category) : Category := {
  obj := @obj Cat;
  hom := (fun A B => @hom Cat B A);
}.
Proof.
  - intros A. apply id.
  - intros A B C f g. eapply comp. apply g. apply f.
  - intros A B f. simpl. apply idRight.
  - intros A B f. apply idLeft.
  - intros A B C D f g h. simpl. rewrite compAssoc. reflexivity.
Defined.

Bind Scope dual_scope with Dual.
Local Open Scope dual_scope.

Notation "C ¯" := (Dual C) (at level 20, left associativity) : dual_scope.

Lemma dualInvolutive : forall C : Category, Dual (Dual C) = C.
Proof.
  (* I need to find a convenient way to do this *)
Admitted.

(*** Epis, Monos and Isos *)

Definition epimorphism `{Category} {A B} (f : hom A B) :=
  forall C (g1 g2 : hom B C), g1 • f = g2 • f -> g1 = g2.

Definition monomorphism `{Category} {A B} (f : hom A B) :=
  forall C (g1 g2 : hom C A), f • g1 = f • g2 -> g1 = g2.

Definition isInverse `{Category} {A B} (f : hom A B) (f' : hom B A) := f • f' = 1 /\ f' • f = 1.

Definition isomorphism `{Category} {A B} (f : hom A B) :=
  exists (f' : hom B A), isInverse f f'.

Definition objIsomorphic `{Category} (A B : obj) := exists (f : hom A B), isomorphism f.

Notation "A == B" := (objIsomorphic A B) (at level 70, right associativity) : object_scope.

Lemma isoIsMono: forall `{Category} {A B} (f : hom A B), isomorphism f -> monomorphism f.
Proof.
  unfold monomorphism. intros Cat A B f Iso C g1 g2 Comp. inversion Iso as [f' H]. destruct H as [L R].
  replace g2 with (comp id g2) by apply idLeft. 
  replace g1 with (comp id g1) by apply idLeft.
  rewrite <- R. rewrite <- compAssoc. rewrite Comp. apply compAssoc.
Qed.

Lemma isoIsEpi: forall `{Category} {A B} (f :hom A B), isomorphism f -> epimorphism f.
Proof.
  unfold epimorphism. intros Cat A B f Iso C g1 g2 Comp. inversion Iso as [f' H]. destruct H as [L R].
  replace g2 with (comp g2 id) by apply idRight.
  replace g1 with (comp g1 id) by apply idRight.
  rewrite <- L. rewrite compAssoc. rewrite Comp. rewrite compAssoc. reflexivity.
Qed.
Definition isPermutation {A : Set} (f g : A -> A) : Prop := compose f g = id
   /\ compose g f = id.

Lemma inverseUnique: forall `{Category} {A B} (f1 f2 : hom A B) (f : hom B A), 
  isInverse f1 f /\ isInverse f2 f -> f1 = f2.
Proof.
  intros Cat A B f1 f2 f Inv. destruct Inv as [Inv1 Inv2]. destruct Inv1 as [Inv1L Inv1R].
  destruct Inv2 as [Inv2L Inv2R].
  replace f1 with (comp f1 id) by apply idRight. rewrite <- Inv2R. rewrite compAssoc.
  rewrite Inv1L. apply idLeft.
Qed.

(*** Initial and Terminal objects *)

Definition isTerminal `{Category} (T : obj) := forall A, exists ! f : hom A T, True.

Lemma terminalUniqueIso1 `{Category} : forall B1 B2, isTerminal B1 /\ isTerminal B2 -> B1 == B2.
Proof.
  unfold objIsomorphic. intros B1 B2 [TermB1 TermB2].
  pose proof TermB1 as TermB1Copy.
  pose proof TermB2 as TermB2Copy.
  destruct TermB1 with B1 as [id1 Uid1].
  destruct TermB2 with B2 as [id2 Uid2].
  destruct TermB1Copy with B2 as [f1 Uf1].
  destruct TermB2Copy with B1 as [f2 Uf2].
  exists f2. unfold isomorphism. exists f1.
  unfold isInverse. split.
  - inversion Uid2. rewrite <- H1 with (comp f2 f1) by constructor. rewrite (H1 id) by constructor. reflexivity.
  - inversion Uid1. rewrite <- H1 with (comp f1 f2) by constructor. rewrite (H1 id) by constructor. reflexivity.
Qed.

Lemma terminalUniqueIso2 `{Category}: forall B1 B2, isTerminal B1 /\ B1 == B2 -> isTerminal B2.
Proof.
  intros B1 B2 Con. destruct Con as [T Iso]. destruct Iso as [f fIso]. inversion fIso as [f' Inv].
  unfold isTerminal. intros A. unfold isTerminal in T. assert (exists ! g : hom A B1, True) by apply T.
  destruct H0. exists (comp f x). split.
  - constructor.
  - intros g' Top. replace g' with (comp id g') by apply idLeft.
    inversion Inv as [L R]. rewrite <- L. rewrite <- compAssoc. replace (comp f' g') with x; try reflexivity.
    + apply H0. constructor.
Qed.

Definition isInitial `{Category} (I : obj) := forall A, exists ! f : hom I A, True.

Corollary initialDualTerminal : 
  forall (Cat : Category) (O : @obj Cat), @isTerminal Cat O <-> @isInitial (Dual Cat) O.
Proof.
  intros Cat O. split; [intros hI A | intros hT A].
  - destruct hI with A as [f [[] H]]. exists f. split; try apply I. intros g []. rewrite <- H; auto.
  - destruct hT with A as [f [[] H]]. exists f. split; try apply I. intros g []. rewrite <- H; auto.
Qed.

Lemma initialUniqueIso1 `{Category} : forall B1 B2, isInitial B1 /\ isInitial B2 
  -> B1 == B2.
Proof.
  (* use duality *)
Admitted.

Lemma initialUniqueIso2 `{Category}: forall B1 B2, 
  isInitial B1 /\ B1 == B2 -> isInitial B2.
Proof.
  (* use duality *)
Admitted.

(*** Functors *)

Class Functor (Cat1 Cat2 : Category) := {
  F_Obj : Cat1 -> Cat2;
  F_Hom : forall {A B : Cat1}, hom A B -> hom (F_Obj A) (F_Obj B);

  idProp : forall (B : Cat1), F_Hom (@id Cat1 B) = id;
  compProp: forall (A B C : Cat1) (f : hom B C) (g: hom A B), 
    F_Hom (f • g) = (F_Hom f) • (F_Hom g);
}.

Bind Scope functor_scope with Functor.
Local Open Scope functor_scope.

Arguments F_Obj {Cat1} {Cat2} (Functor).
Arguments F_Hom {Cat1} {Cat2} (Functor) {A} {B}.

Definition functorObjectPart {Cat1 Cat2 : Category} (F : Functor Cat1 Cat2) 
  (A : @obj Cat1) : @obj Cat2 := @F_Obj Cat1 Cat2 F A.
Coercion functorObjectPart : Functor >-> Funclass.

Notation "F [ f ]" := (F_Hom F f) (at level 40) : functor_scope.

(* Composition of two functors is a functor *)
Instance functorComposition {Cat1 Cat2 Cat3} 
  (F : Functor Cat2 Cat3) (G: Functor Cat1 Cat2) : Functor Cat1 Cat3 := {
  F_Obj := compose F G;
  F_Hom := (fun A B f => F [G [f]]);
}.
Proof.
  - intros B. rewrite idProp. rewrite idProp. reflexivity.
  - intros A B C f g. rewrite compProp. rewrite compProp. reflexivity.
Defined.

Notation "F * G" := (functorComposition F G) : functor_scope.

(* Identity Functor *)
Instance Id {Cat} : Functor Cat Cat := {
  F_Obj := (fun A => A);
  F_Hom := (fun A B f => f);
}.
Proof.
  - reflexivity.
  - reflexivity.
Qed.

(* A functor is an isomorphism if it has an inverse *)
Definition functorIsomorphism {Cat1 Cat2} (F : Functor Cat1 Cat2) :=
  exists (G : Functor Cat2 Cat1), 
    F * G = Id /\ G * F = Id.

(* Two categories are isomorphic if there is an ismorphism between them *)

Definition isomorphismCategories (Cat1 Cat2 : Category) := 
  exists F, functorIsomorphism F.

Notation "C == B" := (isomorphismCategories C B) : category_scope.

(* full functors are functors mapping into all morphisms between objects the map into *)

Definition full {C B : Category} (T : Functor C B) :=
  forall (c c' : obj) (g : hom (T c) (T c')), 
  exists (f : hom c c'), g = T[f].

Corollary compositionFull {C1 C2 C3} : forall (F : Functor C2 C3) (G : Functor C1 C2),
  full F -> full G -> full (F * G).
Proof.
  unfold full. intros F G hFF hFG c c' g. simpl in g. 
  destruct (hFF (G c) (G c') g) as [h E]; subst.
  destruct (hFG c c' h) as [g E]; subst. exists g.
  reflexivity.
Qed.

(* faithful functors or embeddings are injective on the morphisms they map into *)

Definition faithful {C B : Category} (T : Functor C B) :=
  forall (c c' : obj) (f1 f2 : hom c c'), T[f1] = T[f2] -> f1 = f2.

Corollary compositionFaithful {C1 C2 C3} : forall (F : Functor C2 C3) (G : Functor C1 C2),
  faithful F -> faithful G -> faithful (F * G).
Proof.
  unfold faithful. intros F G hFF hFG c c' f1 f2 hE. simpl in hE.
  apply hFF in hE. apply hFG in hE. auto.
Qed.

(*** Natural Transformations *)

Class NatTrans {C B : Category} (S T : Functor C B) := {
  component : forall c, hom (S c) (T c);

  naturality : forall c c' (f : hom c c'), 
    ((component c') • (S[f])) = ((T[f]) • (component c));
}.

Bind Scope natTrans_scope with NatTrans.

Coercion component : NatTrans >-> Funclass.

(* there is two ways of composing nat trans and functors to obtain a new nat. trans *)

Instance idTrans {C B: Category} (F : Functor C B) : NatTrans F F := {
  component := (fun c => id);
}.
Proof.
  intros c c' f. rewrite idLeft. rewrite idRight. reflexivity.
Defined.

(* todo compose natural transformations *)

Instance natTransFunctor {A B C} {F G : Functor A B} 
  (e : NatTrans F G) (H : Functor C A) : NatTrans (F * H) (G * H) := {
  component := (fun c => e (H c));
}.
Proof.
  intros c c' f. simpl. apply naturality.
Qed.

Instance functorNatTrans {A B C} {F G: Functor A B}
  (e : NatTrans F G) (H : Functor B C) : NatTrans (H * F) (H * G) := {
  component := (fun c => F_Hom H (e c));
}.
Proof.
  intros c c' f . simpl.
  rewrite <- (@compProp B C H (F c) (F c') (G c')).
  rewrite <- (@compProp B C H (F c) (G c) (G c')).
  rewrite naturality. reflexivity.
Qed.

(*** Monads *)
(*
Class Monad {C : Category} := {
  T : Functor C C;
  eta : NatTrans Id T;
  mu : NatTrans (T * T) T;

  unitLaw1 : forall c, (mu _) • F_Hom T (eta c) = id;
}.
*)


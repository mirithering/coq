Require Import Utf8 Basics Setoid FunctionalExtensionality List.

Import EqNotations.

Add LoadPath "Category".
Require Import Category.

Generalizable Variables obj hom objA homA objB homB objC homC compA compB.

(*** Functors *)

Class Functor {obj1 obj2 hom1 hom2} `(Category obj1 hom1) `(Category obj2 hom2)
  (Fo : obj1 -> obj2) (Fh : forall {A B : obj1}, hom1 A B -> hom2 (Fo A) (Fo B)) := {
  functor_id : forall (B : obj1), Fh (cid B) = 1;
  functor_comp : forall (A B C : obj1) (f : hom1 B C) (g: hom1 A B), 
    Fh (f • g) = (Fh f) • (Fh g);
}.

Definition getObjPart `(Functor) := Fo.
Definition getHomPart `(Functor) := Fh.

Notation "F [ c ]" := (getObjPart F c) (at level 20).
Notation "F [[ h ]]" := (getHomPart F _ _ h) (at level 20).

Hint Unfold getObjPart getHomPart.

(* Notation for Functor C D Fo Fh? *)
(* It sucks that it's not possible to write `(Functor C D) and let it automatically
  instantiate the names of the underlying functions of the functor. I am not sure
  why not even `(Functor _ _ _ _ _ _ C D) works, it just omits the fact that
  the arguments need to be categories... Ah okay, if I have the arguments written as "_"
  in the premises as category, then it will automatically insert C and D *)

(* Composition of two functors is a functor *)
Instance functorComposition  `{C1: Category} `{C2: Category} `{C3: Category}
  Fo Fh Go Gh
  (F : Functor C2 C3 Fo Fh) (G : Functor C1 C2 Go Gh) : 
  Functor C1 C3 (compose Fo Go) 
  (fun A B => compose (Fh (Go A) (Go B)) (Gh A B)) := {}.
Proof.
  - intros B. unfold compose. rewrite functor_id. rewrite functor_id. reflexivity.
  - intros A B C h h'. unfold compose. rewrite functor_comp. rewrite functor_comp. reflexivity.
Defined.

Notation "( Fo , Fh ) * ( Go , Gh )" := (functorComposition Fo Fh Go Gh _ _).
Notation "F * G" := (functorComposition _ _ _ _ F G).

Remove Hints functorComposition : typeclass_instances.

(* Identity Functor *)
Instance Id_Functor `{Category} : Functor _ _ (fun A => A) (fun A B f => f).
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
Defined.

Instance Const_Functor `(C1 : Category) `(C2 : Category) A : 
  Functor C1 C2 (fun B => A) (fun A B h => 1).
Proof.
  constructor.
  - reflexivity.
  - intros. symmetry. apply idRight.
Defined.

Definition functor_inverse {o1 o2 h1 h2} `{Category o1 h1} `{Category o2 h2}
  (f : o1 -> o2) 
  (f' : forall A B, h1 A B -> h2 (f A) (f B))
  (g : o2 -> o1) 
  (g' : forall A B, h2 A B -> h1 (g A) (g B))
  (E1 : forall A, f (g A) = A)
  (E2 : forall A, g (f A) = A) :=
  (forall A B (h : h1 A B), rew [fun h => h]
    (eq_ind_r (λ o : o1, h1 o (g (f B)) = h1 A B) 
      (eq_ind_r (λ o : o1, h1 A o = h1 A B) 
        eq_refl (E2 B)) (E2 A)) in g' _ _(f' _ _ h) = h) /\
  (forall A B (h : h2 A B), rew [fun h => h]
    (eq_ind_r (λ o : o2, h2 o (f (g B)) = h2 A B) 
      (eq_ind_r (λ o : o2, h2 A o = h2 A B) 
        eq_refl (E1 B)) (E1 A)) in f' _ _(g' _ _ h) = h).

Class Functor_Isomorphism {o1 o2 h1 h2} `{Category o1 h1} `{Category o2 h2}
  (Fo : o1 -> o2) Fh := {
  is_functor :> Functor _ _ Fo Fh;
  has_inverse : exists (Go : o2 -> o1) (Gh : forall (A B : o2), h2 A B -> h1 (Go A) (Go B))
    (G : Functor _ _ Go Gh) 
    (E1 : forall A, Fo (Go A) = A) (E2 : forall A, Go (Fo A) = A),
    functor_inverse Fo Fh Go Gh E1 E2
}.

(* Two categories are isomorphic if there is an ismorphism between them *)

Definition isomorphismCategories {o1 o2 h1 h2} 
  `{C1 : Category o1 h1} `{C2: Category o2 h2} := 
  exists (f : o1 -> o2) f', Functor_Isomorphism f f'.

Notation "C =C= B" := (isomorphismCategories C B)(at level 40) : category_scope.


(* full functors are functors mapping into all morphisms between objects the map into *)
Definition full `(F : Functor) := forall c c' (g : F [c] --> F [c']),
  exists (h : c --> c'), g = F [[h]].

Hint Unfold full.

Corollary compositionFull `{C1 : Category} `{C2 : Category} `{C3 : Category} 
  Fo Fh Go Gh: 
  forall (F : Functor C2 C3 Fo Fh) (G : Functor C1 C2 Go Gh),
  full F -> full G -> full (F * G).
Proof.
  autounfold. intros F G hFF hFG c c' g. simpl in g. 
  destruct (hFF (Go c) (Go c') g) as [h E]; subst.
  destruct (hFG c c' h) as [g E]; subst. exists g.
  reflexivity.
Qed.

(* faithful functors or embeddings are injective on the morphisms they map into *)

Definition faithful `(F : Functor) :=
  forall c c' (f1 f2 : c --> c'), F [[f1]] = F [[f2]] -> f1 = f2.

Hint Unfold faithful.

Corollary compositionFaithful `{C1 : Category} `{C2 : Category}
  `{C3 : Category} Fo Go Fh Gh 
  (F : Functor C2 C3 Fo Fh) (G : Functor C1 C2 Go Gh) :
  faithful F -> faithful G -> faithful (F * G).
Proof.
  autounfold. intros E1 E2 c c' h1 h2 C. apply E2. apply E1. apply C.
Qed.

(* A full and faithful functor is an embedding, but not an isomorphism! *)

(** EXAMPLES **)
Open Scope type_scope.

Instance Product_Functor : Functor Category_Set Category_Set (fun A : Type => A * A)
  (fun (A B : Type) (h : A -> B) => (fun p => (h (fst p), h (snd p)))).
  constructor; intros.
  - extensionality p. destruct p. reflexivity.
  - extensionality p. destruct p. reflexivity.
Defined.

Instance List_Functor : Functor Category_Set Category_Set
  (fun A : Type => list A)
  (fun (A B : Type) (h : A -> B) => (fun l => map h l)).
  constructor; intros.
  - extensionality l. induction l; try reflexivity. simpl in *. rewrite IHl. reflexivity.
  - extensionality l. induction l; try reflexivity.
    simpl in *. rewrite IHl. reflexivity.
Defined.

Inductive tree A :=
  | leaf : A -> tree A
  | bin : tree A -> tree A -> tree A.

Arguments leaf {A} a.
Arguments bin {A} t1 t2.

Fixpoint tree_map {A B} (h : A -> B) (t : tree A) : tree B :=
  match t with
    | leaf a => leaf (h a)
    | bin t1 t2 => bin (tree_map h t1) (tree_map h t2)
  end.

Instance Tree_Functor : Functor Category_Set Category_Set
  (fun A => tree A)
  (fun A B (h : A -> B) t => tree_map h t).
  constructor.
  - intros B. extensionality t. induction t; auto. 
    simpl in *. rewrite IHt1, IHt2. reflexivity.
  - intros A B C f g. extensionality t. induction t; simpl in *; auto.
    rewrite IHt1, IHt2. reflexivity.
Defined.

Instance Hom_Functor `{C : Category} (A : obj) : 
  Functor C Category_Set
  (fun B => A --> B)
  (fun C B (f : C --> B) (h : A --> C) => f • h).
  constructor.
  - intros. extensionality h. apply idLeft.
  - intros. extensionality h. compute. rewrite compAssoc. reflexivity.
Defined.

Notation "C '[' A '-]'" := (@Hom_Functor _ _ _ _ C A) (at level 70).
Notation "C '[-' B ']'" := (@Hom_Functor _ _ _ _ (Dual C) B) (at level 70).

Require Import Ensembles.

Instance P_Functor : Functor Category_Set Category_Set (fun A => Ensemble A)
  (fun A B (h : A -> B) S b => exists a, S a /\ h a = b).
  constructor.
  - intros B. extensionality S. simpl. 
    apply Extensionality_Ensembles. split; intros b I.
    + destruct I. destruct H. subst. apply H.
    + exists b. split; auto.
  - intros A B C f g. extensionality S. autounfold. apply Extensionality_Ensembles.
    split; intros c H.
    + compute in *. destruct H as [a [Ia E] ]. exists (g a). split; auto.
      * exists a. split; auto.
    + destruct H as [b [ [a [Sa Ea] ] Eb] ].
      subst. compute. exists a. split; auto.
Defined.
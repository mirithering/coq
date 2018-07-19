Require Import Utf8 Basics Setoid FunctionalExtensionality List Ensembles.

Import ListNotations.

Import EqNotations.

Add LoadPath "Category".
Require Import Category Functor.

(*** Natural Transformations *)

Class NatTrans `{C : Category} `{D : Category}
  Fo Fh Go Gh (F : Functor C D Fo Fh) (G : Functor C D Go Gh)
  (alpha : forall c, (Fo c) --> (Go c)) := {
  naturality : forall c c' (f : c --> c'), 
    ((alpha c') • (F [[f]])) = ((G [[f]]) • (alpha c));
}.

(* there is two ways of composing nat trans and functors to obtain a new nat. trans *)
(*
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
Qed.*)

(** EXAMPLES **)

Fixpoint flatten A (t : tree A) : list A :=
  match t with
    | leaf a => [a]
    | bin t1 t2 => (flatten A t1) ++ (flatten A t2)
  end.

Instance Natural_Flatten : NatTrans _ _ _ _ Tree_Functor List_Functor flatten.
  constructor. intros A B h. extensionality t.
  induction t.
  - compute. reflexivity.
  - autounfold in *. simpl. rewrite IHt1, IHt2. rewrite map_app. auto.
Defined.

Instance Natural_Singleton : NatTrans _ _ _ _ _ P_Functor (fun A => Singleton A).
  constructor. intros A B f. autounfold. extensionality a.
  apply Extensionality_Ensembles. split; intros b H.
  + compute in *. inversion H. exists a. split; auto. constructor.
  + compute in *. destruct H as [a' [H1 H2] ]. inversion H1. subst. constructor.
Defined.


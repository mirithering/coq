Parameter S : Type.
Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Infix "•" := compose (at level 40).

Open Scope type_scope.

Notation "'K' X" := (S * X) (at level 20, right associativity).
Notation "'[K' f ']'" := (fun p => match p with | (s, x) => (s, f x) end).
Definition  delta (X : Type) (p : K X) : K (K X):=
  match p with | (s, x) => (s, (s, x)) end.
Definition epsilon (X : Type) (p : K X) : X :=
  match p with | (s, x) => x end.

Notation "'T' X" := (S -> X) (at level 15, right associativity).
Notation "'[T' f ']'" := (fun p s => f ( p s )).
Definition eta (X : Type) (x : X) : T X := (fun s => x).
Definition mu (X : Type) (f : T (T X)) : T X := (fun s : S => (f s) s).

Definition lambda (X : Type) (p : K T X) : T K X :=
  match p with | (s1,p) => (fun s2 => (s1, p(s2))) end.

Lemma distMu : forall X, (lambda X) • [K (mu X)] = (mu (K X)) • [T (lambda X)] • (lambda (T X)).
Proof.
  intros. extensionality x. extensionality s. destruct x. reflexivity.
Qed.

Lemma distDelta : forall X, [T (delta X)] • lambda X = lambda (K X) • [K (lambda X)] • delta (T X).
Proof.
  intros. extensionality p. destruct p. extensionality s'. compute. reflexivity.
Qed.

Lemma distEta : forall X, eta (K X) = (lambda X) • [K (eta X)].
Proof.
  intros. extensionality x. destruct x. compute. reflexivity.
Qed.

Lemma distEpsilon : forall X, [T (epsilon X)] • lambda X = epsilon (T X).
Proof.
  intros. extensionality x. destruct x. extensionality s'. compute. reflexivity.
Qed.
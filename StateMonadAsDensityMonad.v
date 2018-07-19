Variable S : Set.

(* Using Theorem from 11.6.18 in Paper notes *)

Definition R X : Type := S -> X.
Definition W X : Type := S * X.

Definition R_fun {X Y} (f : X -> Y) (p : R X) : R Y :=
  fun s => f (p s).

Definition W_fun {X Y} (f : X -> Y) (p : W X) : W Y :=
  match p with (s, x) => (s, f x) end.

Definition eta {X} : X -> R (W X) :=
  fun x => (fun s => (s, x)).

Definition delta {X} : W (R X) -> R (W X) :=
  fun p => match p with (s, q) => (fun s' => (s', q(s))) end.

Definition epsilon' {X} : R (R (W X)) -> R X:=
  fun p => (fun s => match p s s with (s, x) => x end).

Require Import FunctionalExtensionality.

Lemma prop1 {X} (p : R X): (R_fun delta) (eta p) = R_fun eta p.
Proof.
  unfold R_fun, delta, eta. extensionality s. extensionality s'. reflexivity.
Qed.

Lemma prop2 {X} (p : R X) : epsilon' ((R_fun eta) p) = p.
Proof.
  unfold epsilon', R_fun, eta. extensionality s. reflexivity.
Qed.

Lemma prop3 {X} (p : R (W X)) : p = epsilon' (R_fun delta (R_fun (W_fun eta) p)).
Proof.
  unfold epsilon', R_fun, delta, W_fun, eta. extensionality s.
  destruct (p s). reflexivity.
Qed.

Definition mu {X} (p : R (W (R (W X)))) : R (W X) := epsilon' ( R_fun delta p).

Definition mu' {X} (p : R (W (R (W X)))) : R (W X).
  unfold R, W in *. intros. apply p in H. destruct H. apply p0 in s. apply s.
Defined.

Lemma mu_correct {X} (p : R (W (R (W X)))) : mu p = mu' p.
  extensionality s. unfold mu, mu', epsilon', R_fun, delta.
  destruct (p s). reflexivity.
Qed.
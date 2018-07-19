Require Import List Omega FunctionalExtensionality Basics.

Variable G : Set.
Variable list_G : list G.
Variable list_G_k : nat -> list (list G).

Axiom G_finite: forall g : G, In g list_G.

Axiom finite_words_finite : forall k (w : list G), length w = k -> In w (list_G_k k).

Open Scope list_scope.

Definition isR (X : Type) (p : (list G -> list G) * (list G -> X)) := 
  match p with | (t, c) => exists k, forall w v, 
  length w = k -> t(w ++ v) = v /\ c(w ++ v) = c(w) end.

Inductive R (X : Type) : Type := 
  | C : forall t c, isR X (t, c) -> R X.

Axiom proof_irrelevance_R : 
forall X f1 f2 g1 g2 H1 H2 (E1 : f2 = f1) (E2 : g2 = g1),
  C X f1 g1 H1 = C X f2 g2 H2.

Lemma R_fun_correct {X Y} (f : X -> Y)
(t : list G -> list G)
(c : list G -> X)
(i : isR X (t, c)) :
isR Y (t, fun s : list G => f (c s)).
Proof.
  destruct i. exists x. intros.
  eapply H in H0. destruct H0.
  split.
  - apply H0.
  - rewrite H1. reflexivity.
Qed.

Definition R_fun {X Y : Type} (f : X -> Y) (p : R X) : R Y :=
  match p with | C _ t c i =>
  (C Y t (fun s => f (c (s))) (R_fun_correct f t c i)) end.

Lemma R_fun_compose {X Y Z : Type} (f : Y -> Z) (g : X -> Y) :
  R_fun (compose f g) = compose (R_fun f) (R_fun g).
Proof.
  extensionality x. unfold R_fun.
  destruct x. apply proof_irrelevance_R.
  - reflexivity.
  - reflexivity.
Qed.

Definition W (X : Type) : Type := (list G) * X.

Definition W_fun (X Y : Type) (f : X -> Y) (p : W X) : W Y.
  destruct p. apply (l, f x).
Defined.

Lemma eta_correct {X} (x : X) :
  isR (W X) (fun w : list G => w, fun _ : list G => (nil, x)).
Proof.
  intros. unfold isR. exists 0. intros.
  split.
  - simpl. rewrite length_zero_iff_nil in H. rewrite H. reflexivity.
  - reflexivity.
Qed.

Definition eta {X : Type} (x : X) : R (W X) :=
  (C (W X) (fun (w: list G) => w) 
  (fun (w : list G) => (@nil G, x)) (eta_correct x)).

Lemma delta_correct {X : Type}
(s : list G)
(t : list G -> list G)
(c : list G -> X)
(H : isR X (t, c)) :
isR (W X) (fun s' => s'), 
  fun s' : list G => (s', c (s ++ s'))).
Proof.
  destruct H. exists x. 
  intros. eapply H in H0. destruct H0. split.
  
  - rewrite H0. admit.
  - rewrite H0. reflexivity.
Qed.


Definition delta {X : Type} (pp : W (R X)) : R (W X) :=
  match pp with (s, p) => match p with (C _ t c H) =>
  (C (W X) (fun s' => t(s ++ t(s'))) (fun s' => (s', c(s ++ t(s')))) 
  (delta_correct s t c H)) end end.

Import Nat.
Require Import PeanoNat Epsilon.


Fixpoint maximum {X : Type} (l : list X) (f : X -> nat) : nat :=
  match l with
    | nil => 0
    | (x :: l) => let n := maximum l f in (if (f x) <=? n then n else f x)
  end.

Definition getDependency {X : Type} (c : list G -> R X) (l : list G): nat.
  apply c in l. destruct l.
  apply constructive_indefinite_description in i. destruct i.
  apply x.
Defined.

Fixpoint drop {X : Type} (k : nat) (l : list X) := match k,l with
  | 0, _ => l
  | _, nil => nil
  | S k, x :: l => drop k l
  end.


Fixpoint take {X : Type} (k : nat) (l : list X) := match k,l with
  | 0, _ => nil
  | _, nil => nil
  | S k, x :: l => x :: take k l
  end.
  
Require Import Omega.

Lemma helper {X : Type}
(t1 : list G -> list G)
(c1 : list G -> R X)
(k1 : nat)
(R1 : forall w v : list G, length w = k1 -> t1 (w ++ v) = v /\ c1 (w ++ v) = c1 w)
(k2 : nat)
(Heqk2 : k2 = maximum (list_G_k k1) (getDependency c1)) :
isR X
  (fun s : list G => match c1 s with
                     | C _ _ _ _ => drop k2 (t1 s)
                     end, fun s : list G => match c1 s with
                                            | C _ _ c2 _ => c2 (t1 s)
                                            end).
Proof.
  unfold isR. exists (k1 + k2).
  intros.
  
  destruct (c1 (w ++ v)) as [t2 c2 R2] eqn:D. destruct R2 as [k R2].
  assert(k <= k2). admit.
  assert (exists x y z, length x = k1 /\ length y = k /\
    length (y ++ z) = k2 /\ w = x ++ y ++ z). admit.
  destruct H1 as [x [y [z [L1 [L2 [L3 A]]]]]].
  split.
  - rewrite A. eapply R1 in L1. destruct L1. rewrite <- app_assoc in *. rewrite H1.
    admit.
  - assert( c1 (w ++ v) = c1 x).
    eapply R1 in L1. destruct L1. rewrite A. rewrite <- app_assoc in *. rewrite H2.
    reflexivity.
    pose proof L1.
    eapply R1 in L1. destruct L1. rewrite A.
    rewrite H3. rewrite H4. rewrite <- H1. rewrite D.
    eapply R1 in H2. destruct H2. rewrite <- app_assoc in *. erewrite H2.
    assert(c2 (y ++ z) = c2 y).
    apply R2. apply L2. rewrite H6. rewrite <- app_assoc. apply R2. apply L2.
Admitted.

Definition contract {X : Type} (pp : R (R X)) : R X.
  destruct pp as [t1 c1 R1].
  unfold isR in R1.
  apply constructive_indefinite_description in R1. destruct R1 as [k1 R1].
  remember (maximum (list_G_k k1) (getDependency c1)) as k2.
  apply (C X
     (fun s => match c1(s) with
      | C _ t2 c2 H => drop k2 (t1(s))
      end)
    (fun s => match c1(s) with
      | C _ t2 c2 H => c2(t1(s))
      end)). eapply helper. apply R1. apply Heqk2.
Defined.

Definition epsilon' {X : Type} (p : R (R (W X))) : R X.
  apply contract in p.
  destruct p  as [t1 c1].
  apply (C X t1
    (fun s => match c1 s with | (s, x) => x end)).
  unfold isR. destruct i as [k H].
  exists k. intros. split.
  - apply H; auto.
  - eapply H in H0. destruct H0. rewrite H1. reflexivity.
Defined.

Lemma prop1 {X} (p : R X) : R_fun delta (eta p) = R_fun eta p.
Proof.
  unfold delta. unfold eta. unfold R_fun.
  destruct p.
  apply proof_irrelevance_R.
  destruct p as [t c [k H]].
  unfold R_fun. unfold eta.
  apply proof_irrelevance_R.

Definition mu {X} (p : R (W (R (W X)))) : R (W X) := epsilon' (R_fun delta p).

Lemma helper2 {X : Type}
(t1 : list G -> list G)
(c1 : list G -> W (R (W X)))
(H1 : isR (W (R (W X))) (t1, c1)) :
isR (W X)
  (fun s1 : list G =>
   let (s2, r) := c1 s1 in match r with
                           | C _ t2 _ _ => t2 (s2 ++ t1 s1)
                           end,
  fun s1 : list G =>
  let (s2, r) := c1 s1 in
  match r with
  | C _ _ c2 _ => let (s3, x) := c2 (s2 ++ t1 s1) in (s2 ++ s3, x)
  end).
Admitted.

Definition mu' {X} (p1 : R (W (R (W X)))) : R (W X).
  destruct p1 as [t1 c1 H1].
  apply (C (W X)
    (fun s1 => 
      match c1 s1 with | (s2, (C _ t2 c2 H2)) =>
        t2(s2 ++ t1(s1))
      end)
    (fun s1 =>
      match c1 s1 with | (s2, (C _ t2 c2 H2)) =>
      match c2 (s2 ++ t1(s1)) with (s3 , x) => (s2 ++ s3, x) end end )).
apply helper2. apply H1.
Defined.

Import EqNotations.



Lemma mu_correct {X : Type} (p : R (W (R (W X)))): @mu X p= @mu' X p.
  destruct p.
  unfold mu'. unfold mu. unfold epsilon'.
  destruct (contract (R_fun delta (C (W (R (W X))) t c i))) eqn:D.
  inversion D.
  destruct (constructive_indefinite_description
          (fun k : nat =>
           forall w v : list G, length w = k -> t (w ++ v) = v /\ delta (c (w ++ v)) = delta (c w))
          match i with
          | ex_intro _ x H =>
              ex_intro
                (fun k : nat =>
                 forall w v : list G, length w = k -> t (w ++ v) = v /\ delta (c (w ++ v)) = delta (c w)) x
                (fun (w v : list G) (H0 : length w = x) =>
                 match H w v H0 with
                 | conj H1 H2 =>
                     conj H1 (eq_ind_r (fun x0 : W (R (W X)) => delta x0 = delta (c w)) eq_refl H2)
                 end)
          end).
  inversion H0. clear H0. apply fe; extensionality s.
  - rewrite <- H1. destruct (c s), r.
    destruct (delta (l, C (W X) t1 c1 i1)).
    
  destruct (contract (R_fun delta (C (W (R (W X))) t c i))) eqn:C.
  apply fe; extensionality s; destruct (c s) eqn:D.
  inversion C. destruct i. unfold delta in *. unfold R_fun in *. 
  - 

Definition kleisli {X Y} (p : X -> R (W Y)) (q : R (W X)) : R (W Y).
  apply mu. apply (R_fun (W_fun _ _ p)). apply q.
Defined.

Definition pop_push_one {X} (x : X) : R (W X).
  apply (C (W X)
    (fun s1 => drop 1 s1)
    (fun s1 => (take 1 s1, x))).
  exists 1. intros. destruct w; try destruct w; inversion H.
  split.
  - reflexivity.
  - reflexivity.
Defined.


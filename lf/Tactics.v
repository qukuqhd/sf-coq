From LF Require Export Poly.

(* Apply 策略使用 *)

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2.
  (* 这里 使用 apply 代替了 rewrite 和 reflexivity *)

Qed.
  
Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
    intros eq eq2 .
    apply eq. apply eq2.
Qed.
Theorem silly3_firsttry : forall (n : nat),
     true =  (Nat.eqb n  5) ->
     Nat.eqb (S (S n))  7 = true.
Proof.
  intros n H.
  (* apply 需要是精确的匹配所以不能直接使用apply *)
  symmetry.
  apply H.
Qed.



Theorem app_assoc : forall (X :Type) ( l1 l2 l3 : list X),
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
.
Proof.
intros X l1 l2 l3. induction l1 as [| n l1' IHl1'].
- (* l1 = nil *)
    simpl. reflexivity.
- (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'.
    reflexivity. Qed.
Lemma app_nil_r : forall (X : Type) (l : list X),
    l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h' t' Ihl'].
  - reflexivity.
  - simpl. rewrite Ihl'. reflexivity.
Qed.

Lemma rev_app : forall (X : Type) (l1 l2 : list X),
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros X l1 l2.
  induction l1 as [| h' t' Ihl'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite Ihl'. rewrite app_assoc. reflexivity.
Qed.
Lemma rev_involutive : forall (X : Type) (l : list X),
    rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h' t' Ihl'].
  - reflexivity.
  - simpl. rewrite rev_app. simpl. rewrite Ihl'. reflexivity.
Qed.

Lemma rev_injective : forall (X : Type) (l1 l2 : list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
    intros X l1 l2 H.
    
    assert (H_rev : rev (rev l1) = rev (rev l2)).
    { rewrite H. reflexivity. }
    
    rewrite rev_involutive in H_rev.
    rewrite rev_involutive in H_rev.
    rewrite H_rev.
    reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  (* 利用 rev 单射函数 *)
  apply rev_injective.
  rewrite <- H.
  symmetry.
  apply rev_involutive. 
Qed.

(* 使用Apply With *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

(* 提取 = 传递性 *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.


Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = ( o - 2) ->
     (n + p) = m ->
     (n + p) = ( o -2).
Proof.
  intros n m o p eq1 eq2 .
  apply trans_eq with (m := m). 
    - apply eq2. 
    - apply eq1. 
Qed.
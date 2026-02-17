(**
SF LF Induction
**)
From LF Require Import Basics.
Require Import Arith.
(* 利用归纳进行证明 *)

Theorem plus_n_0_firsttry: forall n:nat,
    n = n + 0.
Proof.
    intros n.
    induction  n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite <- Ihn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.

Proof.
    induction n as[|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m:nat,
    S (n + m ) = n + S m.
Proof.
    intros n m.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihn'. reflexivity.
Qed.

Theorem plus_comm: forall m n :nat,
    m + n = n + m.
Proof.
    intros m n.
    induction m as [|m' Ihm'].
    - simpl.
    (* 也可以直接使用n+0 = n 的定理 *)
    induction n as [|n' Ihn'].
        * simpl. reflexivity.
        * simpl. rewrite <- Ihn'. reflexivity.
    -  simpl. rewrite -> Ihm'.
        (* 使用前面的 plus_n_Sm *)
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.

Theorem plus_assoc : forall m n p :nat,
    m + (n + p) = ( m + n ) + p.
Proof.
    intros m n p.
    induction m as [|m' Ihm'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihm'. reflexivity.
Qed.

(* 定义double *)
Fixpoint double (n:nat):nat :=
    match n with
    | 0 => 0
    | S n' => S (S (double n'))
    end
.

Lemma double_plus: forall n ,
    double n = n + n.
Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihn'. simpl.
        (* 使用下 plus_n_Sm 把 S(n' + n') 改写为 n' + S n' *)
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.

Fixpoint evenb (n:nat):bool :=
    match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
    end
.

Definition oddb (n:nat):bool :=
    negb (evenb n)
.


Lemma evenb_minus_tow : forall n:nat,
    evenb (S (S n)) = evenb n
.

Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem evenb_S :forall n :nat,
    evenb (S n)= negb(evenb n).


Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - rewrite -> evenb_minus_tow. rewrite -> Ihn'. rewrite negb_involutive.
    simpl.
    reflexivity.
Qed.
(* 在证明里面定义证明 *)


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem nat_self_eq: forall n :nat,
  Nat.eqb n  n = true.

Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite Ihn'. reflexivity.
Qed.

Theorem plus_swap : forall n m p :nat,
    n + (m + p) = m + n + p.
Proof.
    intros n m p.
    (* 结合律去除括号 *)
    rewrite plus_assoc.
    (* 交换律 *)
    rewrite (plus_comm n m).
    reflexivity.
Qed.

Lemma mult_plus_one : forall m n :nat,
    m * S n = m + m * n
.
(* 对于加法和乘法 都是左规约所以要频繁 plus_swap  *)
Proof.
    intros m n.
    induction m as [|m' Ihm'].
    - simpl. reflexivity.
    - simpl. rewrite Ihm'. rewrite plus_swap. rewrite plus_swap. rewrite (plus_comm  m' n). reflexivity.
Qed.

Theorem mult_comm : forall m n :nat,
    m * n = n *m
.

Proof.
    intros m n.
    induction m as [|m' Ihm'].
    - simpl. rewrite mult_0_r. reflexivity.
    - simpl. rewrite  Ihm'. rewrite   mult_plus_one . reflexivity.
Qed.

Theorem leb_ref1: forall n:nat,
    Nat.leb n  n = true
.
Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite Ihn'. reflexivity.
Qed.


Theorem zero_nbeq_S : forall n :nat,
    Nat.eqb 0 (S n) = false
.
(* 这里直接化简说明 eqb 的实现是左规约的 *)
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem and_false_r :forall b:bool,
    andb b false = false
.

Proof.
    intros b.
    induction b as [].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
    Nat.leb n  m = true -> Nat.leb (p + n)  (p + m) = true.
Proof.
    intros n m p.
    intros H.
    induction p as [|p' Ihp'].
    - simpl. rewrite H. reflexivity.
    - simpl. rewrite Ihp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  Nat.eqb (S n)  0 = false.
Proof.
    simpl.
    reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
    intros n.
    simpl.
    rewrite plus_n_0_firsttry.
    reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
    intros b c.
    induction b as [].
    - simpl. induction c as [].
        * simpl. reflexivity.
        * simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem H_rearrange : forall a b c d : nat, 
    a + b + c + d = a + c + b + d
.
Proof.
    intros a b c d.
    rewrite <- (plus_assoc a b c). (* 变成 (a + (b + c)) + d *)
    rewrite (plus_comm b c).       (* 变成 (a + (c + b)) + d *)
    rewrite (plus_assoc a c b).
    reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p.
    induction p as [|p' Ihp'].
    - simpl. rewrite  <- mult_n_O . rewrite  <- mult_n_O . 
    rewrite  <- mult_n_O . simpl. reflexivity.
    - rewrite mult_plus_one. rewrite mult_plus_one.  
    rewrite mult_plus_one. rewrite Ihp'. rewrite plus_assoc. rewrite plus_assoc.
    rewrite H_rearrange.
    reflexivity.
Qed.

Theorem mult_assoc: forall n m p:nat ,
    n * (m * p) = ( n * m ) * p
.

Proof.
    intros n m p.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite Ihn'.
    (* 分配律化简 *)
    rewrite mult_plus_distr_r. reflexivity.
Qed.

(* replace 进行改写 *)

Theorem plus_swap' : forall n m p :nat,
    n + (m + p) = m + (n + p)
.

Proof.
    intros n m p.
    rewrite plus_assoc. rewrite plus_assoc.
    
    (* replace 把 n+m 改写为 m+n *)
    replace (n + m) with (m + n).
    - reflexivity.
    - (*  对于这里改写 n+m = m+n 进行证明 *)
        rewrite plus_comm.
        reflexivity.
Qed.


Fixpoint nat_to_bin(n:nat):bin :=
    match n with
    | 0 => Z
    | S n' => incr (nat_to_bin n')
    end
.



Lemma bin_to_nat_incr:forall b :bin,
    bin_to_nat (incr b ) = S (bin_to_nat b)
.
Proof.
        intros b.
    induction b as [|a' Iha'|b' Ihb'].
    - simpl.  reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite Ihb'. rewrite plus_n_Sm. rewrite plus_assoc.
    rewrite <- plus_n_0_firsttry with (n := S (bin_to_nat b') + S (bin_to_nat b')).
    rewrite <- plus_n_0_firsttry with (n := bin_to_nat b').
    simpl.
    reflexivity.
Qed.

Theorem nat_bin_nat : forall n,
bin_to_nat (nat_to_bin n) = n
.

Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite bin_to_nat_incr. rewrite Ihn'. reflexivity.
Qed.

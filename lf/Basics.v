(**
SF LF 模块 Basics内容
**)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* Compute 计算验证 *)

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

(* 示例 *)
Example test_next : (next_weekday (next_weekday saturday)) = tuesday.

(* 对示例进行证明 *)

Proof.
    simpl. (* 化简 *)
    reflexivity. (* 正反 *)
Qed.

(* 自己定义下 bool *)

Module MyBool.
    Inductive bool:Type :=
    | true
    | false
    .
    Definition negb (b:bool):bool :=
        match b with
            | true => false
            | false => true
        end
    .
    (* 左规约 *)
    Definition andb(b1 b2 :bool) :bool :=
        match  b1 with
            | true => b2
            | false => false
        end
    .
    Definition orb(b1 b2 :bool) :bool :=
        match b1 with
            | true => true
            | false => b2
        end
    .
    Example test_orb1: (orb true false) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb2: (orb false false) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_orb3: (orb false true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb4: (orb true true) = true.
    Proof. simpl. reflexivity. Qed.
    
    (* 定义bool 的符号和记法 *)
    Notation "x && y " := (andb x y).
    Notation "x || y" := (orb x y ).
    Example test_orb5: false || false || true = true.
    Proof. simpl. reflexivity. Qed.

    (* 使用if需要注意 then 是匹配到第一个构造 这里也是写左规约*)
    Definition negb'(b:bool) :bool :=
        if b then true
        else false
    .
    Definition andb'(b1 b2 :bool) :bool :=
        if b1 then b2
        else false
    .
    Definition orb'(b1 b2 :bool) :bool :=
        if b1 then true
        else b2
    .
    Definition nandb (b1:bool) (b2:bool) : bool :=
        negb (andb b1 b2)
    .
    Example test_nandb1: (nandb true false) = true.
        Proof. simpl. reflexivity. Qed.
    Example test_nandb2: (nandb false false) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_nandb3: (nandb false true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_nandb4: (nandb true true) = false.
    Proof. simpl. reflexivity. Qed.
    Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
        andb b1 (andb b2 b3).
    Example test_andb31: (andb3 true true true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_andb32: (andb3 false true true) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_andb33: (andb3 true false true) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_andb34: (andb3 true true false) = false.
    Proof. simpl. reflexivity. Qed.
    (* Check 获取类型 *)
    Check(true).
    (* 对于 negb来说它的类型是函数 *)
    Check(negb).

    (* 根据已经定义的类型来构造类型 *)
    Inductive rgb :Type :=
        |red
        |green
        |blue.
    Inductive color :Type :=
        |black
        |white
        |primary (p:rgb ). (* 除了黑白以外的由rgb来构造 *)
    
    (* 对于这里的primary 进行匹配 应该是 primary p  *)
    Definition monochrome (c:color):bool :=
        match c with
        |primary p => false
        | _ => true
        end
    .
    Definition is_red(c:color):bool :=
        match c with
        | primary red => true
        | _ => false
        end
    .
    Inductive bit :Type :=
    | t
    | f
    .
    (* 四元bits *)
    Inductive nybble :Type :=
    | bits(b1 b2 b3 b4 :bit)
    .
    Definition is_all_zero (nb:nybble) :bool :=
        match nb with
        | bits f f f f => true
        | _ => false
        end
    .
    (* 对于自然数进行定义 *)
    Inductive nat :Type :=
    |zero
    |S (n:nat)
    .
    Definition pred (n:nat) :nat :=
        match n with
        | zero => zero
        | S n' => n'
        end
    .
    (* 减二 *)
    Definition minus_tow(n :nat):nat :=
        match n with
        | zero => zero
        | S zero => zero
        | S (S n') => n'
        end
    .
    (* 是否为偶数 *)
    Fixpoint evenb(n:nat):bool :=
        match n with
        | zero => true
        | S zero => false
        | S (S n') => evenb n'
        end
    .

    Definition oddb(n:nat):bool :=
        negb (evenb n)
    .

    Fixpoint plus(m n:nat):nat :=
        match m with
        |zero => n
        |S m' => S (plus m' n)
        end
    .
    Fixpoint mult(m n:nat):nat :=
        match m with
        | zero => zero
        | S m' => plus n (mult m' n)
        end
    .
    Fixpoint factorial (n:nat) : nat :=
        match n with
        | zero => S zero
        | S zero => S zero
        | S n' => mult n'  (factorial n')
        end
    .
    Fixpoint minus(m n:nat):nat :=
        match m ,n with
        | _,zero => m
        | zero,_ => zero
        | S m',S n' => minus m' n'
        end
    .
    Fixpoint exp(base power: nat) :nat :=
        match power with
        | zero => S zero
        | S p' => mult base (exp base p')
        end
    .
    Fixpoint eqb(m n :nat):bool :=
        match m , n with
        | zero,zero => true
        | _ ,zero => false
        | zero,_ => false
        | S m',S n' => eqb m' n'
        end
    .
    Fixpoint  leb(m n :nat):bool :=
        match m , n with
        | _,zero => false
        | zero,_ => true
        | S m',S n' => leb m' n'
        end
    .
    Fixpoint  ltb(m n :nat):bool :=
        match m , n with
        | _,zero => false
        | zero,_ => true
        | S m',S n' => ltb m' n'
        end
    .
End MyBool.




Theorem plus_0_n : forall n :nat , 0 + n = n.

Proof.
    simpl.
    reflexivity.
Qed.

Theorem plus_1_n: forall n:nat , 1 + n = S n.
Proof.
    simpl.
    reflexivity.
Qed.
Theorem mult_0_n: forall n:nat , 0 * n =  0.
Proof.
    simpl.
    reflexivity.
Qed.

Theorem plus_id_example : forall m n :nat ,
    n = m -> n + n = m + m
.

Proof.
    intros m n H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
    intros m n o.
    intros H1 H2.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
Qed.
Theorem mult_n_0_m_0 : forall m n :nat,
    (n * 0) + (m *0) = 0
.
Proof.
    intros n m.
    rewrite <- (mult_n_O m).
    rewrite <- (mult_n_O n).
    simpl.
    reflexivity.
Qed.

Theorem mult_n_1 : forall n :nat,
    n * 1 = n.
Proof.
    intros n.
    induction n as [|n' Ihn'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihn'. reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (Nat.eqb (n + 1)  0) = false.

Proof.
    intros n.
    destruct n as [|n'] eqn:E.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
Theorem plus_1_neq_0 : forall n : nat,
  (Nat.eqb (n + 1)  0) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros b c.
    intros H.
    destruct b eqn:E.
    - rewrite <- H.
        simpl.
        reflexivity.
    - rewrite <- H.
        discriminate H.
Qed.

Theorem zero_nbeq_plus_1 : forall n: nat,
    (Nat.eqb 0 (n + 1)) = false.
Proof.
    intros n.
    destruct n as [|n'] eqn:H.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
    intros b c.
    intros H.
    destruct b .
    - destruct c.
        * simpl. reflexivity.
        * discriminate.
    - destruct c.
        * discriminate.
        * simpl. reflexivity.
Qed.

(* 定义二进制数 *)
Inductive bin:Type :=
| Z
| A (n:bin)
| B (n:bin)
.
Fixpoint incr (m:bin) : bin :=
    match m with
    | Z => B Z
    | A m' => B m'
    | B m' => A (incr m')
    end
.
Fixpoint bin_to_nat (m:bin) : nat :=
    match m with
    | Z => 0
    | A m' => 2 * (bin_to_nat m')
    | B m' => S (2 * (bin_to_nat m'))
    end
.

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof.
    simpl.
    reflexivity.
Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof.
    simpl.
    reflexivity.
Qed.
Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof.
    simpl.
    reflexivity.
Qed.
Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof.
    simpl.
    reflexivity.
Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof.
    simpl.
    reflexivity.
Qed.
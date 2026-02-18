From LF Require Export Lists.

(* 多态 *)

(* 
对于Lists 里面定义的列表 h 必须是nat 如果其他的类型就要
重新定义了我们可以使用多态归纳类型来对列表进行定义
 *)

Inductive list(X:Type) :Type :=
    |nil
    |Cons(x:X) (l:list X)
.

(* 对于类型 list 可以理解为本身是 类型的函数 Type -> Type  *)
Check list.

(* 对于 list 来说 X 是一个类型的参数 它需要传入 *)

Check (nil nat).

Check (Cons nat 1 (nil nat)).

(* 具体 nil 构造子 是 forall X:Type , list X   *)
Check nil.

(* Cons 构造子是 forall X:Type, X -> list X -> list X  *)
Check Cons.

(* 和原来的 repeat 相比就要指定列表元素类型 *)
Fixpoint repeat(X:Type)(x:X)(count:nat):list X :=
    match count with
    | 0 => nil X
    | S n' => Cons X x (repeat X x n')
    end
.
Example test_repeat1 :
  repeat nat 4 2 = Cons nat 4 (Cons nat 4 (nil nat)).
Proof. simpl. reflexivity. Qed.


Example test_repeat2 :
  repeat bool false 1 = Cons bool false (nil bool).
Proof. simpl. reflexivity. Qed.
Module MumbleGrumble.
    Inductive mumble : Type :=
    | a
    | b (x : mumble) (y : nat)
    | c.
    Inductive grumble (X:Type) : Type :=
    | d (m : mumble)
    | e (x : X).
    (* Check (d  (b a 5)). *)
    Check (d mumble (b a 5)).
    Check (d bool (b a 5)).
    Check (e bool true).
    Check (e mumble (b c 0)).
    (* Check (e bool (b c 0)). *)
    Check (c).
End MumbleGrumble.

Arguments nil {X}.
Arguments Cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := Cons 1 (Cons 2 (Cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => Cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | Cons h t => Cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | Cons h t => app (rev t) (Cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | Cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (Cons 1 (Cons 2 nil)) = (Cons 2 (Cons 1 nil)).

Proof. simpl. reflexivity. Qed.

Example test_rev2:
  rev (Cons true nil) = Cons true nil.
Proof. simpl. reflexivity. Qed.

Example test_length1: length (Cons 1 (Cons 2 (Cons 3 nil))) = 3.
Proof. simpl. reflexivity. Qed.

(* 对nil 没有指定类型的错误 进行定义*)
Fail Definition mynil := nil.

Definition mynil : list nat := nil.
Check @nil .
Definition mynil' := @nil nat.

Notation "x :: y" := (Cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (Cons x .. (Cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| h' t' Ihl'].
  - simpl.  reflexivity.
  - simpl. rewrite Ihl'. reflexivity. 

Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [|h' t' Ihl'].
  - simpl. reflexivity.
  - simpl. rewrite Ihl'. reflexivity.
Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| h' t' Ihl'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite Ihl'. rewrite app_assoc. reflexivity.
Qed. 
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h' t' Ihl'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite Ihl'. reflexivity.
Qed.

Module MyProd.
Inductive prod (X Y:Type) :Type :=
| pair (x:X) (y:Y)
.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

(* 积类型 *)
Notation " X * Y " := (prod X Y) : type_scope.


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end
.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end
.


Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end
.
Check (combine).
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
    | nil => (nil , nil )
    | h::t => let (l1,l2) := split t in
      (fst h ::l1 , snd h :: l2)
  end
.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

End MyProd.

Module OptionPlayground.

Inductive option (X:Type) :Type :=
| Some (x:X)
| None
.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if (Nat.eqb n  O) then Some a else nth_error l' (pred n)
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | nil => None
    | h::t => Some h
  end
.

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Qed.


End  OptionPlayground.

(* 高阶函数 *)

Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Check @doit3times: forall X : Type, (X -> X) -> X -> X.

Fixpoint filter {X:Type} (f : X -> bool) (l :list X):(list X) := 
  match l with
  | [] => []
  | h :: t => if (f h) then h::(filter f t) 
      else filter f t
  end
.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  Nat.eqb (length l)  1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. simpl. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. simpl. reflexivity. Qed.

Example test_filter2':
    filter (fun l => Nat.eqb (length l)  1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.
Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (fun item =>  andb (Nat.leb  7 item) (evenb item)) l
.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].

Proof. simpl. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. simpl. reflexivity. Qed.


Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  ((filter test l) ,(filter (fun item => negb (test item)) l))
.


Fixpoint partition' {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  match l with
  | [] => ([],[])
  | h::t => let (t1,t2) := partition' test t
      in if (test h) then (h::t1,t2) else (t1,h::t2)
  end
.
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).

Proof. simpl. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).

Proof. simpl. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity. Qed.


Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. simpl. reflexivity. Qed.
Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. simpl. reflexivity. Qed.

Lemma map_f_app_list : forall (X Y : Type) (f : X -> Y) (l1 l2:list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2) 
.
Proof.
  intros X Y f l1 l2.
  induction l1 as [|h' t' Ihl'].
  - simpl. reflexivity.
  - simpl. rewrite Ihl'. reflexivity.

Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros  X Y f l.
  induction l as [|h' t' Ihl'].
  - simpl. reflexivity.
  - simpl. rewrite map_f_app_list. simpl. rewrite Ihl'.
    reflexivity.
Qed.
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
  match l with
  | [] => []
  | h::t => (f h) ++  (flat_map f t)
  end
.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. simpl. reflexivity. Qed.


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end
.

(* 和之前都是左规约 这里是左折叠 *)
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end
.
Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. simpl. reflexivity. Qed.
Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. simpl. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].

Proof. simpl. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. simpl. reflexivity. Qed.


Example constfun_example2 : (constfun 5) 99 = 5.
Proof. simpl. reflexivity. Qed.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7.
Proof. simpl. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. simpl. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. simpl. reflexivity. Qed.

Module Exercises.
  Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
  Example test_fold_length1 : fold_length [4;7;0] = 3.
  Proof. simpl. reflexivity. Qed.
  Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
  Proof.
    intros X l .
    induction l as [| h' t' Ihl'].
    - simpl. reflexivity.
    - simpl. rewrite <- Ihl'.  reflexivity.
  Qed.

  Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
    fold (fun item l => (f item)::l) l [] 
  .
  Theorem fold_map_correct : forall (X Y : Type) (f:X->Y) (l : list X) ,
    fold_map f l = map f l
  .
  Proof.
    intros X Y f l.
    induction l as [|h' t' Ihl'].
    - simpl. reflexivity.
    - simpl. rewrite <- Ihl'. reflexivity.
  Qed.

  Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

  Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
    let (x,y) := p in
      f x y
  .
  Theorem uncurry_curry : forall (X Y Z : Type) (f : X * Y -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros X Y Z f p.
    induction p as [].
    - simpl. reflexivity.
  Qed.

  Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
  Proof. simpl. reflexivity. Qed.

    Check @prod_uncurry.
  Theorem curry_uncurry : forall (X Y Z : Type)
                          (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p
  .
  
  Proof.
  intros X Y Z f p.
  induction p as [].
  - simpl. reflexivity. 
  Qed.

  Module Church.
    Definition cnat := forall X : Type, (X -> X) -> X -> X.
    Definition one : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f x.

    Definition two : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f (f x).

    Definition zero : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => x.

    Definition three : cnat := @doit3times.
    
    Definition succ (n : cnat) : cnat:=
      fun (X : Type) (f : X -> X) (x : X) => f (n X f x)
    .

    Example succ_1 : succ zero = one.
    Proof. simpl. reflexivity. Qed.
    Example succ_2 : succ one = two.
    Proof. simpl. reflexivity. Qed.
    Example succ_3 : succ two = three.
    Proof. simpl. reflexivity. Qed.

    Definition plus (n m : cnat) : cnat :=
    fun (X : Type) (f : X -> X) (x : X) =>  (n X f  (m X f x))
    .

    Example plus_1 : plus zero one = one.
    Proof. simpl. reflexivity. Qed.
    Example plus_2 : plus two three = plus three two.
    Proof. simpl. reflexivity. Qed.
    Example plus_3 :
      plus (plus two two) three = plus one (plus three three).
    Proof. simpl. reflexivity. Qed.

    Definition mult (n m : cnat) : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.

    Example mult_1 : mult one one = one.
    Proof. simpl. reflexivity. Qed.
    Example mult_2 : mult zero (plus three three) = zero.
    Proof. simpl. reflexivity. Qed.
    Example mult_3 : mult two three = plus three three.
    Proof. simpl. reflexivity. Qed.

    Definition exp (n m : cnat) : cnat :=
    fun (X : Type) => m (X -> X) (n X)
    .
    Example exp_1 : exp two two = plus two two.
    Proof. simpl. reflexivity. Qed.
    Example exp_2 : exp three zero = one.
    Proof. simpl. reflexivity. Qed.
    Example exp_3 : exp three two = plus (mult two (mult two two)) one.
    Proof. simpl. reflexivity. Qed.
  End Church.
  
End Exercises.


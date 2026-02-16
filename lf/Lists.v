From LF Require Export Induction.
Module NatList.
    Inductive natprod:Type :=
        |pair (n1 n2 :nat)
        .
    Check(pair 1 2).
    Definition fst(p:natprod):nat :=
        match p with
        | pair n1 n2 => n1
        end
    .
    Definition snd(p:natprod):nat :=
        match p with
        | pair n1 n2 => n2
        end
    .
    Compute(snd (pair 1 2)).
    Notation "( x , y )" := (pair x y).
    Definition swap_pair(p:natprod):natprod :=
        match p with
        | (x,y)=> (y,x)
        end
    .

    Theorem surjective_pairing' : forall n m :nat,
        (n,m) = (fst (n,m),snd (n,m))
    .
    Proof.
        simpl.
        reflexivity.
    Qed.
    
    Theorem snd_fst_is_swap: forall p:natprod,
        (snd p, fst p) = swap_pair p
    .
    Proof.
        intros p.
        induction p as [].
        - simpl. reflexivity.
    Qed.
    Theorem fst_swap_is_snd : forall (p : natprod),
        fst (swap_pair p) = snd p.
    Proof.
        intros p.
        induction p as [].
        - simpl. reflexivity.
    Qed.
    
    (* 定义nat列表 *)
    Inductive natList:Type :=
    | nil (*空*)
    | cons(n:nat) (l:natList)
    .

    Notation " x :: l " := (cons x l).
    Notation "[ ]" := nil.
    Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
    
    Fixpoint repeat(n count:nat):natList :=
        match count with
        | 0 => []
        | S count' => n :: (repeat n count')
        end
    .
    Fixpoint length (l:natList):nat :=
        match l with
        | nil => 0
        | h :: t => S (length t)
        end
    .
    Fixpoint app(l1 l2 :natList):natList :=
        match l1 with
        | nil => l2
        | h :: t => h::(app t l2)
        end
    .
    Notation "x ++ y" := (app x y).
    Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
    Proof. reflexivity. Qed.
    Example test_app2: nil ++ [4;5] = [4;5].
    Proof. reflexivity. Qed.
    Example test_app3: [1;2;3] ++ nil = [1;2;3].
    Proof. reflexivity. Qed.
    
    Definition hd (default:nat)(l:natList):nat :=
        match l with
        | nil => default
        | h::t => h
        end
    .
    Definition tl(l:natList):natList :=
        match l with
        | nil => nil
        | _::t => t
        end
    .
    Example test_hd1: hd 0 [1;2;3] = 1.
    Proof. reflexivity. Qed.
    Example test_hd2: hd 0 [] = 0.
    Proof. reflexivity. Qed.
    Example test_tl: tl [1;2;3] = [2;3].
    Proof. reflexivity. Qed.
    Fixpoint nonzeros (l:natList) : natList :=
        match  l with
        | nil => nil
        | 0 :: t => nonzeros t
        | h :: t => h :: (nonzeros t)
        end
    .
    Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
    Proof. simpl. reflexivity. Qed.
    Fixpoint oddmembers (l:natList) : natList:=
        match  l with
        | nil => nil
        | h :: t => if (evenb h) then (oddmembers t) else h :: (oddmembers t)
        end
    .
    Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
    Proof. simpl. reflexivity. Qed.
    Definition countoddmembers (l:natList) : nat :=
        length (oddmembers l)
    .
    Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
    Proof. simpl. reflexivity. Qed.
    Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
    Proof. simpl. reflexivity. Qed.
    Example test_countoddmembers3:
    countoddmembers nil = 0.
    Proof. simpl. reflexivity. Qed.
    Fixpoint alternate (l1 l2 : natList) : natList :=
        match l1 with
        | nil => l2
        | h1::t1 => match l2 with
            | nil => l1
            | h2 :: t2 => h1 ::(h2::(alternate t1 t2))
            end
        end
    .
    Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
    Proof. simpl. reflexivity. Qed.
    Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
    Proof. simpl. reflexivity. Qed.
    Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
    Proof. simpl. reflexivity. Qed.
    Example test_alternate4:
    alternate [] [20;30] = [20;30].
    Proof. simpl. reflexivity. Qed.

    Definition bag := natList.
    
End NatList.

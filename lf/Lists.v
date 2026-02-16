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
    Fixpoint count(v:nat)(s:bag):nat:=
        match s with
        | nil => 0
        | h::t=> if ( Nat.eqb h v) 
                    then S (count v t)
                    else (count v t)
        end
    .
    Example test_count1: count 1 [1;2;3;1;4;1] = 3.
    Proof. simpl. reflexivity. Qed.
    Example test_count2: count 6 [1;2;3;1;4;1] = 0.
    Proof. simpl. reflexivity. Qed.
    Definition sum(b1 b2:bag):bag :=
        b1 ++ b2
    .

    Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
    Proof. simpl. reflexivity. Qed.
    Definition add (v:nat) (s:bag) : bag :=
        [v] ++  s
    .
    Example test_add1: count 1 (add 1 [1;4;1]) = 3.
    Proof. simpl. reflexivity. Qed.
    Example test_add2: count 5 (add 1 [1;4;1]) = 0.
    Proof. simpl. reflexivity. Qed.
    Definition member (v:nat) (s:bag) : bool :=
       negb  (Nat.eqb (count v s) 0) 
    .
    Example test_member1: member 1 [1;4;1] = true.
    Proof. simpl. reflexivity. Qed.
    Example test_member2: member 2 [1;4;1] = false.
    Proof. simpl. reflexivity. Qed.
    Fixpoint remove_one (v:nat) (s:bag) : bag :=
        match s with
        | nil => nil
        | h::t => if (Nat.eqb h v) then t
                else h::(remove_one v t)
        end
    .
    Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
    Proof. simpl. reflexivity. Qed.
    Fixpoint remove_all (v:nat) (s:bag) : bag :=
        match s with
        | nil => nil
        | h::t => if (Nat.eqb h v) then (remove_all v t)
                else h::(remove_all v t)
        end
    .
    Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
    Proof. simpl. reflexivity. Qed.
    Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
    Proof. simpl. reflexivity. Qed.
    Fixpoint subset (s1:bag) (s2:bag) : bool :=
        match s1 with
        | nil => true
        | h::t => if (member h s2) then
            (subset t (remove_one h  s2)) 
            else false
        end
    .
    Example test_subset1: subset [1;2] [2;1;4;1] = true.
    Proof. simpl. reflexivity. Qed.
    Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
    Proof. simpl. reflexivity. Qed.
    Theorem nil_app : forall l:natList,
        [] ++ l = l
    .
    Proof. simpl. reflexivity. Qed.

    Theorem tl_length_pred : forall l:natList,
    pred (length l) = length (tl l)
    .
    Proof.
        intro l.
        destruct l as [] eqn:E.
        - simpl. reflexivity.
        - simpl. reflexivity. 
    Qed.
    Theorem app_assoc : forall l1 l2 l3 : natList,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
    .
    Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - (* l1 = nil *)
        simpl. reflexivity.
    - (* l1 = cons n l1' *)
        simpl. rewrite -> IHl1'. reflexivity. Qed.
    Fixpoint rev(l:natList):natList :=
        match l with
        | nil => l
        | h::t => (rev t) ++ [h]
        end
    .
    Example test_rev1: rev [1;2;3] = [3;2;1].
    Proof. reflexivity. Qed.
    Example test_rev2: rev nil = nil.
    Proof. reflexivity. Qed.
    Theorem app_length: forall l1 l2 : natList ,
        (length l1) + (length l2) = length (l1 ++ l2)
    .
    Proof.
        intros l1 l2.
        induction l1 as [| h' t' Ihh'].
        - simpl. reflexivity.
        - simpl. rewrite Ihh'. reflexivity.
    Qed.
    Theorem rev_length_firsttry : forall l:natList,
        length (rev l) = length l
    .
    Proof.
        intros l.
        (* 这里结构归纳 对于 cos 是 cos (h:nat ) (l:natList) 所以这里是 n l' *)
        induction l as [| n l' Ihl'].
        - simpl. reflexivity.
        - simpl. rewrite <- app_length. simpl.
            rewrite Ihl'. rewrite plus_comm. simpl.
            reflexivity.
    Qed.
    Theorem app_nil_r : forall l : natList,
        l ++ [] = l
    .
    Proof.
        intro l.
        induction l as [| h t Iht].
        - simpl. reflexivity.
        - simpl. rewrite Iht. reflexivity.
    Qed.
    Theorem rev_app : forall l1 l2 :natList,
        rev (l1 ++ l2) = (rev l2) ++ (rev l1)
    .
    Proof.
        intros l1 l2.
        induction l1 as [|h' t' Ih'].
        - simpl. rewrite app_nil_r. reflexivity.
        - simpl. rewrite Ih'. rewrite app_assoc.
            reflexivity.
    Qed.
    Theorem rev_involutive : forall l : natList,
      rev (rev l) = l
    .
    Proof.
        intro l.
        induction l as [| h' t' Ih'].
        - simpl. reflexivity.
        - simpl. rewrite rev_app. rewrite Ih'. simpl. 
            reflexivity.
    Qed.

    Theorem app_assoc4 : forall l1 l2 l3 l4 : natList,
        l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
    .
    Proof.
        intros l1 l2 l3 l4.
        rewrite app_assoc. 
        rewrite app_assoc.
        reflexivity.
    Qed.
    Lemma nonzeros_app : forall l1 l2 : natList,
        nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
    .
    Proof.
        intros l1 l2.
        induction l1 as [| h' t' Ih].
        - simpl. reflexivity.
        - induction h' as [| n' Ihn'].
            * simpl. rewrite Ih. reflexivity.
            * simpl. rewrite Ih. reflexivity.
    Qed.
    Fixpoint eqblist (l1 l2 : natList) : bool := 
        match l1 with
        | nil => match l2 with
            | nil => true
            | _ => false
            end
        | h1::t1 => match l2 with
            | nil => false
            | h2::t2 => if (Nat.eqb h1 h2)
                then (eqblist t1 t2)
                else false
            end
        end
    .
    Example test_eqblist1 :
    (eqblist nil nil = true).
        Proof. simpl. reflexivity. Qed.
    Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
        Proof. simpl. reflexivity. Qed.
    Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
        Proof. simpl. reflexivity. Qed.
    Lemma nat_eq_refl: forall n ,
        Nat.eqb n n = true
    .
    Proof.
        intros n.
        induction n as [|n' Ihn'].
        - simpl. reflexivity.
        - simpl. rewrite Ihn'. reflexivity.
    Qed.
    Theorem eqblist_refl : forall l:natList,
        true = eqblist l l
    .
    Proof.
        intro l.
        induction l as [| h' t' Ih].
        - simpl. reflexivity.
        - induction h' as [|n' Ihn'].
            * simpl. rewrite Ih. reflexivity.
            * simpl. rewrite nat_eq_refl.  rewrite Ih.
                reflexivity.
    Qed.
    Theorem count_member_nonzero : forall (s : bag),
        Nat.leb 1  (count 1 (1 :: s)) = true
    .
    Proof.
        intros s.
        reflexivity.
    Qed.
    Theorem leb_n_Sn : forall n,
        Nat.leb n  (S n) = true
        .
    Proof.
    intros n. induction n as [| n' IHn'].
    - (* 0 *)
        simpl. reflexivity.
    - (* S n' *)
        simpl. rewrite IHn'. reflexivity. 
    Qed.
    Theorem remove_does_not_increase_count: forall (s : bag),
        Nat.leb (count 0 (remove_one 0 s))  (count 0 s) = true
    .
    Proof.
        intros s.
        induction s as [| h' t' Ih'].
        - simpl. reflexivity.
        - induction h' as [|n' Ihn'].
            * simpl. rewrite leb_n_Sn. reflexivity.
            * simpl. rewrite Ih'. reflexivity.
    Qed.
    (* 证明 rev 为单射 函数 *)
    Theorem rev_injective : forall (l1 l2 : natList),
        rev l1 = rev l2 -> l1 = l2
    . 
    Proof.
        intros l1 l2 H.
        (* 在 rev l1 = rev l2 的条件下 rev (rev l1) = l2 *)
        assert (H_rev : rev (rev l1) = rev (rev l2)).
            { rewrite H. reflexivity. }
        rewrite  rev_involutive in H_rev.
        rewrite  rev_involutive in H_rev.
        rewrite H_rev.
        reflexivity.
    Qed.

    Inductive natOption :Type :=
    |Some(n:nat)
    |None
    .

    Fixpoint nth_error (l:natList) (n:nat) : natOption :=
    match l with
    | nil => None
    | a :: l' => match n with
                | O => Some a
                | S n' => nth_error l' n'
                end
    end.
    Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
    Proof. simpl. reflexivity. Qed.
    Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
    Proof. simpl. reflexivity. Qed.
    Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
    Proof. simpl. reflexivity. Qed.
    Inductive id : Type :=
      | Id (n : nat)
    .

    Definition eqb_id (x1 x2 : id) :=
        match x1, x2 with
        | Id n1, Id n2 => Nat.eqb n1   n2
        end
    .
    Theorem eqb_id_refl : forall x, 
        true = eqb_id x x
    .
    Proof.
        intros x.
        induction x as [].
        - induction n as [|n' Ihn'].
         * simpl. reflexivity.
         * simpl. rewrite nat_eq_refl. reflexivity.
    Qed.


End NatList.

Module PartialMap.
Export NatList.
    Inductive partial_map : Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).
    Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
          record x value d
    .
    Fixpoint find (x : id) (d : partial_map) : natOption :=
        match d with
        | empty => None
        | record y v d' => if eqb_id x y
                            then Some v
                            else find x d'
        end
    .


    Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
        find x (update d x v) = Some v
    .
    Proof.
        intros d x v.
        simpl.
        rewrite <- eqb_id_refl.
        reflexivity.
    Qed.
    Theorem update_neq : forall (d : partial_map) (x y : id) (o: nat),
        eqb_id x y = false -> find x (update d y o) = find x d
    .
    Proof.
        intros d x y o.
        intros H.
        simpl.
        rewrite H.
        reflexivity.
    Qed.
    Inductive baz : Type :=
        | Baz1 (x : baz)
        | Baz2 (y : baz) (b : bool)
    .
End PartialMap.
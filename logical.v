Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import PeanoNat.
Import ListNotations.
Open Scope list_scope.


Instance optionMonad : Monad option :=
  {
    ret T x := Some x;
    bind T U m f :=
      match m with
        | Some x => f x
        | None => None
      end;

  }.


(* Return the nth item from the list if it exists *)
Fixpoint nth {X : Type} (lst : list X) (n : nat) : option X :=
  match lst with
    | [] => None
    | (x :: xs) =>
        match n with
          | 0 => Some x
          | S n' => nth xs n'
        end
  end.

Definition tuple := list nat.
(* This is a database table *)
Record relation : Type :=
  {
    data : list tuple; (* Rows in the table *)
    order : nat; (* number of columns in each row *)
  }.


Example r_ex :=
  {| data := [[1;1];[1]]; order := 3 |}.

Example good_r :=
  {| data := [[1;1;1]]; order := 3 |}.


Definition coherent_relation (r : relation) : Prop :=
  forall (t : tuple),
    In t (data r) ->
    length t = (order r).


Definition coherent_relations (r1 r2 : relation) : Prop :=
  coherent_relation r1 /\ coherent_relation r2 /\ order r1 = order r2.

Definition boolean := bool.
Definition relname : Type := nat.
Definition predicate := tuple -> boolean.
Definition select : Type := nat.
Definition database := list relation.

Definition get_relation (db : database) (n : relname) : option relation :=
  nth db n.


Definition schema := list nat.
Definition coherent_database (db : database) : Prop :=
  forall r,
    In r db ->
    coherent_relation r.
Definition compliant_relation (r : relation) (o : nat) : Prop :=
  coherent_relation r /\ order r = o.
Definition compliant_database (db : database) (s : schema) : Prop :=
  forall relname (o : nat),
    nth s relname = Some o ->
    exists (r : relation),
      get_relation db relname = Some r /\ compliant_relation r o.


Lemma one_relation_per_name : forall (db : database) (name : relname) (r1 r2 : relation),
    get_relation db name = Some r1 ->
    get_relation db name = Some r2 ->
    r1 = r2.
Proof.
  intros.
  rewrite H0 in H.
  injection H.
  auto.
Qed.



Example ex_r1 : relation :=
  {| data := [[1;1;1];[1;1;1]]; order := 3; |}.

Example ex_r2 : relation :=
  {| data := [[2;2]; [2;2]]; order := 2 |}.

Example ex_db : database := [ex_r1; ex_r2].

Example ex_schema : schema := [3; 2].

(* TODO make proving compliance easeir *)
Example ex_compiant : compliant_database ex_db ex_schema.
Proof.
  simpl.
  unfold compliant_database.
  intros.
  simpl in H.
  destruct relname0.
  - inversion H.
    subst.
    exists ex_r1.
    split.
    + unfold get_relation.
      simpl.
      reflexivity.
    + unfold compliant_relation.
      split.
      * unfold coherent_relation.
        intros.
        inversion H0.
        rewrite <- H1.
        auto.
        inversion H1.
        rewrite <- H2.
        auto.
        inversion H2.
      * auto.
  - destruct relname0.
    + inversion H.
      subst.
      exists ex_r2.
      split.
      auto.
      unfold compliant_relation.
      unfold coherent_relation.
      split.
      intros.
      inversion H0.
      rewrite <- H1.
      auto.
      inversion H1.
      rewrite <- H2.
      auto.
      inversion H2.
      auto.
    + simpl.
      discriminate H.
Qed.

Inductive quantifier : Type :=
  | Forall
  | Exists.

Inductive set_op : Type :=
  | Union
  | Intersection.

Inductive and_or : Type :=
  | And
  | Or.




Inductive query : Type :=
  | Q_Table : relname -> query
  | Q_Set :
    set_op -> query -> query -> query
  | Q_Join : query -> query -> query
  | Q_Pi : list select -> query -> query
  | Q_Sigma : formula -> query -> query
  (* | Q_Gammma : *)
  (*   list term -> formula -> list select -> query -> query *)
with formula : Type :=
  | Q_Conj :
    and_or -> formula -> formula -> formula
  | Q_Not : formula -> formula
  | Q_Atom : atom -> formula

with atom : Type :=
  | Q_True
  | Q_Pred : predicate -> list tuple -> atom
  | Q_Quant :
    quantifier -> predicate -> list tuple ->
    query -> atom
  | Q_In : list select -> query -> atom
  | Q_Exists : query -> atom.


Inductive has_query_order : schema -> query -> nat -> Prop :=
  | Order_Table : forall sch n o,
      nth sch n = Some o ->
      has_query_order sch (Q_Table n) o
  | Order_Set : forall sch q1 q2 op o,
      has_query_order sch q1 o ->
      has_query_order sch q2 o ->
      has_query_order sch (Q_Set op q1 q2) o
  | Order_Join : forall sch q1 q2 o1 o2 o,
      has_query_order sch q1 o1 ->
      has_query_order sch q2 o2 ->
      o = o1 + o2 ->
      has_query_order sch (Q_Join q1 q2) o.




Fixpoint query_order (sch : schema) (q : query) : option nat :=
    match q with
      | Q_Table name => nth sch name
      | Q_Set o q1 q2 =>
        o1 <- query_order sch q1;;
        o2 <- query_order sch q2;;
        if o1 =? o2 then
          Some (o1)
        else
          None
      | Q_Join q1 q2 =>
          o1 <- query_order sch q1;;
          o2 <- query_order sch q2;;
          Some (o1 + o2)
      | _ => None
    end.

Theorem has_query_equiv : forall q sch n,
    has_query_order sch q n <-> query_order sch q = Some n.
Proof.
  intros q.
  induction q.
  - intros.
    split.
    + intros.
      simpl.
      inversion H.
      subst.
      auto.
    + intros.
      simpl in H.
      apply Order_Table.
      auto.
  - intros.
    split.
    + intros.
      simpl.
      inversion H.
      subst.
      apply IHq1 in H5.
      rewrite H5.
      apply IHq2 in H6.
      rewrite H6.
      rewrite Nat.eqb_refl.
      reflexivity.
    + intros.
      simpl in H.
      destruct (query_order sch q1) eqn:Hq1;
        destruct (query_order sch q2) eqn:Hq2;
        try discriminate.
      destruct (n0 =? n1) eqn:Heq; try discriminate.
      injection H.
      intros.
      apply Order_Set.
      apply IHq1 in Hq1.
      rewrite H0 in Hq1.
      apply Hq1.
      apply IHq2 in Hq2.
      apply Nat.eqb_eq in Heq.
      rewrite <- Heq in Hq2.
      rewrite H0 in Hq2.
      apply Hq2.
  - intros.
    split.
    + intros.
      inversion H.
      subst.
      simpl.
      apply IHq1 in H2.
      rewrite H2.
      apply IHq2 in H4.
      rewrite H4.
      reflexivity.
    + intros.
      simpl in H.
      destruct (query_order sch q1) eqn:Hq1;
        destruct (query_order sch q2) eqn:Hq2;
        try discriminate.
      injection H.
      intros.
      apply Order_Join with (o1 := n0) (o2 := n1).
      apply IHq1 in Hq1.
      apply Hq1.
      apply IHq2 in Hq2.
      apply Hq2.
      auto.
  - split.
    + intros.
      inversion H.
    + intros.
      discriminate.
  - split.
    + intros.
      inversion H.
    + intros.
      discriminate.
Qed.

Fixpoint all_same_lengths {X : Type} (t : nat) (xs : list (list X)) : boolean :=
  match xs with
    | [] => true
    | (x::xs') => andb (t =? (length x)) (all_same_lengths t xs')
  end.
          
Search eqb.

Definition is_coherent_relation (r : relation) : boolean :=
  match r with
    {| data := data; order := order; |} =>
      all_same_lengths order data
  end.

Theorem is_coherent_equiv : forall r,
    coherent_relation r <-> is_coherent_relation r = true.
Proof.
  intros.
  split.
  - intros.
    unfold is_coherent_relation.
    destruct r.
    unfold coherent_relation in H.
    rename order0 into order.
    induction data0.
    + simpl. auto.
    + simpl.
      assert (length a = order).
      {
        apply H.
        simpl.
        left.
        auto.
      }.
      rewrite H0.
      rewrite PeanoNat.Nat.eqb_refl.
      assert (all_same_lengths order data0 = true).
      {
        apply IHdata0.
        intros.
        apply H.
        simpl.
        right.
        simpl in H1.
        auto.
      }.
      rewrite H1.
      auto.
 - intros.
   destruct r.
   rename order0 into order.
   induction data0.
   + simpl.
     unfold coherent_relation.
     intros.
     inversion H0.
   + simpl.
     unfold coherent_relation.
     intros.
     inversion H0.
     * simpl. subst.
       simpl in H.
       apply andb_prop in H.
       destruct H.
       apply PeanoNat.Nat.eqb_eq in H.
       auto.
     * simpl.
       assert (coherent_relation {| data := data0; order := order |}).
       apply IHdata0.
       simpl.
       unfold is_coherent_relation in H.
       simpl in H.
       apply andb_prop in H. destruct H.
       auto.
       unfold coherent_relation in H2.
       apply H2.
       auto.
Qed.

Fixpoint nat_in (n : nat) (xs : list nat) : boolean :=
  match xs with
    | [] => false
    | (x::xs') =>
        if x =? n then
          true
        else
          nat_in n xs'
  end.

Theorem nat_in_equiv : forall n xs,
    nat_in n xs = true <-> In n xs.
Proof.
  intros.
  split.
  - intros.
    induction xs.
    + simpl in H. discriminate H.
    + simpl in H.
      destruct (a =? n) eqn:Heq.
      * simpl.
        left.
        apply Nat.eqb_eq.
        auto.
      * simpl.
        right.
        apply IHxs.
        auto.
  - intros.
    induction xs.
    + auto.
    + simpl in H.
      destruct H.
      * simpl.
        apply Nat.eqb_eq in H.
        rewrite H.
        auto.
      * simpl.
        destruct (a =? n) eqn:Eq; auto.
Qed.

Definition set_union (r1 r2 : relation) : relation :=
  let new_data := (data r1) ++ (data r2) in
  {| data := new_data; order := order r1 |}.


(* TODO would be nice to get this to work *)
Ltac destruct_coherence H :=
  unfold coherent_relations in H;
  destruct H as [ H1 H2 ];
  destruct H as [ H2 H3 ];
  unfold coherent_relation in H1;
  unfold coherent_relation in H2;
  unfold coherent_relation in H3.


Lemma complaince_is_coherence : forall r o,
    compliant_relation r o ->
    coherent_relation r.
Proof.
  intros.
  unfold compliant_relation in H.
  destruct H.
  apply H.
Qed.

Lemma union_preserves_coherence : forall (r1 r2 r' : relation),
    coherent_relations r1 r2 ->
    r' = set_union r1 r2 ->
    compliant_relation r' (order r1).
Proof.
  intros.
  unfold coherent_relations in H.
  destruct H as [ H1 H2 ].
  destruct H2 as [ H2 H3 ].
  unfold compliant_relation.
  unfold coherent_relation in *.
  split.
  - simpl.
    intros.
    unfold set_union in H0.
    rewrite H0.
    simpl.
    assert (In t (data r1) \/ In t (data r2)).
    {
      apply in_app_or.
      rewrite H0 in H.
      simpl in H.
      apply H.
    }.
    destruct H4.
    + apply H1.
      apply H4.
    + rewrite H3.
      apply H2.
      apply H4.
  - unfold set_union in H0.
    rewrite H0.
    simpl.
    reflexivity.
Qed.

Fixpoint list_eqb (l1 l2 : list nat) : boolean :=
  match l1, l2 with
    | [], [] => true
    | (x::xs),(y::ys) => if x =? y then list_eqb xs ys else false
    | _, _ => false
  end.

Lemma list_neq_cons : forall x xs,
    list_eqb xs (x :: xs) = false.
Proof.
  intros.
  induction xs.
  - simpl. reflexivity.
  - simpl. destruct (a =? x) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      rewrite Heq.
      apply IHxs.
    + reflexivity.
Qed.

Lemma list_eqb_refl : forall xs,
    list_eqb xs xs = true.
Proof.
  induction xs.
  - auto.
  - simpl.
    rewrite Nat.eqb_refl.
    apply IHxs.
Qed.

Theorem list_eqb_eq : forall xs ys,
    list_eqb xs ys = true <-> xs = ys.
Proof.
  intros xs.
  induction xs.
  - split.
    intros.
    destruct ys.
    + auto.
    + simpl in H.
      discriminate.
    + intros.
      rewrite H.
      apply list_eqb_refl.
  - split.
    + intros.
      destruct ys.
      * simpl in H. discriminate.
      * destruct (a =? n) eqn:Heq.
        -- apply Nat.eqb_eq in Heq.
           subst.
           simpl in H.
           rewrite Nat.eqb_refl in H.
           assert (xs = ys).
           apply IHxs.
           auto.
           subst.
           reflexivity.
      -- simpl in H.
         rewrite Heq in H.
         discriminate.
   + intros.
     destruct ys.
     * simpl in H. discriminate.
     * destruct (a =? n) eqn:Heq.
       -- simpl.
          rewrite Heq.
          injection H.
          intros.
          subst.
          apply list_eqb_refl.
       -- simpl.
          injection H.
          intros.
          subst.
          rewrite Nat.eqb_refl in Heq. discriminate.
Qed.

Fixpoint sublist_in (ns : list nat) (l : list (list nat)) : boolean :=
  match l with
    | [] => false
    | x::xs => if list_eqb x ns then true else sublist_in ns xs
  end.

Lemma sublist_in_equiv : forall ns l,
    sublist_in ns l = true <-> In ns l.
Proof.
  split.
  - intros.
    induction l.
    + simpl in *. discriminate.
    + simpl.
      destruct (list_eqb a ns) eqn:Heq.
      * left.
        apply list_eqb_eq in Heq.
        auto.
      * right.
        apply IHl.
        simpl in H.
        rewrite Heq in H.
        apply H.
  - intros.
    induction l.
    + simpl in *. exfalso.
      apply H.
    + simpl.
      destruct (list_eqb a ns) eqn:Heq.
      * reflexivity.
      * simpl.
        apply IHl.
        simpl in H.
        destruct H.
        -- simpl.
           subst.
           rewrite list_eqb_refl in Heq.
           discriminate.
        -- simpl.
           apply H.
Qed.


Definition list_intersect (l1 l2 : list (list nat)) : list (list nat) :=
  filter (fun l => sublist_in l l2) l1.




Theorem list_intersect_step : forall l1 l2 l l',
    In l (list_intersect (l' :: l1) l2) ->
      (l = l') \/ (In l l1).
Proof.
  intros.
  destruct (sublist_in l l2) eqn:Hinl2.
  - simpl.
    destruct (list_eqb l l') eqn:Heq.
    + apply list_eqb_eq in Heq.
      auto.
    + simpl.
      right.
      simpl in H.
      destruct (sublist_in l' l2) eqn:Hl2.
      * simpl.
        simpl in H.
        destruct H.
        -- rewrite H in Heq.
           rewrite list_eqb_refl in Heq.
           discriminate.
        -- unfold list_intersect in H.
           remember (fun l => sublist_in l l2) as f.
           assert (In l l1 /\ f l = true).
           apply filter_In.
           apply H.
           destruct H0.
           apply H0.
    * unfold list_intersect in H.
      remember (fun l => sublist_in l l2) as f.
      assert (In l l1 /\ f l = true).
      apply filter_In.
      auto.
      destruct H0.
      apply H0.
  -
    simpl in H.
    destruct (sublist_in l' l2).
    + simpl in H.
      destruct H.
      * left.
        auto.
      * exfalso.
        unfold list_intersect in H.
        remember (fun l => sublist_in l l2) as f.
        assert (In l l1 /\ f l = true).
        apply filter_In.
        apply H.
        destruct H0.
        rewrite Heqf in H1.
        rewrite H1 in Hinl2.
        discriminate.
   + exfalso.
     unfold list_intersect in H.
     remember (fun l => sublist_in l l2) as f.
     assert (In l l1 /\ f l = true).
     apply filter_In.
     apply H.
     destruct H0.
     rewrite Heqf in H1.
     rewrite Hinl2 in H1.
     discriminate.
Qed.


Theorem list_intersect_spec : forall l1 l2 l,
    In l (list_intersect l1 l2) <-> (In l l1) /\ (In l l2).
Proof.
  intros l1.
  induction l1.
  - intros.
    split.
    + intros.
      exfalso.
      simpl in H.
      apply H.
    + intros.
      exfalso.
      simpl in H.
      destruct H.
      apply H.
  - intros.
    split.
    + intros.
      destruct (sublist_in l l2) eqn:Heql2;
        destruct (list_eqb l a) eqn:Heq.
      * simpl.
        rewrite list_eqb_eq in Heq.
        subst.
        apply sublist_in_equiv in Heql2.
        auto.
      * split.
        -- simpl.
           right.
           apply IHl1.
           simpl in H.
           destruct (sublist_in a l2).
           ++ simpl in H.
              destruct H.
              ** symmetry in H.
                apply list_eqb_eq in H.
                rewrite H in Heq.
                discriminate.
              ** simpl.
                 assert (In l l1 /\ In l l2).
                 apply IHl1.
                 apply H.
                 apply IHl1.
                 destruct H0.
                 split; apply H0.
          ++ simpl.
             assert (In l l1 /\ In l l2).
             apply IHl1.
             apply H.
             destruct H0.
             apply IHl1.
             split; apply H0.
        -- simpl.
           rewrite sublist_in_equiv in Heql2.
           apply Heql2.
      * exfalso.
        apply list_eqb_eq in Heq.
        simpl in H.
        destruct (sublist_in a l2) eqn:Hin.
        -- simpl.
           rewrite <- Heq in Hin.
           rewrite Heql2 in Hin.
           discriminate.
        -- assert (In l l1 /\ In l l2).
           apply IHl1.
           apply H.
           destruct H0.
           apply sublist_in_equiv in H1.
           rewrite H1 in Heql2.
           discriminate.
    * exfalso.
      simpl in H.
      destruct (sublist_in a l2) eqn:Hsub.
      -- simpl in H.
         destruct H.
         ++ symmetry in H.
            apply list_eqb_eq in H.
            rewrite H in Heq.
            discriminate.
         ++ assert (In l l1 /\ In l l2).
            apply IHl1.
            apply H.
            destruct H0.
            apply sublist_in_equiv in H1.
            rewrite H1 in Heql2.
            discriminate.
     -- simpl.
        assert (In l l1 /\ In l l2).
        apply IHl1.
        apply H.
        destruct H0.
        apply sublist_in_equiv in H1.
        rewrite H1 in Heql2.
        discriminate.
  + intros.
    simpl.
    simpl in H.
    destruct H.
    destruct (sublist_in a l2) eqn:Hal2.
    * simpl.
      destruct H.
      -- left.
         apply H.
      -- right.
         apply IHl1.
         split.
         apply H.
         apply H0.
    * simpl.
      destruct H.
      -- exfalso.
         rewrite H in Hal2.
         apply sublist_in_equiv in H0.
         rewrite H0 in Hal2.
         discriminate.
      -- simpl.
         apply IHl1.
         split.
         apply H.
         apply H0.
Qed.


Ltac compliance_proof :=
  unfold compliant_relation;
  unfold coherent_relations in *;
  unfold coherent_relation in *;
  split.


Definition set_intersect (r1 r2 : relation) : relation :=
  let data' := list_intersect (data r1) (data r2) in
  {| data := data'; order := order r1 |}.

Theorem intersect_preserves_coherence : forall r1 r2 r',
    coherent_relations r1 r2 ->
    r' = set_intersect r1 r2 ->
    compliant_relation r' (order r1).
Proof.
  intros.
  compliance_proof.
  - intros.
    destruct H.
    destruct H2.
    unfold set_intersect in H0.
    assert (In t (data r1) /\ In t (data r2)).
    {
      apply list_intersect_spec.
      rewrite H0 in H1.
      simpl in H1.
      apply H1.
    }.
    destruct H4.
    rewrite H0.
    simpl.
    apply H.
    apply H4.
  - rewrite H0.
    simpl.
    reflexivity.
Qed.


Definition interp_set_op (o : set_op) (r1 r2 : relation) :=
  match o with
    | Union => set_union r1 r2
    | Intersect => set_intersect r1 r2
  end.

Theorem set_ops_preserve_coherence (o : set_op) (r1 r2 r' : relation) :
  coherent_relations r1 r2 ->
  r' = interp_set_op o r1 r2 ->
  compliant_relation r' (order r1).
Proof.
  intros.
  destruct o.
  - eapply union_preserves_coherence; eauto.
  - eapply intersect_preserves_coherence; eauto.
Qed.

Fixpoint join_column (t : tuple) (ts : list tuple) : list tuple :=
  match ts with
    | [] => []
    | tup::ts' =>
        (tup ++ t) :: (join_column t ts')
  end.


Fixpoint cartesian_product (r1 r2 : list tuple) : list tuple :=
  match r1 with
    | [] => []
    | r::r1' => (join_column r r2) ++ (cartesian_product r1' r2)
  end.


Lemma join_order : forall (r : list tuple) (o1 o2 : nat) (t : tuple),
    length t = o1 ->
    (forall (t' : tuple), In t' r -> length t' = o2) ->
    forall (t' : tuple),
    In t' (join_column t r) ->
    length t' = o1 + o2.
Proof.
  intros r.
  induction r; intros.
  - simpl in H1.
    exfalso.
    apply H1.
  - simpl in H1.
    destruct H1.
    + simpl.
      rewrite <- H1.
      rewrite <- H.
      assert (length a = o2).
      apply H0.
      simpl.
      left.
      reflexivity.
      rewrite <- H2.
      rewrite Nat.add_comm.
      apply app_length.
    + apply IHr with (t := t).
      apply H.
      intros.
      apply H0.
      simpl.
      right.
      apply H2.
      apply H1.
Qed.

Lemma cartesian_product_order :
  forall (r1 r2 : list tuple) (o1 o2 : nat),
    (forall t, In t r1 -> length t = o1) ->
    (forall t, In t r2 -> length t = o2) ->
    forall t',
      In t' (cartesian_product r1 r2) ->
      length t' = (o1 + o2).
Proof.
  intros r1.
  induction r1; intros.
  - exfalso.
    inversion H1.
  - simpl in H1.
    apply in_app_or in H1.
    destruct H1.
    + simpl.
      apply join_order with
        (r := r2)
        (t := a).
      apply H.
      simpl.
      left.
      reflexivity.
      apply H0.
      apply H1.
    + apply IHr1 with (r2 := r2).
      intros.
      apply H.
      simpl.
      right.
      apply H2.
      intros.
      apply H0.
      apply H2.
      apply H1.
Qed.

Fixpoint eval_query (q : query) (db : database) : option relation :=
  match q with
  | Q_Table r => get_relation db r
  | Q_Set o q1 q2 =>
        r1 <- eval_query q1 db;;
        r2 <- eval_query q2 db;;
        if order r1 =? order r2 then
          Some (interp_set_op o r1 r2)
        else
          None
  | Q_Join q1 q2 =>
      r1 <- eval_query q1 db;;
      r2 <- eval_query q2 db;;
      if order r1 =? order r2 then
        Some
          {|
            data := cartesian_product (data r1) (data r2);
            order := order r1;
          |}
      else
        None

  | _ => None
  end.




Lemma database_relation_order : forall db sch r n o,
    compliant_database db sch ->
    nth sch n = Some o ->
    get_relation db n = Some r ->
    compliant_relation r o.
Proof.
  intros.
  unfold compliant_database in H.
  assert
    (exists r, get_relation db n = Some r /\ compliant_relation r o).
  {
    apply H.
    auto.
  }.
  destruct H2 as [ r' ].
  destruct H2.
  assert (r = r').
  apply one_relation_per_name with (db := db) (name := n); auto.
  subst.
  auto.
Qed.

Lemma compliance_is_coherence : forall r o,
    compliant_relation r o ->
    coherent_relation r.
Proof.
  intros.
  unfold compliant_relation in H.
  destruct H.
  apply H.
Qed.

Theorem schema_preserves_order :
  forall (q : query)  (db : database) (sch : schema) (o : nat) (r : relation),
    compliant_database db sch ->
    has_query_order sch q o ->
    eval_query q db = Some r ->
    compliant_relation r o.
Proof.
  intros q.
  induction q; intros; try (inversion H1; fail).
  - rename r into name.
    inversion H0.
    subst.
    apply database_relation_order
            with (db := db)
                 (sch := sch)
                 (n := name); auto.
  - simpl.
    inversion H0.
    subst.
    simpl in H1.
    destruct (eval_query q1 db) eqn:Hq1;
      destruct (eval_query q2 db) eqn:Hq2;
      try discriminate.
    + simpl.
      destruct (order r0 =? order r1) eqn:Heq; try discriminate.
        simpl.
        rename r1 into r2.
        rename r0 into r1.
        apply Nat.eqb_eq in Heq.
        assert (compliant_relation r1 o /\ compliant_relation r2 o).
        {
          split.
          - apply IHq1 with (db := db) (sch := sch); auto.
          - apply IHq2 with (db := db) (sch := sch); auto.
        }.
        destruct H2.
        assert (order r1 = o).
        {
          unfold compliant_relation in H2.
          destruct H2.
          apply H4.
        }.
        rewrite <- H4.
        apply set_ops_preserve_coherence with (o := s) (r2 := r2).
        * unfold coherent_relations.
          split.
          apply compliance_is_coherence with (o := o).
          auto.
          split.
          apply compliance_is_coherence with (o := o).
          auto.
          auto.
        * injection H1.
          intros.
          symmetry.
          auto.
  - inversion H0.
    subst.
    simpl in H1.
    destruct (eval_query q1 db) eqn:Hq1;
      destruct (eval_query q2 db) eqn:Hq2;
      try discriminate.
    destruct (order r0 =? order r1) eqn:Heq.
    + injection H1.
      intros.
      clear H1.
      rewrite <- H2.
      unfold compliant_relation.
      simpl.
      split.
      * simpl.
        unfold coherent_relation.




(* Proof  *)
Theorem sound_schema :
  forall (q : query) (db : database) (sch : schema) (o : nat),
    compliant_database db sch ->
    has_query_order sch q o ->
    exists (r : relation),
      eval_query q db = Some r.
Proof.
  intros q.
  induction q; intros;
    try (inversion H0).
  - simpl.
    unfold compliant_database in H.
    rename r into name.
    assert (exists r, get_relation db name = Some r /\ compliant_relation r o).
    {
      apply H.
      inversion H0.
      subst.
      apply H3.
    }.
    destruct H5 as [ r ].
    destruct H5.
    exists r.
    apply H5.
  - subst.
    assert (exists r, eval_query q1 db = Some r).
    {
      apply IHq1 with (sch := sch) (o := o).
      apply H.
      apply H6.
    }.
    destruct H1 as [ r1 ].
    assert (compliant_relation r1 o).
    {
      apply schema_preserves_order
              with (q := q1)
                   (db := db)
                   (sch := sch); auto.
    }.
    assert (exists r, eval_query q2 db = Some r).
    {
      apply IHq2 with (sch := sch) (o := o).
      apply H.
      auto.
    }.
    destruct H3 as [ r2 ].
    assert (compliant_relation r2 o).
    {
      apply schema_preserves_order
              with (q := q2)
                   (db := db)
                   (sch := sch); auto.
    }.
    simpl.
    rewrite H1.
    rewrite H3.
    exists (interp_set_op s r1 r2).
    unfold compliant_relation in H4.
    unfold compliant_relation in H2.
    destruct H2.
    destruct H4.
    rewrite H8.
    rewrite <- H5.
    rewrite Nat.eqb_refl.
    reflexivity.
Qed.

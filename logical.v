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


Definition tuple := list nat.
Record relation : Type :=
  {
    data : list tuple;
    order : nat;
  }.


Definition coherent_relation (r : relation) : Prop :=
  forall t,
    In t (data r) ->
    length t = (order r).

Definition coherent_relations (r1 r2 : relation) : Prop :=
  coherent_relation r1 /\ coherent_relation r2 /\ order r1 = order r2.

Definition database := list relation.
Definition coherent_database (db : database) : Prop :=
  forall r,
    In r db ->
    coherent_relation r.

Definition boolean := bool.
Definition relname : Type := nat.
Definition term : Type := nat.
Definition predicate := term -> boolean.
Definition select : Type := nat.
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
  | Q_Pred : predicate -> list term -> atom
  | Q_Quant :
    quantifier -> predicate -> list term ->
    query -> atom
  | Q_In : list select -> query -> atom
  | Q_Exists : query -> atom.


Fixpoint nth {X : Type} (lst : list X) (n : nat) : option X :=
  match lst with
    | [] => None
    | (x :: xs) =>
        match n with
          | 0 => Some x
          | S n' => nth xs n'
        end
  end.

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

Lemma union_preserves_coherence : forall (r1 r2 r' : relation),
    coherent_relations r1 r2 ->
    r' = set_union r1 r2 ->
    coherent_relation r' /\ order r1 = order r'.
Proof.
  intros.
  unfold coherent_relations in H.
  destruct H as [ H1 H2 ].
  destruct H2 as [ H2 H3 ].
  unfold coherent_relation in *.
  split.
  - intros.
    rewrite H0 in H.
    apply in_app_or in H.
    rewrite H0.
    destruct H.
    + simpl.
      apply H1.
      apply H.
    + simpl.
      rewrite H3.
      apply H2.
      apply H.
  - rewrite H0.
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



Definition set_intersect (r1 r2 : relation) : relation :=
  let data' := list_intersect (data r1) (data r2) in
  {| data := data'; order := order r1 |}.

Theorem intersect_preserves_coherence : forall r1 r2 r',
    coherent_relations r1 r2 ->
    r' = set_intersect r1 r2 ->
    coherent_relation r' /\ order r1 = order r'.
Proof.
  intros.
  unfold coherent_relations in H.
  destruct H.
  destruct H1.
  rewrite H0.
  split.
  - unfold coherent_relation in *.
    intros.
    simpl.
    apply H.
    simpl in H3.
    apply list_intersect_spec in H3.
    destruct H3.
    apply H3.
  - simpl.
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
  coherent_relation r' /\ order r1 = order r'.
Proof.
  intros.
  destruct o.
  - eapply union_preserves_coherence; eauto.
  - eapply intersect_preserves_coherence; eauto.
Qed.



Fixpoint eval_query (q : query) (db : database) : option relation :=
  match q with
  | Q_Table r => nth db r
  | _ => None
  end.

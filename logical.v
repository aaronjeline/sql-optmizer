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


Inductive type : Type :=
  | Number
  | Boolean.

Definition type_eqb t1 t2 : boolean :=
  match t1, t2 with
    | Number, Number => true
    | Boolean, Boolean => true
    | _, _ => false
  end.

Theorem type_eqb_eq : forall t1 t2,
    type_eqb t1 t2 = true <-> t1 = t2.
Proof.
  split;
    intros;
    destruct t1,t2;
    auto;
    simpl in H;
    discriminate.
Qed.

Theorem type_eqb_refl : forall t1,
    type_eqb t1 t1 = true.
Proof.
  intros.
  rewrite type_eqb_eq.
  reflexivity.
Qed.

Inductive predicate : Type :=
  | Literal : nat -> predicate
  | Tru
  | Fls
  | And : predicate -> predicate -> predicate
  | Or : predicate -> predicate -> predicate
  | Equals : predicate -> predicate -> predicate
  | Plus : predicate -> predicate -> predicate
  | LessThan : predicate -> predicate -> predicate
  | Field : nat -> predicate.

Inductive value : Type :=
  | VTrue
  | VFalse
  | VNum : nat -> value.

Definition value_eqb v1 v2 : boolean :=
  match v1, v2 with
    | VTrue, VTrue => true
    | VFalse, VFalse => true
    | VNum n1, VNum n2 => n1 =? n2
    | _, _ => false
  end.

Theorem value_eqb_eq : forall v1 v2,
    value_eqb v1 v2 = true <-> v1 = v2.
Proof.
  split; intros; destruct v1, v2; auto;
    try (simpl in H; discriminate).
  - simpl in H.
    apply Nat.eqb_eq in H.
    auto.
  - simpl.
    apply Nat.eqb_eq.
    injection H.
    auto.
Qed.

Lemma value_eqb_refl : forall v,
    value_eqb v v = true.
Proof.
  intros.
  apply value_eqb_eq.
  auto.
Qed.

Fixpoint compute_type (p : predicate) (order : nat) : option type :=
  match p with
    | Literal _ => Some Number
    | Field n => if n <? order then Some Number else None
    | Tru => Some Boolean
    | Fls => Some Boolean
    | Equals p1 p2 =>
        t1 <- compute_type p1 order;;
        t2 <- compute_type p2 order;;
        if andb (type_eqb t1 t2) (type_eqb t1 Number) then
          Some Boolean
        else None
    | Plus p1 p2 =>
        t1 <- compute_type p1 order;;
        t2 <- compute_type p2 order;;
        if andb (type_eqb t1 t2) (type_eqb t1 Number) then
          Some Number
        else None
    | LessThan p1 p2 =>
        t1 <- compute_type p1 order;;
        t2 <- compute_type p2 order;;
        if andb (type_eqb t1 t2) (type_eqb t1 Number) then
          Some Boolean
        else None
    | And p1 p2 =>
        t1 <- compute_type p1 order;;
        t2 <- compute_type p2 order;;
        if andb (type_eqb t1 t2) (type_eqb t1 Boolean) then
          Some Boolean
        else None
    | Or p1 p2 =>
        t1 <- compute_type p1 order;;
        t2 <- compute_type p2 order;;
        if andb (type_eqb t1 t2) (type_eqb t1 Boolean) then
          Some Boolean
        else None
  end.

Inductive well_typed : nat -> predicate -> type -> Prop :=
  | WT_Lit : forall n o, well_typed o (Literal n) Number
  | WT_Field : forall i o,
      i < o ->
      well_typed o (Field i) Number
  | WT_True : forall o, well_typed o (Tru) Boolean
  | WT_False : forall o, well_typed o (Fls) Boolean
  | WT_Plus : forall o p1 p2,
      well_typed o p1 Number ->
      well_typed o p2 Number ->
      well_typed o (Plus p1 p2) Number
  | WT_Equals : forall o p1 p2,
      well_typed o p1 Number ->
      well_typed o p2 Number ->
      well_typed o (Equals p1 p2) Boolean
  | WT_LessThan : forall o p1 p2,
      well_typed o p1 Number ->
      well_typed o p2 Number ->
      well_typed o (LessThan p1 p2) Boolean
  | WT_And : forall o p1 p2,
      well_typed o p1 Boolean ->
      well_typed o p2 Boolean ->
      well_typed o (And p1 p2) Boolean
  | WT_Or : forall o p1 p2,
      well_typed o p1 Boolean ->
      well_typed o p2 Boolean ->
      well_typed o (Or p1 p2) Boolean.

Theorem well_typed_computable : forall p o t,
    well_typed o p t <-> compute_type p o = Some t.
Proof.
  intros p.
  induction p; split; intros; try (inversion H; subst); auto.
  - apply WT_Lit.
  - apply WT_True.
  - apply WT_False.
  - apply IHp1 in H3.
    apply IHp2 in H5.
    simpl.
    rewrite H3.
    rewrite H5.
    simpl.
    reflexivity.
  - destruct t;
      destruct (compute_type p1 o) eqn:Hp1;
      destruct (compute_type p2 o) eqn:Hp2;
      try discriminate.
    + destruct (type_eqb t t0) eqn:Hteq;
        destruct (type_eqb t Boolean) eqn:Hbool;
        try (simpl in H1; discriminate).
    + destruct (type_eqb t t0) eqn:Hteq;
        destruct (type_eqb t Boolean) eqn:Hbool;
        try (simpl in H1; discriminate).
      apply type_eqb_eq in Hbool.
      apply type_eqb_eq in Hteq.
      subst.
      apply IHp1 in Hp1.
      apply IHp2 in Hp2.
      apply WT_And; auto.
  - simpl.
    apply IHp1 in H3.
    apply IHp2 in H5.
    rewrite H3.
    rewrite H5.
    auto.
  - destruct t;
      destruct (compute_type p1 o) eqn:Hp1;
      destruct (compute_type p2 o) eqn:Hp2;
      try discriminate.
    + destruct (type_eqb t t0);
        destruct (type_eqb t Boolean);
        try discriminate.
    + destruct (type_eqb t t0) eqn:Heq1;
        destruct (type_eqb t Boolean) eqn:Heq2;
        try discriminate.
      apply type_eqb_eq in Heq1.
      apply type_eqb_eq in Heq2.
      subst.
      apply IHp1 in Hp1.
      apply IHp2 in Hp2.
      apply WT_Or; auto.
    - apply IHp1 in H3.
      apply IHp2 in H5.
      simpl.
      rewrite H3.
      rewrite H5.
      auto.
    - destruct (compute_type p1 o) eqn:Hp1;
        destruct (compute_type p2 o) eqn:Hp2;
        try discriminate.
      + destruct (type_eqb t0 t1) eqn:Heq1;
          destruct (type_eqb t0 Number) eqn:Heq2;
          try discriminate.
        apply type_eqb_eq in Heq1.
        apply type_eqb_eq in Heq2.
        subst.
        apply IHp1 in Hp1.
        apply IHp2 in Hp2.
        destruct t; try (simpl in H; discriminate).
        apply WT_Equals; auto.
    - apply IHp1 in H3.
      apply IHp2 in H5.
      simpl.
      rewrite H3.
      rewrite H5.
      auto.
    - destruct (compute_type p1 o) eqn:Hp1;
        destruct (compute_type p2 o) eqn:Hp2;
        try discriminate.
      destruct t;
        destruct (type_eqb t0 t1) eqn:Heq1;
        destruct (type_eqb t0 Number) eqn:Heq2;
        try discriminate.
      apply IHp1 in Hp1.
      apply IHp2 in Hp2.
      apply type_eqb_eq in Heq2.
      apply type_eqb_eq in Heq1.
      subst.
      apply WT_Plus; auto.
      - simpl.
        apply IHp1 in H3.
        apply IHp2 in H5.
        rewrite H3.
        rewrite H5.
        auto.
  - destruct (compute_type p1 o) eqn:Hp1;
      destruct (compute_type p2 o) eqn:Hp2;
      try discriminate.
    destruct t;
      destruct (type_eqb t0 t1) eqn:Heq1;
      destruct (type_eqb t0 Number) eqn:Heq2;
      try discriminate.
    apply type_eqb_eq in Heq1.
    apply type_eqb_eq in Heq2.
    subst.
    apply IHp1 in Hp1.
    apply IHp2 in Hp2.
    apply WT_LessThan; auto.
  - simpl.
    apply Nat.ltb_lt in H2.
    rewrite H2.
    reflexivity.
  - destruct (n <? o) eqn:Hlt.
    + injection H1.
      intros.
      subst.
      apply WT_Field.
      apply Nat.ltb_lt in Hlt.
      auto.
    + discriminate.
Qed.

Inductive valid_predicate : nat -> predicate -> Prop :=
  | Valid : forall o p,
      well_typed o p Boolean ->
      valid_predicate o p.

Definition is_valid_predicate (o : nat) (p : predicate) : boolean :=
  match compute_type p o with
    | None => false
    | Some t => type_eqb t Boolean
  end.

Lemma valid_predicate_computable : forall o p,
    valid_predicate o p <-> is_valid_predicate o p = true.
Proof.
  split.
  - intros.
    inversion H.
    subst.
    apply well_typed_computable in H0.
    unfold is_valid_predicate.
    rewrite H0.
    auto.
  - intros.
    unfold is_valid_predicate in H.
    destruct (compute_type p o) eqn:Htype.
    + apply Valid.
      apply well_typed_computable in Htype.
      apply type_eqb_eq in H.
      subst.
      apply Htype.
    + discriminate.
Qed.

Definition extract_field (t : tuple) (i : nat) : option nat :=
  nth_error t i.

Lemma extract_coherent_field : forall i (t : tuple) o,
    length t = o ->
    i < o ->
    exists (n : nat),
      extract_field t i = Some n.
Proof.
  intros.
  destruct (extract_field t i) eqn:Heq.
  - exists n.
    reflexivity.
  - exfalso.
    unfold extract_field in Heq.
    assert (nth_error t i <> None).
    {
      apply nth_error_Some.
      rewrite <- H in H0.
      apply H0.
    }.
    rewrite Heq in H1.
    unfold not in H1.
    apply H1.
    reflexivity.
Qed.

Inductive predicate_value : predicate -> Prop :=
  | LitVal : forall n, predicate_value (Literal n)
  | TruVal : predicate_value Tru
  | FlsVal : predicate_value Fls.

(* small step semantics for predicate *)
Inductive predicate_steps : predicate -> tuple -> predicate -> Prop :=
  | FieldStep : forall t i n,
      extract_field t i = Some n ->
      predicate_steps (Field i) t (Literal n)
  | Andvalue__true : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Tru ->
      p2 = Tru ->
      predicate_steps (And p1 p2) t (Tru)
  | Andvalue__false : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Fls \/ p2 = Fls ->
      predicate_steps (And p1 p2) t (Fls)
  | And1 : forall p1 p1' p2 t,
      predicate_steps p1 t p1' ->
      predicate_steps (And p1 p2) t (And p1' p2)
  | And2 : forall p1 p2 p2' t,
      predicate_value p1 ->
      predicate_steps p2 t p2' ->
      predicate_steps (And p1 p2) t (And p1 p2')
  | Orvalue__true : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Tru \/ p2 = Tru ->
      predicate_steps (Or p1 p2) t (Tru)
  | Orvalue__false : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Fls ->
      p2 = Fls ->
      predicate_steps (Or p1 p2) t (Fls)
  | Or1 : forall p1 p1' p2 t,
      predicate_steps p1 t p1' ->
      predicate_steps (Or p1 p2) t (Or p1' p2)
  | Or2 : forall p1 p2 p2' t,
      predicate_value p1 ->
      predicate_steps p2 t p2' ->
      predicate_steps (Or p1 p2) t (Or p1 p2')
  | Equalsvalue__true : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = p2 ->
      predicate_steps (Equals p1 p2) t (Tru)
  | Equalsvalue__false : forall p1 p2 t,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 <> p2 ->
      predicate_steps (Equals p1 p2) t (Fls)
  | Equals1 : forall p1 p1' p2 t,
      predicate_steps p1 t p1' ->
      predicate_steps (Equals p1 p2) t (Equals p1' p2)
  | Equals2 : forall p1 p2 p2' t,
      predicate_value p1 ->
      predicate_steps p2 t p2' ->
      predicate_steps (Equals p1 p2) t (Equals p1 p2')
  | LessThanvalue__true : forall p1 p2 t n1 n2,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Literal n1 ->
      p2 = Literal n2 ->
      n1 < n2 ->
      predicate_steps (LessThan p1 p2) t (Tru)
  | LessThanvalue__false : forall p1 p2 t n1 n2,
      predicate_value p1 ->
      predicate_value p2 ->
      p1 = Literal n1 ->
      p2 = Literal n2 ->
      n1 >= n2 ->
      predicate_steps (LessThan p1 p2) t (Fls)
  | LessThan1 : forall p1 p1' p2 t,
      predicate_steps p1 t p1' ->
      predicate_steps (LessThan p1 p2) t (LessThan p1' p2)
  | LessThan2 : forall p1 p2 p2' t,
      predicate_value p1 ->
      predicate_steps p2 t p2' ->
      predicate_steps (LessThan p1 p2) t (LessThan p1 p2').



(* Big Step relation *)
Inductive predicate_bigstep : predicate -> tuple -> predicate -> Prop :=
  | Refl : forall p1 t, predicate_bigstep p1 t p1
  | Steps : forall p1 t p2,
      predicate_steps p1 t p2 ->
      predicate_bigstep p1 t p2
  | Trans : forall p1 p2 p3 t,
      predicate_steps p1 t p2 ->
      predicate_steps p2 t p3 ->
      predicate_bigstep p1 t p3.

Definition make_value (p : predicate) : option value :=
  match p with
    | Literal n => Some (VNum n)
    | Tru => Some VTrue
    | Fls => Some VFalse
    | _ => None
  end.

Lemma make_value_spec : forall p,
    predicate_value p ->
    exists v,
      make_value p = Some v.
Proof.
  intros.
  inversion H; simpl.
  - exists (VNum n).
    auto.
  - exists VTrue.
    auto.
  - exists VFalse.
    auto.
Qed.

Fixpoint eval_predicate (p : predicate) (t : tuple) : option value :=
  match p with
    | Literal n => Some (VNum n)
    | Field i =>
        fv <- extract_field t i;;
        Some (VNum fv)
    | Tru => Some (VTrue)
    | Fls => Some (VFalse)
    | And p1 p2 =>
        v1 <- eval_predicate p1 t;;
        v2 <- eval_predicate p2 t;;
        match v1, v2 with
          | VTrue, VTrue => Some VTrue
          | VTrue, VFalse => Some VFalse
          | VFalse, VFalse => Some VFalse
          | VFalse, VTrue => Some VFalse
          | _, _ => None
        end
    | Or p1 p2 =>
        v1 <- eval_predicate p1 t;;
        v2 <- eval_predicate p2 t;;
        match v1, v2 with
          | VTrue, VTrue => Some VTrue
          | VTrue, VFalse => Some VTrue
          | VFalse, VFalse => Some VFalse
          | VFalse, VTrue => Some VTrue
          | _, _ => None
        end
    | Equals p1 p2 =>
        v1 <- eval_predicate p1 t;;
        v2 <- eval_predicate p2 t;;
        if value_eqb v1 v2 then Some VTrue else Some VFalse
   | Plus p1 p2 =>
       v1 <- eval_predicate p1 t;;
       v2 <- eval_predicate p2 t;;
       match v1, v2 with
         | (VNum n1), (VNum n2) => Some (VNum (n1 + n2))
         | _, _ => None
        end
   | LessThan p1 p2 =>
       v1 <- eval_predicate p1 t;;
       v2 <- eval_predicate p2 t;;
       match v1, v2 with
         | (VNum n1), (VNum n2) => Some (if n1 <? n2 then VTrue else VFalse)
         | _, _ => None
        end
  end.


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
  | Q_Raw : predicate -> formula
  (* | Q_Atom : atom -> formula *)

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
      has_query_order sch (Q_Join q1 q2) o
  | Order_Select : forall sch q1 f o,
      has_query_order sch q1 o ->
      valid_predicate o f ->
      has_query_order sch (Q_Sigma (Q_Raw f) q1) o.




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
      | Q_Sigma (Q_Raw f) q =>
          o <- query_order sch q;;
          if is_valid_predicate o f then
            Some o
          else
            None
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
    intros.
    + inversion H.
      subst.
      simpl.
      apply IHq in H3.
      rewrite H3.
      apply valid_predicate_computable in H5.
      rewrite H5.
      reflexivity.
    + intros.
      simpl in H.
      destruct f eqn:Hf.
      destruct (query_order sch q) eqn:qo; try discriminate.
      destruct (is_valid_predicate n0 p) eqn:vp; try discriminate.
      injection H.
      intros.
      subst.
      apply IHq in qo.
      apply valid_predicate_computable in vp.
      apply Order_Select; auto.
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

Definition join_relations (r1 r2 : relation) : relation :=
  {|
    data := cartesian_product (data r1) (data r2);
    order := (order r1) + (order r2);
  |}.


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

Lemma join_order_spec : forall (r1 r2 r' : relation) (o1 o2 o' : nat),
    compliant_relation r1 o1 ->
    compliant_relation r2 o2 ->
    join_relations r1 r2 = r' ->
    o' = o1 + o2 ->
    compliant_relation r' o'.
Proof.
  intros.
  unfold compliant_relation in *.
  unfold coherent_relation in *.
  destruct H.
  destruct H0.
  split.
  - intros.
    unfold join_relations in H1.
    rewrite <- H1.
    simpl.
    destruct r1.
    destruct r2.
    apply cartesian_product_order
            with (r1 := data0)
                 (r2 := data1).
    intros.
    auto.
    intros.
    auto.
    rewrite <- H1 in H5.
    simpl in H5.
    auto.
  - unfold join_relations in H1.
    rewrite <- H1.
    simpl.
    rewrite H2.
    rewrite H3.
    rewrite H4.
    reflexivity.
Qed.


Definition run_formula (f : formula) (t : tuple)

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
      Some (join_relations r1 r2)
  | Q_Sigma f q =>
      r <- eval_query q db;;
      filter f q
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
    injection H1.
    intros.
    rewrite <- H2.
    remember (o1 + o2) as o'.
    apply join_order_spec
            with (r1 := r0)
                 (r2 := r1)
                 (o1 := o1)
                 (o2 := o2).
    apply IHq1 with (db := db) (sch := sch); auto.
    apply IHq2 with (db := db) (sch := sch); auto.
    reflexivity.
    auto.
Qed.

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
  - subst.
    assert (exists r, eval_query q1 db = Some r).
    apply IHq1 with (sch := sch) (o := o1); auto.
    destruct H1 as [ r1 ].
    assert (exists r, eval_query q2 db = Some r).
    apply IHq2 with (sch := sch) (o := o2); auto.
    destruct H2 as [ r2 ].
    exists (join_relations r1 r2).
    simpl.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

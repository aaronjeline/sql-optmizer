From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

Definition compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).


(* Setup Lists *)
Open Scope list_scope.
Import ListNotations.

Inductive result (A : Type) :=
  | Result :  A -> result A
  | No_Result : result A
  | Empty_Cursor : result A.

Fixpoint iter {A B : Type} (f : A -> (B * A))  n c acc :=
  match n with
    | 0 => (c, acc)
    | (S n') =>
      let (x, c') := (f c) in
      iter f n' c' (c :: acc)
  end.


Class Cursor c (elt : Type) :=
  {
    next : c -> result elt * c;
    has_next : c -> Prop;
    reset : c -> c;
    collection : c -> list elt;
    visited : c -> list elt;
    coherent : c -> Prop;
    ubound : c -> nat;
  }.


Class SafeCursor c elt `{Cursor c elt} :=
  {
    next_collection :
      forall c,
        coherent c ->
        collection (snd (next c)) = collection c;
    next_visited_Result : forall a c c',
      coherent c ->
      next c = (Result elt a, c') ->
      visited c' = a :: (visited c);
    next_visited_No_Result : forall c c',
      coherent c ->
      next c = (No_Result elt, c') ->
      visited c' = visited c;
    next_visited_Empty_Cursor : forall c c',
      coherent c ->
      next c = (Empty_Cursor elt, c') ->
      visited c' = visited c;
    next_coherent : forall c,
      coherent c -> coherent (snd (next c));
    has_next_spec : forall c,
        coherent c -> ~ has_next c ->
        (collection c) = (rev (visited c));
    has_next_next_neg : forall c,
        coherent c ->
        (has_next c <-> fst (next c) <> (Empty_Cursor elt));
    reset_collection : forall c,
        collection (reset c) = collection c;
    reset_visited : forall c,
        visited (reset c) = [];
    reset_coherent : forall c,
        coherent (reset c);
    ubound_complate : forall c acc,
        coherent c ->
        ~ has_next (fst (iter next (ubound c) c acc));

  }.



Record Seq (elt : Type) : Type :=
  {
    total : list elt;
    to_visit : list elt;
    vs : list elt;
  }.

Instance seqCursor (elt : Type) : Cursor (Seq elt) elt :=
  {
    next c := match c with
                | {| total := t; to_visit := tv; vs := vs |} =>
                    match tv with
                      | [] => (Empty_Cursor elt, c)
                      | (x::xs) => (Result elt x, {| total := t; to_visit := xs; vs := x::vs |})
                    end
              end;
    has_next c := match to_visit elt c with
                    | [] => False
                    | (_::_) => True
                  end;
    reset c := let t := total elt c in {| total := t; to_visit := t; vs := [] |};
    collection c := total elt c;
    visited c := vs elt c;
    coherent c := total elt c = (rev (vs elt c)) ++ (to_visit elt c);
    ubound c := length (to_visit elt c)
  }.

Theorem seq_next_collection (elt : Type) :
  forall (c : Seq elt) , coherent c ->
                    collection (snd (next c)) = collection c.
Proof.
  intros.
  induction c.
  simpl.
  induction to_visit0.
  auto.
  simpl.
  auto.
Qed.


Lemma seq_next_result elt : forall (c : Seq elt) c' x,
    coherent c ->
    next c = (Result elt x, c') ->
    visited c' = x :: (visited c).
Proof.
  intros.
  destruct c.
  destruct to_visit0.
  - simpl.
    simpl in H0. injection H0 as H'. discriminate H'.
  - simpl.
    simpl in H0.
    injection H0.
    intros.
    rewrite <- H1.
    simpl.
    rewrite H2.
    auto.
Qed.



Lemma seq_next_visited_No_Result elt : forall c c',
      coherent c ->
      next c = (No_Result elt, c') ->
      visited c' = visited c.
Proof.
  intros.
  destruct c.
  - destruct to_visit0.
    + simpl in H0.
      injection H0.
      intros.
      rewrite H1.
      auto.
    + simpl in H0.
      injection H0.
      intros.
      discriminate H2.
Qed.

Lemma seq_next_visited_Empty_Cursor elt : forall c c',
      coherent c ->
      next c = (Empty_Cursor elt, c') ->
      visited c' = visited c.
Proof.
  intros.
  destruct c.
  destruct to_visit0.
  - simpl in H0.
    injection H0.
    simpl.
    intros.
    rewrite <- H1.
    simpl.
    auto.
  - simpl in H0.
    injection H0.
    intros.
    simpl in *.
    discriminate H2.
Qed.



Lemma no_result_same_seq (elt : Type) : forall (c c' : Seq elt),
      coherent c ->
      (next c = (No_Result elt, c')) \/ (next c = (Empty_Cursor elt, c')) ->
      c = c'.
Proof.
  intros.
  destruct H0;
  simpl;
  inversion H0;
    destruct c;
    destruct to_visit0;
    injection H2;
    auto;
    injection H2;
    intros;
    discriminate H3.
Qed.


Lemma total_unchanged (elt : Type) : forall (c : Seq elt),
      coherent c ->
      total elt c = total elt (snd (next c)).
Proof.
  intros.
  destruct (next c) eqn:Heq.
  rename s into c'.
  destruct r;
  simpl;
    destruct c;
    destruct c';
    inversion Heq;
    destruct to_visit0;
      simpl;
      inversion Heq;
      auto.
Qed.

Lemma seq_next_coherent_result (elt : Type) : forall (c c' : Seq elt) x,
      coherent c ->
      next c = (Result elt x, c') ->
      coherent c'.
Proof.
  intros.
  inversion H.
  simpl in H0.
  destruct c.
  destruct to_visit0.
  injection H0.
  intros.
  discriminate H3.
  rename to_visit0 into es.
  simpl in H0.
  simpl in H2.
  simpl.
  injection H0.
  intros.
  rewrite <- H1.
  simpl.
  rewrite H2.
  remember (rev vs0) as r.
  assert (((r ++ [e]) ++ es) = r ++ ([e] ++ es)).
  rewrite app_assoc.
  auto.
  rewrite H4.
  auto.
Qed.






Lemma seq_next_coherent (elt : Type) : forall (c : Seq elt),
      coherent c -> coherent (snd (next c)).
Proof.
  intros.
  destruct (next c) eqn:Heq.
  destruct r.
  - rename s into c'.
    rename e into x.
    eapply seq_next_coherent_result; eauto.
  - assert (c = s).
    apply no_result_same_seq; auto.
    rewrite <- H0.
    auto.
  - assert (c = s).
    apply no_result_same_seq; auto.
    rewrite <- H0.
    auto.
Qed.

Lemma seq_has_next_spec (elt : Type) : forall (c : Seq elt),
      coherent c ->
      ~ has_next c ->
      (collection c) = (rev (visited c)).
Proof.
  intros.
  inversion H.
  simpl.
  destruct c.
  simpl in *.
  destruct to_visit0.
  - rewrite H2.
    rewrite app_nil_r.
    auto.
  - simpl.
    unfold not in H0.
    exfalso.
    apply H0.
    tauto.
Qed.

Lemma seq_has_next_next_neg (elt : Type) : forall c,
        coherent c ->
        (has_next c <-> fst (next c) <> (Empty_Cursor elt)).
Proof.
  intros.
  split.
  - intros.
    simpl.
    destruct c.
    destruct to_visit0.
    + auto.
    + discriminate.
  - intros.
    destruct c.
    destruct to_visit0;
      simpl in *;
      auto.
Qed.


Lemma seq_ubound_complate (elt : Type) : forall (c : Seq elt) acc,
        coherent c ->
        ~ has_next (fst (iter next (ubound c) c acc)).
Proof.
  intros.
  destruct c.
  induction to_visit0.
  - unfold not.
    intros.
    simpl in *.
    auto.
  - unfold not.
    intros.
    simpl in H.





Instance seqsafe elt : SafeCursor (Seq elt) elt.
Proof.
  constructor; intros; auto.
  - apply seq_next_collection.
    auto.
  -
    apply seq_next_result; auto.
  - intros.
    apply seq_next_visited_No_Result; auto.
  - intros.
    apply seq_next_visited_Empty_Cursor; auto.
  - intros.
    apply seq_next_coherent.
    auto.
  - apply seq_has_next_spec.
    auto.
    auto.
  - apply seq_has_next_next_neg.
    auto.
  - simpl. auto.
Qed.

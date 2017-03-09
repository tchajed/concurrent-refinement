Set Implicit Arguments.

Require Import FunctionalExtensionality.

Definition EqDec A := forall (x y:A), {x=y}+{x<>y}.
Existing Class EqDec.

Definition eq_dec {A} {dec:EqDec A} x y : {x=y}+{x<>y}
  := dec x y.

Definition pfun A V := A -> option V.

Definition upd A {AEQ: EqDec A} V (m: pfun A V) a v : pfun A V :=
  fun a' => if AEQ a a' then Some v else m a'.

Ltac destruct_match :=
  match goal with
  | [ H: context[match ?d with | _ => _ end] |- _ ] =>
    let Heq := fresh in
    destruct d eqn:Heq; simpl in H; subst; try congruence
  | [ |- context[match ?d with | _ => _ end] ] =>
    let Heq := fresh in
    destruct d eqn:Heq; simpl; subst; try congruence
  end.

Theorem upd_eq : forall A {AEQ: EqDec A} V (m: pfun A V) a v,
    upd m a v a = Some v.
Proof.
  unfold upd; intros.
  destruct_match; auto.
Qed.

Theorem upd_neq : forall A {AEQ: EqDec A} V (m: pfun A V) a v a',
    a <> a' ->
    upd m a v a' = m a'.
Proof.
  unfold upd; intros.
  destruct_match; auto.
Qed.

Hint Rewrite upd_eq  : upd.
Hint Rewrite upd_neq using (solve [ auto ]) : upd.

Theorem upd_commute : forall A {AEQ:EqDec A} V (m: pfun A V) a v a' v',
    a <> a' ->
    upd (upd m a v) a' v' = upd (upd m a' v') a v.
Proof.
  unfold upd; intros.
  extensionality a''.
  repeat destruct_match.
Qed.

Theorem upd_repeat : forall A {AEQ:EqDec A} V (m: pfun A V) a v v',
    upd (upd m a v) a v' = upd m a v'.
Proof.
  unfold upd; intros.
  extensionality a''.
  destruct_match.
Qed.

Hint Rewrite upd_repeat : upd.

Definition remove A {AEQ: EqDec A} V (m: pfun A V) a : pfun A V :=
  fun a' => if AEQ a a' then None else m a'.

Lemma remove_eq : forall A {AEQ: EqDec A} V (m: pfun A V) a,
    remove m a a = None.
Proof.
  unfold remove; intros.
  destruct_match; auto.
Qed.

Lemma remove_neq : forall A {AEQ: EqDec A} V (m: pfun A V) a a',
    a <> a' ->
    remove m a a' = m a'.
Proof.
  unfold remove; intros.
  destruct_match; auto.
Qed.

Hint Rewrite remove_eq : upd.
Hint Rewrite remove_neq using (solve [ auto ]) : upd.

Theorem remove_upd : forall A {AEQ:EqDec A} V (m: pfun A V) a v,
    m a = Some v ->
    m = upd (remove m a) a v.
Proof.
  intros.
  extensionality a'.
  destruct (AEQ a a'); subst; autorewrite with upd; auto.
Qed.

Theorem remove_none : forall A {AEQ:EqDec A} V (m: pfun A V) a,
    m a = None ->
    remove m a = m.
Proof.
  unfold remove; intros.
  extensionality a'.
  destruct_match.
Qed.

Theorem upd_remove : forall A {AEQ:EqDec A} V (m: pfun A V) a v,
    remove (upd m a v) a = remove m a.
Proof.
  unfold remove; intros; extensionality a'.
  destruct_match; autorewrite with upd; auto.
Qed.

Hint Rewrite upd_remove : upd.
Hint Rewrite remove_none using (solve [ auto ]) : upd.

Theorem upd_remove_commute : forall A {AEQ:EqDec A} V (m: pfun A V) a v a',
    a <> a' ->
    upd (remove m a) a' v = remove (upd m a' v) a.
Proof.
  unfold upd, remove; intros; extensionality a''.
  repeat destruct_match.
Qed.
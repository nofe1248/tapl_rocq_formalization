(** * Chapter 3: Untyped Arithmetic Expressions *)

From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Module UntypedArithExpr.

Create HintDb untyped_db.

Inductive tm : Type :=
  | tm_true    : tm                    (* Constant true *)
  | tm_false   : tm                    (* Constant false *)
  | tm_if      : tm -> tm -> tm -> tm  (* Conditional *)
  | tm_zero    : tm                    (* Constant zero*)
  | tm_succ    : tm -> tm              (* Successor *)
  | tm_pred    : tm -> tm              (* Predecessor *)
  | tm_iszero  : tm -> tm              (* Zero test *)
.

Hint Constructors tm : untyped_db.

Declare Custom Entry untyped.
Declare Scope untyped_scope.

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom untyped at level 200,
                 x custom untyped,
                 y custom untyped,
                 z custom untyped at level 200,
                 left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom untyped at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom untyped at level 0).
Notation "'0'"      := tm_zero (in custom untyped at level 0).
Notation "'succ' t" := (tm_succ t)
  (in custom untyped at level 0, t custom untyped at level 0).
Notation "'pred' t" := (tm_pred t)
  (in custom untyped at level 0, t custom untyped at level 0).
Notation "'iszero' t" := (tm_iszero t)
  (in custom untyped at level 0, t custom untyped at level 0).

Notation "$( x )" := x (in custom untyped at level 0, x constr, only parsing) : untyped_scope.
Notation "x" := x (in custom untyped at level 0, x constr at level 0) : untyped_scope.
Notation "<{ e }>" := e (e custom untyped at level 200) : untyped_scope.
Notation "( x )" := x (in custom untyped at level 0, x custom untyped) : untyped_scope.

Open Scope untyped_scope.

Example syntax_example_1 :
  <{ if iszero 0 then true else false }> =
  tm_if (tm_iszero tm_zero) tm_true tm_false.
Proof. reflexivity. Qed.

Example syntax_example_2 :
  <{ pred (succ 0) }> =
  tm_pred (tm_succ tm_zero).
Proof. reflexivity. Qed.

Inductive boolean_value : tm -> Prop :=
  | v_true :
      boolean_value <{ true }>
  | v_false :
      boolean_value <{ false }>
.

Inductive numeric_value : tm -> Prop :=
  | v_zero :
      numeric_value <{ 0 }>
  | v_succ : forall t, 
      numeric_value t -> 
      numeric_value <{ succ $(t) }>
.

Definition value t : Prop :=
  boolean_value t \/ numeric_value t.

Hint Constructors boolean_value : untyped_db.
Hint Constructors numeric_value : untyped_db.
Hint Unfold value : untyped_db.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | E_IfTrue : forall t2 t3,
      <{ if true then t2 else t3 }> --> t2
  | E_IfFalse : forall t2 t3,
      <{ if false then t2 else t3 }> --> t3
  | E_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{ if t1 then t2 else t3 }> --> <{ if t1' then t2 else t3 }>
  | E_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | E_PredZero :
      <{ pred 0 }> --> <{ 0 }>
  | E_PredSucc : forall nv,
      numeric_value nv ->
      <{ pred (succ nv) }> --> <{ nv }>
  | E_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | E_IsZeroZero :
      <{ iszero 0 }> --> <{ true }>
  | E_IsZeroSucc : forall nv,
      numeric_value nv ->
      <{ iszero (succ nv) }> --> <{ false }>
  | E_IsZero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
  
  where " t '-->' t' " := (step t t').

Hint Constructors step : untyped_db.

Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form t :=
  normal_form step t.

Hint Unfold step_normal_form : untyped_db.
Hint Unfold normal_form : untyped_db.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z
.

Hint Constructors multi : untyped_db.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - assumption.
    - apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.

Example small_step_example_1 :
  <{ if (if true then true else false) then pred (succ 0) else 0 }> -->*
  <{ 0 }>.
Proof. 
  eapply multi_step.
  - apply E_If.
    apply E_IfTrue.
  - eapply multi_step.
    + apply E_IfTrue.
    + eapply multi_step.
      * apply E_PredSucc.
        apply v_zero.
      * apply multi_refl.
Qed.

Example small_step_example_1' :
  <{ if (if true then true else false) then pred (succ 0) else 0 }> -->*
  <{ 0 }>.
Proof. eauto 10 with untyped_db. Qed.

Theorem bv_is_nf : forall t,
  boolean_value t -> step_normal_form t.
Proof.
  intros t Hbv [t' Hstep].
  induction Hstep; inversion Hbv.
Qed.

Theorem nv_is_nf : forall t,
  numeric_value t -> step_normal_form t.
Proof.
  intros t Hnv [t' Hstep].
  induction Hstep; inversion Hnv; auto.
Qed.

Theorem value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form, normal_form.
  intros t Hvalue.
  destruct Hvalue as [Hbv | Hnv].
  - exact (bv_is_nf _ Hbv).
  - exact (nv_is_nf _ Hnv).
Qed.

Definition stuck t :=
  ~ value t /\ step_normal_form t.

Theorem nf_not_implies_value : exists t,
  ~ (step_normal_form t -> value t).
Proof.
  exists <{ succ true }>.
  intros Hc.
  assert (step_normal_form <{ succ true }>) as Hnf.
  { 
    unfold step_normal_form, normal_form.
    intros [t' Hstep].
    inversion Hstep.
    subst.
    inversion H0.
  }
  apply Hc in Hnf.
  destruct Hnf as [Hbv | Hnv].
  - inversion Hbv.
  - inversion Hnv.
    inversion H0.
Qed.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem step_deterministic :
  deterministic step.
Proof with eauto with untyped_db.
  unfold deterministic.
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst...
    inversion H3.
  - inversion Hy2; subst...
    inversion H3.
  - inversion Hy2; subst; try solve [inversion Hy1].
    f_equal.
    apply IHHy1.
    exact H3.
  - inversion Hy2; subst.
    f_equal.
    apply IHHy1.
    exact H0.
  - inversion Hy2; subst...
    inversion H0.
  - inversion Hy2; subst...
    assert (value <{ succ nv }>) as Hv.
    { right. apply v_succ. exact H. }
    apply value_is_nf in Hv.
    exfalso.
    apply Hv.
    exists t1'.
    exact H1.
  - inversion Hy2; subst.
    + inversion Hy1.
    + assert (value <{ succ y2 }>) as Hv.
      { right. apply v_succ. exact H0. }   
      apply value_is_nf in Hv.
      exfalso.
      apply Hv.
      exists t1'.
      exact Hy1.
    + f_equal.
      apply IHHy1.
      exact H0.
  - inversion Hy2; subst...
    inversion H0.
  - inversion Hy2; subst...
    assert (value <{ succ nv }>) as Hv.
    { right. apply v_succ. exact H. }   
    apply value_is_nf in Hv.
    exfalso.
    apply Hv.
    exists t1'.
    exact H1.
  - inversion Hy2; subst...
    + inversion Hy1.
    + assert (value <{ succ nv }>) as Hv.
      { right. apply v_succ. exact H0. }
      apply value_is_nf in Hv.
      exfalso.
      apply Hv.
      exists t1'.
      exact Hy1.
    + f_equal.
      apply IHHy1.
      exact H0.
Qed.

Lemma multi_if : forall t1 t1' t2 t3,
  t1 -->* t1' ->
  <{ if t1 then t2 else t3 }> -->* <{ if t1' then t2 else t3 }>.
Proof.
  intros t1 t1' t2 t3 Ht1.
  induction Ht1; eauto with untyped_db.
Qed.

Lemma multi_succ : forall t t',
  t -->* t' ->
  <{ succ t }> -->* <{ succ t' }>.
Proof.
  intros t t' Ht.
  induction Ht; eauto with untyped_db.
Qed.

Lemma multi_pred : forall t t',
  t -->* t' ->
  <{ pred t }> -->* <{ pred t' }>.
Proof.
  intros t t' Ht.
  induction Ht; eauto with untyped_db.
Qed.

Lemma multi_iszero : forall t t',
  t -->* t' ->
  <{ iszero t }> -->* <{ iszero t' }>.
Proof.
  intros t t' Ht.
  induction Ht; eauto with untyped_db.
Qed.

Reserved Notation " t '==>' t' " (at level 40).

Inductive big_step : tm -> tm -> Prop :=
  | B_Value : forall v,
      value v ->
      v ==> v
  | B_IfTrue : forall t1 t2 t3 v2,
      t1 ==> <{ true }> ->
      t2 ==> v2 ->
      <{ if t1 then t2 else t3 }> ==> v2
  | B_IfFalse : forall t1 t2 t3 v3,
      t1 ==> <{ false }> ->
      t3 ==> v3 ->
      <{ if t1 then t2 else t3 }> ==> v3
  | B_Succ : forall t1 nv1,
      numeric_value nv1 ->
      t1 ==> nv1 ->
      <{ succ t1 }> ==> <{ succ nv1 }>
  | B_PredZero : forall t1,
      t1 ==> <{ 0 }> ->
      <{ pred t1 }> ==> <{ 0 }>
  | B_PredSucc : forall t1 nv1,
      numeric_value nv1 ->
      t1 ==> <{ succ nv1 }> ->
      <{ pred t1 }> ==> nv1
  | B_IsZeroZero : forall t1,
      t1 ==> <{ 0 }> ->
      <{ iszero t1 }> ==> <{ true }>
  | B_IsZeroSucc : forall t1 nv1,
      numeric_value nv1 ->
      t1 ==> <{ succ nv1 }> ->
      <{ iszero t1 }> ==> <{ false }>

  where " t '==>' t' " := (big_step t t').

Hint Constructors big_step : untyped_db.

Example eval_bigstep_example_1 :
  <{ if (if true then true else false) then pred (succ 0) else 0 }> ==>
  <{ 0 }>.
Proof. 
  apply B_IfTrue.
  - apply B_IfTrue; apply B_Value; left; constructor.
  - apply B_PredSucc; constructor.
    right.
    repeat constructor.
Qed.

Example eval_bigstep_example_1' :
  <{ if (if true then true else false) then pred (succ 0) else 0 }> ==>
  <{ 0 }>.
Proof. eauto 20 with untyped_db. Qed.

Lemma big_step_value : forall t v,
  t ==> v -> value v.
Proof with eauto with untyped_db.
  intros t v Hbs.
  induction Hbs...
Qed.

Lemma step_preserves_big_step : forall t t' v,
  t --> t' ->
  t' ==> v ->
  t ==> v.
Proof with eauto with untyped_db.
  intros t t' v Hst.
  generalize dependent v.
  induction Hst; intros...
  - inversion H; subst...
    inversion H0. inversion H1. inversion H1.
  - inversion H; subst...
    inversion H0; inversion H1; subst...
    apply B_Succ...
  - inversion H. subst...
  - inversion H0; subst; inversion H; subst...
  - inversion H; subst...
    inversion H0; inversion H1.
  - inversion H. subst.
    apply B_IsZeroZero, B_Value. right. apply v_zero.
  - inversion H0. subst.
    eapply B_IsZeroSucc...
  - inversion H; subst...
    inversion H0; inversion H1.
Qed.

Theorem big_step_complete : forall t v,
  value v ->
  t -->* v ->
  t ==> v.
Proof.
  intros t v Hvalue Hst.
  induction Hst.
  - apply B_Value.
    assumption.
  - pose proof (IHHst Hvalue) as Hyz.
    pose proof (step_preserves_big_step _ _ _ H Hyz) as Hxz.
    assumption.
Qed.

Theorem big_step_sound : forall t v,
  t ==> v ->
  t -->* v.
Proof with eauto with untyped_db.
  intros t v Hbs.
  induction Hbs...
  - eapply multi_trans.
    + apply multi_if. exact IHHbs1.
    + eapply multi_step... 
  - eapply multi_trans.
    + apply multi_if. exact IHHbs1.
    + eapply multi_step... 
  - apply multi_succ. exact IHHbs.
  - eapply multi_trans.
    + apply multi_pred. exact IHHbs.
    + eapply multi_step...
  - eapply multi_trans.
    + apply multi_pred. exact IHHbs.
    + eapply multi_step...
  - eapply multi_trans.
    + apply multi_iszero. exact IHHbs.
    + eapply multi_step...
  - eapply multi_trans.
    + apply multi_iszero. exact IHHbs.
    + eapply multi_step...
Qed.

Theorem big_step_and_small_step_coincide : forall t v,
  value v -> t ==> v <-> t -->* v.
Proof.
  intros. split.
  + apply big_step_sound.
  + apply big_step_complete. assumption.
Qed.

End UntypedArithExpr.

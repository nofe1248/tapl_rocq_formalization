(** * Chapter 4: Untyped Arithmetic Expression Implementation *)

From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Tapl Require Import UntypedArithExpr. Import UntypedArithExpr.

Module UntypedArithExprImpl.
Open Scope untyped_scope.

Declare Scope eval_scope.
Notation "'nat!' n" := (Some (inl n))
  (at level 0, n at level 99) : eval_scope.
Notation "'bool!' b" := (Some (inr b))
  (at level 0, b at level 99) : eval_scope.
Notation "x '<-' e ';;' e'" :=
  (match e with Some x => e' | None => None end)
  (at level 100, e at next level, right associativity) : eval_scope.

Delimit Scope eval_scope with eval.
Open Scope eval_scope.

Fixpoint eval (t : tm) : option (nat + bool) :=
  match t with
  | tm_true => bool! true
  | tm_false => bool! false
  | tm_if t1 t2 t3 =>
      b <- eval t1;;
      match b with
      | inl _ => None
      | inr true => eval t2
      | inr false => eval t3
      end
  | tm_zero => nat! 0
  | tm_succ t1 =>
      n <- eval t1;;
      match n with
      | inl n' => nat! (S n')
      | inr _ => None
      end
  | tm_pred t1 =>
      n <- eval t1;;
      match n with
      | inl n' => nat! (Nat.pred n')
      | inr _ => None
      end
  | tm_iszero t1 =>
      n <- eval t1;;
      match n with
      | inl n' => bool! (Nat.eqb n' 0)
      | inr _ => None
      end
  end.

Example eval_example :
  eval <{ if (if true then true else false) then pred (succ 0) else 0 }> = 
  nat! 0.
Proof. reflexivity. Qed.

Fixpoint nat_to_tm (n : nat) : tm :=
  match n with
  | 0 => <{ 0 }>
  | S n' => <{ succ $(nat_to_tm n') }>
  end.

Definition result_to_tm (r : nat + bool) : tm :=
  match r with
  | inl n => nat_to_tm n
  | inr true => <{ true }>
  | inr false => <{ false }>
  end.

Lemma nat_to_tm_nv : forall n nv,
  nat_to_tm n = nv ->
  numeric_value nv.
Proof.
  induction n as [| n']; 
    intros nv Hres; simpl in Hres; subst.
  - constructor.
  - apply v_succ, IHn'. reflexivity.
Qed.

Lemma nat_to_tm_injective : forall n m,
  nat_to_tm n = nat_to_tm m -> n = m.
Proof.
  induction n as [| n' IH]; intros [| m] H; simpl in H; try discriminate.
  - reflexivity.
  - injection H as H.
    f_equal. apply IH. exact H.
Qed.

Lemma result_to_tm_injective : forall r1 r2,
  result_to_tm r1 = result_to_tm r2 -> r1 = r2.
Proof.
  intros [n1 | b1] [n2 | b2] H; simpl in H.
  - f_equal. eapply nat_to_tm_injective. exact H.
  - destruct b2; simpl in H;
      pose proof (nat_to_tm_nv n1 _ H) as Hnv; inversion Hnv.
  - destruct b1; simpl in H; symmetry in H;
      pose proof (nat_to_tm_nv n2 _ H) as Hnv; inversion Hnv.
  - destruct b1, b2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma result_to_tm_value : forall r v,
  result_to_tm r = v ->
  value v.
Proof.
  intros r v Hres.
  destruct r as [n | b]; simpl in Hres.
  - right.
    eapply nat_to_tm_nv, Hres.
  - destruct b; subst; left; constructor.
Qed.

Lemma result_to_tm_inversion_true : forall r,
  result_to_tm r = <{ true }> ->
  r = (inr true).
Proof.
  intros r H.
  destruct r; simpl in H.
  - destruct n; discriminate H.
  - destruct b; try discriminate.
    reflexivity.
Qed.

Lemma result_to_tm_inversion_false : forall r,
  result_to_tm r = <{ false }> ->
  r = (inr false).
Proof.
  intros r H.
  destruct r; simpl in H.
  - destruct n; discriminate H.
  - destruct b; try discriminate.
    reflexivity.
Qed.

Lemma result_to_tm_inversion_0 : forall r,
  result_to_tm r = <{ 0 }> ->
  r = (inl 0).
Proof.
  intros r H.
  destruct r; simpl in H.
  - destruct n; try discriminate.
    reflexivity.
  - destruct b; discriminate.
Qed.

Lemma result_to_tm_inversion_succ : forall r nv,
  result_to_tm r = <{ succ nv }> ->
  exists n, r = (inl (S n)) /\ nat_to_tm n = nv.
Proof.
  intros r nv H.
  destruct r; simpl in H.
  - destruct n; try discriminate.
    exists n.
    simpl in H. injection H as H.
    split; simpl; auto.
  - destruct b; discriminate.
Qed.

Lemma result_to_tm_inversion_numeric : forall r nv,
  numeric_value nv ->
  result_to_tm r = nv ->
  exists n, r = inl n /\ nat_to_tm n = nv.
Proof.
  intros r nv Hv Hres.
  destruct r; simpl in Hv.
  - destruct n; simpl in Hres; subst.
    + exists 0. auto.
    + exists (S n). auto. 
  - destruct b; simpl in Hres; subst; inversion Hv.
Qed.

Theorem eval_sound : forall t r, 
  eval t = Some r -> t ==> result_to_tm r.
Proof with eauto with untyped_db.
  intros t r Heval.
  generalize dependent r.
  induction t; intros r Heval; simpl in Heval.
  - injection Heval as Heval.
    subst. simpl...
  - injection Heval as Heval.
    subst. simpl...
  - destruct (eval t1) as [[n | b] |] eqn:Hcond; simpl in Heval.
    + discriminate.
    + destruct b; simpl in Heval.
      * eapply B_IfTrue.
        --- specialize IHt1 with (inr true).
          simpl in IHt1. apply IHt1. reflexivity.
        --- apply IHt2. exact Heval.
      * eapply B_IfFalse.
        --- specialize IHt1 with (inr false).
          simpl in IHt1. apply IHt1. reflexivity.
        --- apply IHt3. exact Heval.
    + discriminate.
  - injection Heval as Heval.
    subst. simpl...
  - destruct (eval t) as [[n | b] |] eqn:He; 
    simpl in Heval; [| discriminate .. ].
    specialize IHt with (inl n). simpl in IHt.
    injection Heval as Heval. subst.
    eapply B_Succ...
    eapply nat_to_tm_nv.
    reflexivity.
  - destruct (eval t) as [[n | b] |] eqn:He; 
    simpl in Heval; [| discriminate .. ].
    destruct n as [| n']; simpl in Heval.
    + injection Heval as Heval. subst.
      eapply B_PredZero.
      specialize IHt with (inl 0).
      simpl in IHt. apply IHt. reflexivity.
    + injection Heval as Heval. subst.
      eapply B_PredSucc with (nv1 := nat_to_tm n').
      * eapply nat_to_tm_nv. reflexivity.
      * specialize IHt with (inl (S n')).
        simpl in IHt. apply IHt. reflexivity.
  - destruct (eval t) as [[n | b] |] eqn:He; 
    simpl in Heval; [| discriminate .. ].
    induction n; simpl in Heval.
    + injection Heval as Heval.
      subst. simpl.
      specialize IHt with (inl 0). simpl in IHt...
    + injection Heval as Heval.
      subst. simpl.
      eapply B_IsZeroSucc with (nv1 := nat_to_tm n).
      * eapply nat_to_tm_nv. reflexivity.
      * specialize IHt with (inl (S n)).
        simpl in IHt. apply IHt. reflexivity.
Qed.

Lemma value_eval : forall v,
  value v ->
  exists r, eval v = Some r /\ result_to_tm r = v.
Proof.
  intros v Hv.
  destruct Hv as [Hbv | Hnv].
  - inversion Hbv; subst.
    + exists (inr true). split; auto.
    + exists (inr false). split; auto.
  - induction Hnv.
    + exists (inl 0). split; auto.
    + destruct IHHnv as [r [H Hr]].
      destruct r.
      * exists (inl (S n)).
        split.
        --- simpl. rewrite H. reflexivity.
        --- simpl in *. rewrite Hr. reflexivity.
      * simpl in Hr.
        destruct b; subst; inversion Hnv.
Qed.

Theorem eval_complete : forall t v, 
  t ==> v ->
  exists r, eval t = Some r /\ result_to_tm r = v.
Proof with eauto with untyped_db.
  intros t v Hbs.
  induction Hbs.
  - pose proof (value_eval _ H) as [r [Heval Hres]].
    exists r.
    split; assumption.
  - destruct IHHbs1 as [x [H1 Hr1]], IHHbs2 as [y [H2 Hr2]].
    exists y.
    split...
    simpl. rewrite H1, <- H2. simpl in Hr1.
    apply result_to_tm_inversion_true in Hr1.
    rewrite Hr1. reflexivity.
  - destruct IHHbs1 as [x [H1 Hr1]], IHHbs2 as [y [H2 Hr2]].
    exists y.
    split...
    simpl. rewrite H1, <- H2. simpl in Hr1.
    apply result_to_tm_inversion_false in Hr1.
    rewrite Hr1. reflexivity.
  - destruct IHHbs as [x [He Hr]].
    apply result_to_tm_inversion_numeric in Hr...
    destruct Hr as [n [Hx Hn]].
    exists (inl (S n)).
    split.
    + simpl. rewrite He. rewrite Hx. reflexivity.
    + simpl. rewrite Hn. reflexivity.
  - destruct IHHbs as [x [He Hr]].
    exists x.
    split...
    simpl. rewrite He.
    apply result_to_tm_inversion_0 in Hr.
    rewrite Hr. reflexivity.
  - destruct IHHbs as [x [He Hr]].
    apply result_to_tm_inversion_succ in Hr.
    destruct Hr as [n [Hx Hn]].
    exists (inl n).
    split...
    simpl. rewrite He, Hx. reflexivity.
  - destruct IHHbs as [x [He Hr]].
    exists (inr true).
    split...
    simpl. rewrite He.
    apply result_to_tm_inversion_0 in Hr.
    rewrite Hr. reflexivity.
  - destruct IHHbs as [x [He Hr]].
    apply result_to_tm_inversion_succ in Hr.
    destruct Hr as [n [Hx Hn]].
    exists (inr false).
    split...
    simpl. rewrite He, Hx. reflexivity.
Qed.

Theorem eval_correct : forall t r,
  eval t = Some r <-> t ==> result_to_tm r.
Proof with eauto with untyped_db.
  split.
  - apply eval_sound.
  - intros Hbs.
    destruct (eval_complete _ _ Hbs) as [r' [Heval Hresult]].
    apply result_to_tm_injective in Hresult.
    subst r'.
    exact Heval.
Qed.

End UntypedArithExprImpl.

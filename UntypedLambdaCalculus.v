(** * Chapter 5: Untyped Lambda Calculus *)

From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import FSets.FSetAVL.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Structures.OrderedTypeEx.

Module StringSet := FSetAVL.Make(String_as_OT).

Module UntypedLambda.

Create HintDb untyped_lam_db.

Inductive tm : Type :=
  | tm_var  : string -> tm
  | tm_app  : tm -> tm -> tm
  | tm_abs  : string -> tm -> tm
.

Hint Constructors tm : untyped_lam_db.

Declare Scope ulc_scope.
Open Scope ulc_scope.

Declare Custom Entry ulc_tm.

Notation "$( x )" := x (in custom ulc_tm at level 0, x constr, only parsing) : ulc_scope.
Notation "x" := x (in custom ulc_tm at level 0, x constr at level 0) : ulc_scope.
Notation "<{ e }>" := e (e custom ulc_tm at level 200) : ulc_scope.
Notation "( x )" := x (in custom ulc_tm at level 0, x custom ulc_tm) : ulc_scope.

Notation "x y" := (tm_app x y) (in custom ulc_tm at level 10, left associativity) : ulc_scope.
Notation "\ x , y" :=
  (tm_abs x y) (in custom ulc_tm at level 200, x global,
                   y custom ulc_tm at level 200,
                   left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Fixpoint fv (t:tm) : StringSet.t :=
  match t with
  | tm_var x => StringSet.singleton x
  | <{t1 t2}> => StringSet.union (fv t1) (fv t2)
  | <{\x , y}> => StringSet.remove x (fv y)
  end.

Reserved Notation "'[' x ':=' s ']' t" 
  (in custom ulc_tm at level 5, x global, s custom ulc_tm,
      t custom ulc_tm at next level, right associativity).

Fixpoint subst (x:string) (s t:tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ t1 t2 }> =>
      <{ [x:=s] t1 [x:=s] t2}>
  | <{ \y , b }> =>
      if String.eqb x y then t else <{ \y , [x:=s] b }>
  end

  where "'[' x ':=' s ']' t" := (subst x s t) (in custom ulc_tm).

Inductive value : tm -> Prop :=
  | v_abs : forall x y,
      value <{ \x , y }>
.

Hint Constructors value : untyped_lam_db.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | E_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>
  | E_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ v1 t2 }> --> <{ v1 t2' }>
  | E_AppAbs : forall x t v,
      value v ->
      <{ (\x , t) v }> --> <{ [x:=v] t }>

  where "t '-->' t'" := (step t t').

Hint Constructors step : untyped_lam_db.

Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form t :=
  normal_form step t.

Hint Unfold step_normal_form : untyped_lam_db.
Hint Unfold normal_form : untyped_lam_db.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z
.

Hint Constructors multi : untyped_lam_db.

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
    - eapply multi_step.
      + apply H0.
      + apply IHG. assumption.
Qed.

(* [normalize] tactic from the [Smallstep] 
    chapter of *Programming Language Foundations* *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10 with untyped_lam_db; fail) | simpl]);
  apply multi_refl.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition t : string := "t".
Definition f : string := "f".
Definition b : string := "b".
Definition s : string := "s".
Hint Unfold x : untyped_lam_db.
Hint Unfold y : untyped_lam_db.
Hint Unfold z : untyped_lam_db.
Hint Unfold t : untyped_lam_db.
Hint Unfold f : untyped_lam_db.
Hint Unfold b : untyped_lam_db.
Hint Unfold s : untyped_lam_db.

Abbreviation tru :=
  <{ \t, \f, t }>.

Abbreviation fls :=
  <{ \t, \f, f }>.

Abbreviation cand :=
  <{ \x, \y, x y fls }>.

Abbreviation cor :=
  <{ \x, \y, x tru y }>.

Abbreviation cnot :=
  <{ \x, x fls tru }>.

Example church_boolean_example_1 :
  <{ cand tru fls }> -->* <{ fls }>.
Proof. normalize. Qed.

Example church_boolean_example_2 :
  <{ cnot (cor (cand tru fls) tru) }> -->* <{ fls }>.
Proof. normalize. Qed.

Abbreviation cpair :=
  <{ \x, \y, \b, b x y }>.

Abbreviation cfst :=
  <{ \x, x tru }>.

Abbreviation csnd :=
  <{ \x, x fls }>.

Example church_pair_example_1 :
  <{ cfst (csnd (cpair tru (cpair tru fls))) }> -->* <{ tru }>.
Proof. normalize. Qed.

Abbreviation c0 :=
  <{ \s, \z, z }>.
Abbreviation c1 :=
  <{ \s, \z, s z }>.
Abbreviation c2 :=
  <{ \s, \z, s (s z) }>.
Abbreviation c3 :=
  <{ \s, \z, s (s (s z)) }>.
Abbreviation c4 :=
  <{ \s, \z, s (s (s (s z))) }>.
Abbreviation c5 :=
  <{ \s, \z, s (s (s (s (s z)))) }>.
Abbreviation c6 :=
  <{ \s, \z, s (s (s (s (s (s z))))) }>.
Abbreviation c7 :=
  <{ \s, \z, s (s (s (s (s (s (s z)))))) }>.
Abbreviation c8 :=
  <{ \s, \z, s (s (s (s (s (s (s (s z))))))) }>.

Abbreviation csucc :=
  <{ \x, \s, \z, s (x s z) }>.

Abbreviation cplus :=
  <{ \x, \y, \s, \z, x s (y s z) }>.

End UntypedLambda.
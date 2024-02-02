Require Import String.
Require Import List.
Require Import Arith. (* Import the Nat module *)

Inductive Expression :=
| Num (n: nat)
| Var (v: string)
| Plus (l: Expression) (r: Expression)
| Let (var: string) (initializer: Expression) (result: Expression).

Inductive EvalResult :=
| Ok (n: nat)
| Error.

Fixpoint lookup_variable (var: string) (env: list (string * nat)) : option nat :=
  match env with
  | nil => None
  | (v, n) :: rest => if string_dec var v then Some n else lookup_variable var rest
  end.

Fixpoint evaluate_with_env (expr: Expression) (env: list (string * nat)) : EvalResult :=
  match expr with
  | Num n => Ok n
  | Var v => match lookup_variable v env with
             | Some n => Ok n
             | _ => Error
             end
  | Plus l r => match (evaluate_with_env l env, evaluate_with_env r env) with
                | (Ok n1, Ok n2) => Ok (n1 + n2)
                | _ => Error
                end
  | Let var initializer result =>
    match evaluate_with_env initializer env with
    | Ok n => evaluate_with_env result ((var, n) :: env)
    | _ => Error
    end
  end.

Definition evaluate (expr: Expression) : EvalResult :=
  evaluate_with_env expr nil.

Inductive IsFree (var: string) : Expression -> Prop :=
| IsFreeVar: IsFree var (Var var)
| IsFreePlusLeft (e1: Expression) (e2: Expression): IsFree var e1 ->
IsFree var (Plus e1 e2)
| IsFreePlusRight (e1: Expression) (e2: Expression): IsFree var e2
-> IsFree var (Plus e1 e2)
| IsFreeLetInit (other_var: string) (e1: Expression) (e2:
Expression):
IsFree var e1 -> IsFree var (Let other_var e1 e2)
| IsFreeLetBody (other_var: string) (e1: Expression) (e2:
Expression):
IsFree var e2 -> ~ var = other_var -> IsFree var (Let
other_var e1 e2).

Lemma evaluate_plus: forall n1 n2 e1 e2, evaluate e1 = Ok n1 ->
evaluate e2 = Ok n2
-> evaluate (Plus e1 e2) = Ok (n1 + n2).
Proof.
intros n1 n2 e1 e2.
intros H1 H2.
unfold evaluate in *.
simpl.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma evaluate_plus_comm: forall e1 e2, evaluate (Plus e1 e2) =
evaluate (Plus e2 e1).
Proof.
intros e1 e2.
unfold evaluate.
simpl.
destruct evaluate_with_env.
destruct evaluate_with_env.
- rewrite Nat.add_comm. reflexivity.
- reflexivity.
- destruct evaluate_with_env.
  +reflexivity.
  +reflexivity.
Qed.

Lemma extended_env_error_implies_env_error: forall e2 var n,
evaluate_with_env e2 ((var, n) :: nil) = Error -> evaluate e2 = Error.
Proof.
Admitted.

Lemma error_implies_free: forall e,
 evaluate e = Error -> exists v : string, IsFree v e.
intro e. intro H. induction e.
  + inversion H.
  + exists v. apply IsFreeVar. 
  + destruct (evaluate e1) eqn:E1.
    -- destruct (evaluate e2) eqn:E2. 
      ++ pose proof (evaluate_plus n n0 e1 e2).
         rewrite E1 in H0. rewrite E2 in H0.
       rewrite H in H0. discriminate H0. reflexivity. reflexivity.
      ++ assert (exists v : string, IsFree v e2). apply IHe2. reflexivity. 
          destruct H0 as [v1 F]. exists v1. apply IsFreePlusRight. exact F.
    -- assert (exists v : string, IsFree v e1). apply IHe1. reflexivity. 
          destruct H0 as [v1 F]. exists v1. apply IsFreePlusLeft. exact F.
  + destruct (evaluate e1) eqn:E1.
    -- clear IHe1. unfold evaluate in H. simpl in H. unfold evaluate in E1. rewrite E1 in H.
      clear E1. destruct (evaluate e2) eqn:Eq2.
      ++ clear IHe2. pose proof (extended_env_error_implies_env_error e2 var n).
          assert (evaluate e2 = Error). rewrite H0. reflexivity. exact H.
           rewrite H1 in Eq2. discriminate.
      ++ assert (exists v : string, IsFree v e2). apply IHe2. reflexivity. clear IHe2.
         destruct H0 as[v1 F]. exists v1. apply IsFreeLetBody. exact F.
          unfold not. intros HF. rewrite HF in F. clear HF v1. 
admit.
    -- assert (exists v : string, IsFree v e1). apply IHe1. reflexivity.
        destruct H0 as [v1 H0']. exists v1. apply IsFreeLetInit. exact H0'.
Admitted.

Lemma Free_implies_error : forall e,
(exists v : string, IsFree v e) -> evaluate e = Error.
Proof.
intros e.
intro H.  induction e.
- destruct H as [v F]. inversion F.
- destruct H as [v0 F].
destruct (lookup_variable v nil) as [n |] eqn:L. discriminate.
unfold evaluate. unfold evaluate_with_env. rewrite L. reflexivity.
- destruct H as [v F]. unfold evaluate. simpl. destruct (evaluate e1) eqn:E1.
  + unfold evaluate in E1. rewrite E1. assert (evaluate e2 = Error).
    -- rewrite IHe2. reflexivity. clear IHe1. admit.
    -- unfold evaluate in H. rewrite H. reflexivity.
  + unfold evaluate in E1. rewrite E1. reflexivity.
- destruct H as [v F]. unfold evaluate. simpl. destruct (evaluate e1) eqn:E1.
  + unfold evaluate in E1. rewrite E1. admit.
  + unfold evaluate in E1. rewrite E1. reflexivity.
Admitted.

Lemma evaluate_error: forall e, evaluate e = Error <-> exists v,
IsFree v e.
Proof.
intros e. split.
- apply error_implies_free.
- apply Free_implies_error.
Qed.


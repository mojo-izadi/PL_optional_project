Require Import String.
Require Import List.
Require Import Arith. (* Import the Nat module *)
Require Import Field.

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
             | None => Error
             end
  | Plus l r => match (evaluate_with_env l env, evaluate_with_env r env) with
                | (Ok n1, Ok n2) => Ok (n1 + n2)
                | _ => Error
                end
  | Let var initializer result =>
    match evaluate_with_env initializer env with
    | Ok n => evaluate_with_env result ((var, n) :: env)
    | Error => Error
    end
  end.

Definition evaluate (expr: Expression) : EvalResult :=
  evaluate_with_env expr nil.

Example test1: evaluate (Let "y" (Num 3) (Plus (Var "x") (Plus (Num 1) (Num 1)))) = Error.
Proof.
reflexivity.
Qed.

Example test2: evaluate (Let "x" (Plus (Num 1) (Num 7))(Let "y" (Num 3) (Plus (Var "y") (Plus (Var "x") (Num 1))))) = Ok 12.
Proof.
simpl.
reflexivity.
Qed.

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
unfold evaluate in *.
simpl.
destruct evaluate_with_env.
destruct evaluate_with_env.
-simpl. rewrite Nat.add_comm. reflexivity.
-reflexivity.
-simpl. destruct evaluate_with_env.
  +reflexivity.
  +reflexivity.
Qed.


Lemma evaluate_error: forall e, evaluate e = Error <-> exists v,
IsFree v e.
Proof.
intros e. split.
- intros H. induction e.
  + destruct IsFree.
  +
  +
  +
simpl.
reflexivity.
Qed.



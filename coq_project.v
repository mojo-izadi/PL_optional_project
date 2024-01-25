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
simpl.
reflexivity.
Qed.

Example test2: evaluate (Let "x" (Plus (Num 1) (Num 7))(Let "y" (Num 3) (Plus (Var "y") (Plus (Var "x") (Num 1))))) = Ok 12.
Proof.
simpl.
reflexivity.
Qed.



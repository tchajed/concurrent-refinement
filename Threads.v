Require Arith.
Require Import Prog.

Definition EqDec A := forall (x y:A), {x=y}+{x<>y}.
Existing Class EqDec.

Instance tid_EqDec : EqDec TID := PeanoNat.Nat.eq_dec.

Definition pfun A V := A -> option V.

Definition upd A {AEQ: EqDec A} V (m: pfun A V) a v : pfun A V :=
  fun a' => if AEQ a a' then Some v else m a'.

Section Threads.

  Variable act : Actions.
  Variable sem: ActionSem act.

  Inductive YieldOutcome T :=
  | Completed : state sem -> T -> YieldOutcome T
  | Yielded : forall T', state sem -> prog act T' -> YieldOutcome T
  | YieldError : YieldOutcome T.
  Arguments YieldError {T}.
  Arguments Yielded {T T'} s p.

  Inductive execSection : forall T, state sem -> prog act T ->
                               YieldOutcome T -> Prop :=
  | ExecSectionRet : forall s T (v:T),
      execSection s (Ret act v) (Completed s v)
  | ExecSectionIo : forall s a r s',
      act_step sem s a (r, s') ->
      execSection s (Io act a) (Completed s' r)
  | ExecSectionIoError : forall s a,
      act_error sem s a ->
      execSection s (Io act a) YieldError
  | ExecSectionYield : forall s,
      execSection s (Yield act) (Yielded s (Ret act tt))
  | ExecSectionBindCompleted : forall T T' (p1: prog act T') (p2: T' -> prog act T)
                                 s s' v out,
      execSection s p1 (Completed s' v) ->
      execSection s' (p2 v) out ->
      execSection s (Bind p1 p2) out
  | ExecSectionBindYield : forall T T' (p1: prog act T') (p2: T' -> prog act T)
                                 s s' T'' (p': prog act T''),
      execSection s p1 (Yielded s' p') ->
      execSection s (Bind p1 p2) (Yielded s' p').

  Definition Env := pfun TID {T:Type & prog act T}.

  Inductive out_prog_is T : YieldOutcome T ->
                            state sem -> {T:Type & prog act T} -> Prop :=
  | CompletedProg : forall s v,
      out_prog_is (Completed s v) s (existT _ _ (Ret _ v))
  | YieldedProg : forall s T' (p: prog _ T'),
      out_prog_is (Yielded s p) s (existT _ _ p).

  Inductive envExec : state sem -> Env -> state sem -> Env -> Prop :=
  | EnvExecDone : forall s env,
      (forall tid, match env tid with
              | Some (existT _ _ p) => exists v, p = Ret act v
              | None => True
              end) ->
      envExec s env s env
  | EnvExecStep : forall s env tid T (p: prog act T) out
                    s' p' s'' env'',
      env tid = Some (existT _ _ p) ->
      execSection s p out ->
      out_prog_is out s' p' ->
      envExec s' (upd env tid p') s'' env'' ->
      envExec s env s'' env''.

End Threads.
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
  | Yielded : state sem -> prog act T -> YieldOutcome T
  | YieldError : YieldOutcome T.
  Arguments YieldError {T}.

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
                                 s s' p1',
      execSection s p1 (Yielded s' p1') ->
      execSection s (Bind p1 p2) (Yielded s' (Bind p1' p2)).

  Definition Env := pfun TID {T:Type & prog act T}.

  Inductive out_prog_is T : YieldOutcome T ->
                            state sem -> {T:Type & prog act T} -> Prop :=
  | CompletedProg : forall s v,
      out_prog_is (Completed s v) s (existT _ _ (Ret _ v))
  | YieldedProg : forall s p,
      out_prog_is (Yielded s p) s (existT _ _ p).

  (* TODO: should really have an error output *)
  Inductive envExec : state sem -> Env -> state sem -> Env -> Prop :=
  | EnvExecDone : forall s env,
      (forall tid, match env tid with
              | Some (existT _ _ p) => exists v, p = Ret act v
              | None => True
              end) ->
      envExec s env s env
  | EnvExecStep : forall s env tid T (p: prog act T),
      env tid = Some (existT _ _ p) ->
      forall out,
        execSection s p out ->
        forall s' p',
          (* out_prog_is masks errors in out *)
          out_prog_is out s' p' ->
          forall s'' env'',
            envExec s' (upd env tid p') s'' env'' ->
            envExec s env s'' env''.

  Inductive texec (tid:TID) :
    Env -> forall T, state sem * state sem -> prog act T ->
               Env -> outcome sem T -> Prop :=
  | TexecComplete : forall env s_i s T (p: prog _ T) s' v,
      execSection s p (Completed s' v) ->
      texec tid env (s_i, s) p env (Finished _ (s_i, s') v)
  | TexecYield : forall env s_i s T (p: prog _ T),
      forall s' p',
        execSection s p (Yielded s' p') ->
        forall s'' env',
          envExec s' env s'' env' ->
          forall env'' out,
            texec tid env' (s'', s'') p' env'' out ->
            texec tid env (s_i, s) p env'' out
  | TexecError : forall env s_i s T (p: prog _ T),
      execSection s p YieldError ->
      texec tid env (s_i, s) p env (Error _ _).

End Threads.
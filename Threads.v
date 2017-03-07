Require Import Prog.
Require Import PFun.
Require Import Automation.

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

  Notation "'witness' x" := (existT _ _ x) (at level 30).

  Inductive out_prog_is T : YieldOutcome T ->
                            state sem -> {T:Type & prog act T} -> Prop :=
  | CompletedProg : forall s v,
      out_prog_is (Completed s v) s (witness (Ret _ v))
  | YieldedProg : forall s p,
      out_prog_is (Yielded s p) s (witness p).

  (* TODO: should really have an error output *)
  Inductive envExec : state sem -> Env -> state sem -> Env -> Prop :=
  | EnvExecDone : forall s env,
      (forall tid, match env tid with
              | Some (witness p) => exists v, p = Ret act v
              | None => True
              end) ->
      envExec s env s env
  | EnvExecStep : forall s env tid T (p: prog act T),
      env tid = Some (witness p) ->
      forall out,
        execSection s p out ->
        forall s' p',
          (* out_prog_is masks errors in out *)
          out_prog_is out s' p' ->
          forall s'' env'',
            envExec s' (upd env tid p') s'' env'' ->
            envExec s env s'' env''.

  Inductive toutcome T :=
  | TFinished : state sem -> T -> toutcome T
  | TError.
  Arguments TError {T}.

  Inductive texec (tid:TID) :
    Env -> forall T, state sem -> prog act T ->
               Env -> toutcome T -> Prop :=
  | TexecComplete : forall env s T (p: prog _ T) s' v,
      execSection s p (Completed s' v) ->
      texec tid env s p env (TFinished s' v)
  | TexecYield : forall env s T (p: prog _ T),
      forall s' p',
        execSection s p (Yielded s' p') ->
        forall s'' env',
          envExec s' env s'' env' ->
          forall env'' out,
            texec tid env' s'' p' env'' out ->
            texec tid env s p env'' out
  | TexecError : forall env s T (p: prog _ T),
      execSection s p YieldError ->
      texec tid env s p env TError.

  Hint Constructors texec execSection envExec.

  Theorem env_to_texec : forall s ts s'' ts' tid T (p: prog _ T),
      ts tid = Some (witness p) ->
      envExec s ts s'' ts' ->
      let env := remove ts tid in
      exists s' env' v,
        texec tid env s p env'
              (TFinished s' v) /\
        envExec s' (upd env' tid (witness (Ret _ v))) s'' ts'.
  Proof.
    intros.
    assert (ts = upd env tid (witness p)) as Hts.
    apply remove_upd; auto.
    rewrite Hts in *; clear Hts.
    assert (env tid = None).
    subst env; autorewrite with upd; auto.
    clear H.
    generalize dependent env.
    intros.
    remember (upd env tid (witness p)).
    induction H0; subst.
    - pose proof (H tid); autorewrite with upd in *; deex; subst.
      exists s, env, v.
      intuition eauto.
    - admit.
  Abort.

End Threads.

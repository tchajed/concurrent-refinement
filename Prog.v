Require Import Relation_Operators.
Require Import PFun.

Global Set Implicit Arguments.

Record Actions :=
  { action: Type;
    (* I'm going to regret this so much *)
    action_ret : action -> Type; }.

Record ActionSem (act:Actions) :=
  { state : Type;
    act_step: state -> forall a, (action_ret act a * state) -> Prop;
    act_error : state -> action act -> Prop; }.

Section Prog.

  Variable act:Actions.

  Inductive prog : Type -> Type :=
  | Io : forall a, prog (action_ret act a)
  | Yield : prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T' -> (T' -> prog T) -> prog T.

  Variable sem:ActionSem act.

  Definition TID := nat.
  Opaque TID.

  Inductive outcome T :=
  | Finished : (state sem)*(state sem) -> T -> outcome T
  | Error.
  Arguments Error {T}.

  Inductive act_sem :
    forall a, state sem * state sem -> outcome (action_ret act a) -> Prop :=
  | StepIo : forall a s_i s r s',
      act_step sem s a (r, s') ->
      act_sem a (s_i, s) (Finished (s_i, s') r)
  | StepIoError : forall a s_i s,
      act_error sem s a ->
      act_sem a (s_i, s) Error.

  Definition Protocol := TID -> state sem -> state sem -> Prop.
  Variable G : Protocol.
  Definition Rely : Protocol :=
    fun tid => clos_refl_trans _ (fun s s' =>
                                 exists tid', tid <> tid' /\
                                         G tid' s s').

  Inductive exec (tid:TID) : forall T, (state sem)*(state sem) -> prog T -> outcome T -> Prop :=
  | ExecIo : forall a st out,
      act_sem a st out ->
      exec tid st (Io a) out
  | ExecRet : forall T (v:T) st,
      exec tid st (Ret v) (Finished st v)
  | ExecBindFinished : forall T T'
                         (p1: prog T') (p2: T' -> prog T)
                         st st' r out,
      exec tid st p1 (Finished st' r) ->
      exec tid st' (p2 r) out ->
      exec tid st (Bind p1 p2) out
  | ExecBindError : forall T T'
                      (p1: prog T') (p2: T' -> prog T)
                      st,
      exec tid st p1 Error ->
      exec tid st (Bind p1 p2) Error
  | ExecYield : forall s_i s s',
      G tid s_i s ->
      Rely tid s s' ->
      exec tid (s_i, s) Yield (Finished (s', s') tt)
  | ExecYieldError : forall s_i s,
      ~G tid s_i s ->
      exec tid (s_i, s) Yield Error.

  Record SpecParams T :=
    { precondition : Prop;
      postcondition : forall (st': state sem * state sem) (r:T), Prop }.

  Definition Spec T := state sem * state sem -> SpecParams T.

  Definition prog_ok tid T (spec: Spec T) (p: prog T) :=
    forall st out,
      precondition (spec st) ->
      exec tid st p out ->
      match out with
      | Finished st' r => postcondition (spec st) st' r
      | Error => False
      end.

End Prog.

Instance tid_EqDec : EqDec TID.
Proof.
  unfold EqDec.
  decide equality.
Defined.

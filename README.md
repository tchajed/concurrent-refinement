# Concurrent refinement

Experiments in defining instrumented semantics for programming languages and proving them sound with respect to lower-level semantics.

Our particular use cases have instrumented semantics where:
* the semantics defines execution of a single program, abstracting away other threads in terms of a protocol, and
* ghost state that is shared among all threads but cannot influence program behavior.

The desired primitive semantics should include a scheduler that interleaves a set of threads. Programs proven using the instrumented semantics should be correct under the primitive semantics, so we need a proof that every primitive execution has an instrumented one.

---------------------------------- MODULE Base ---------------------------------
\* EXTENDS Apalache
LOCAL INSTANCE Integers

BSeq(S) == UNION { [1 .. k -> S] : k \in 0 .. 2 }
\* @type: (Set(a)) => Set(Seq(a));
\* BSeq(S) == Gen(2)

================================================================================

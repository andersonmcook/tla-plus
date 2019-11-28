---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157490615399740000 == 
[x \in {"a", "b", "c"} |-> TRUE]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157490615399740000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157490615399741000 ==
FALSE/\capacity = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157490615399742000 ==
FALSE/\capacity' = capacity
----
=============================================================================
\* Modification History
\* Created Wed Nov 27 19:55:53 CST 2019 by acook

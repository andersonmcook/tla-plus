---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157490617698546000 == 
DOMAIN [x \in {"a", "b", "c"} |-> TRUE]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157490617698546000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157490617698547000 ==
FALSE/\capacity = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157490617698548000 ==
FALSE/\capacity' = capacity
----
=============================================================================
\* Modification History
\* Created Wed Nov 27 19:56:16 CST 2019 by acook

---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157490620782358000 == 
[x \in (1..3) |-> TRUE]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157490620782358000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157490620782359000 ==
FALSE/\capacity = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157490620782360000 ==
FALSE/\capacity' = capacity
----
=============================================================================
\* Modification History
\* Created Wed Nov 27 19:56:47 CST 2019 by acook

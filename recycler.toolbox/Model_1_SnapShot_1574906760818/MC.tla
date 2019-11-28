---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157490675689188000 == 
[type: {"trash", "recycle"}, size: 1..6]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157490675689188000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157490675689189000 ==
FALSE/\capacity = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157490675689190000 ==
FALSE/\capacity' = capacity
----
=============================================================================
\* Modification History
\* Created Wed Nov 27 20:05:56 CST 2019 by acook

---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157490647427579000 == 
[trash: 1..3, recycle: 1..3]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157490647427579000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157490647427580000 ==
FALSE/\capacity = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157490647427581000 ==
FALSE/\capacity' = capacity
----
=============================================================================
\* Modification History
\* Created Wed Nov 27 20:01:14 CST 2019 by acook

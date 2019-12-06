---- MODULE MC ----
EXTENDS recycler, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15756471041683000 == 
FALSE \/ TRUE
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15756471041683000>>)
----

=============================================================================
\* Modification History
\* Created Fri Dec 06 09:45:04 CST 2019 by acook

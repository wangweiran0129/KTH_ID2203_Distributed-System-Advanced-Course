---- MODULE MC ----
EXTENDS LeaderElection, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_162108501784899000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1STOP
const_1621085017848100000 == 
5
----

\* Constant expression definition @modelExpressionEval
const_expr_1621085017848101000 == 
N
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1621085017848101000>>)
----

=============================================================================
\* Modification History
\* Created Sat May 15 15:23:37 CEST 2021 by wangweiran

---- MODULE MC ----
EXTENDS LeaderElection, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_162117466595532000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1STOP
const_162117466595533000 == 
5
----

\* Constant expression definition @modelExpressionEval
const_expr_162117466595534000 == 
N
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162117466595534000>>)
----

=============================================================================
\* Modification History
\* Created Sun May 16 16:17:45 CEST 2021 by wangweiran

---------------- MODULE 13BusfeederData_20200831_Settings3 ----------------
EXTENDS Sequences

\* Import feeder module
INSTANCE 13BusfeederData_20200831_v2

\****** Regulatory Settings ******

\* Version Control
RE_ProtocolVersion == "v14.0"
RE_StateEstimator == "BranchLoadSum"
RE_Optimization == "SecurityConstraint"

\* Process ordering
RE_preNodeReporting == <<"RE", "OP">>
RE_postNodeReporting == <<"SE", "AR", "CL">>

\* Settings for nodes
RE_COM_node_settings == {}

\* Settings for transaction module
RE_TR_settings == {}

\* Settings for AR Module
RE_AR_settings == {"ReportedLoadsWithinTolerance"}

\* Billing period is stored in the RE layer
RE_BillingPeriod == 2

\* Cost charged to customers at each node
RE_retailRate == 18

\* Settings for auditing and regulatory module
AR_tolerance_kW == 200 \* Maximum difference between reported load and measured at substation

\* Optimization settings
OP_SlackBusPower == <<10000, 0>> \* Power limit on slack bus by time step (0 for outage)
OP_tolerance_kW == 50 \* For stable operation, need to converge to a value within 100 kW
OP_initialPrice == 20 
OP_initialStepSize == 10 \* Step size, which is scaled on subsequent iterations
OP_maxIterations == 1000 \* Limit the number of OP iterations

\* Latency options for each node
latencyOptions == [671n |-> {1}] \* no error
    \*[671n |-> {1,2},
    \*646n |-> {1,2}] \* Table 2 error (11 full iterations)
    
    \*[692n |-> {1,2},
    \*646n |-> {1,2}] \* More complex error

=============================================================================
\* Modification History
\* Last modified Mon Aug 31 23:45:28 EDT 2020 by Alan
\* Last modified Wed Aug 19 10:11:41 EDT 2020 by Alan
\* Last modified Tue Aug 18 22:02:24 EDT 2020 by aransil
\* Last modified Mon Aug 17 21:10:55 EDT 2020 by aransil
\* Last modified Thu Aug 13 11:58:52 EDT 2020 by Alan
\* Created Mon Dec 09 22:47:20 EST 2019 by aransil

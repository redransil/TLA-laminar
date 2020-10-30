--------------------------- MODULE transactive_8 ---------------------------
\* FDIA system applied to a hierarchical, radial feeder
\* Each load node must have exactly one parent branch, each branch may have up to one parent branch
\* Power is injected at the slack bus and consumed at load nodes

EXTENDS TLC, Integers, Sequences, FiniteSets
INSTANCE 13BusfeederData_20200831_Settings3
RECURSIVE Sum(_), sumOverSet(_, _), appendSet(_, _), superBranches(_), coordDomainBranches(_), calcPowerOfBranchWCDs(_, _, _, _), calcPowerOfCD(_, _, _, _), calcSetOfCoordDomains(_, _)
    
\* Version of this protocol
ProtocolVersion == "v14.0"

\*crash == TRUE \* Use to force system to error after optimization for readout
crash == FALSE

\********** General utility operators

\* Find the max of two numbers in a set
Max(set) == CHOOSE x \in set : \A y \in set : x >= y
Min(set) == CHOOSE x \in set : \A y \in set : x <= y

\* Find the absolute value of a number
Abs(num) == Max({num, -num})

\* Finds num1 mod num2
Mod(num1, num2) == 
    IF num2 = 0
    THEN num1
    ELSE num1 - num2 * (num1 \div num2) \* the operator \div rounds down

\* Gets the range of a function (including a sequence)
range(func) == {func[x] : x \in DOMAIN func}

\* Takes a sequence of numbers and returns their sum
Sum(seq) == 
    IF Len(seq) = 0
    THEN 0
    ELSE Head(seq) + Sum(Tail(seq))

\* Returns the sum of values of all elements in inputSet
sumOverSet(inputSet, elementValues) ==
    IF inputSet = {} THEN 0 ELSE
        LET
            thisElem == CHOOSE x \in inputSet : TRUE
            remainingSet == inputSet \ {thisElem}
            toAdd == IF thisElem \in DOMAIN elementValues THEN elementValues[thisElem] ELSE 0
        IN
            toAdd + sumOverSet(remainingSet, elementValues)
            
\* Appends set to sequence
appendSet(seq, set) ==
    LET
        thisElem == CHOOSE elem \in set : TRUE
        remainingSet == set \ {thisElem}
        nextIndex == Len(seq) + 1
    IN
        IF remainingSet = {} THEN Append(seq, thisElem)
        ELSE Append(appendSet(seq, remainingSet), thisElem)
        
\********** Tracking the flow of time and process sequencing

\* Time steps correspond to elements of loadSequence
timeSteps == DOMAIN loadSequence

\* If sequence has only this process, check whether it's available
\* If there's another process before it, check whether that process is complete
checkProcessAvailable(processName, processSeq, processAvailable) ==
    IF ~ processName \in range(processSeq)
    THEN FALSE
    ELSE
        LET 
            processIndex == CHOOSE i \in 1..Len(processSeq) : processSeq[i] = processName
            prevProcessName == processSeq[processIndex-1]
        IN
            IF Len(processSeq) = 1 \/ processIndex = 1
            THEN processAvailable[processName]
            ELSE ~processAvailable[prevProcessName] /\ processAvailable[processName]
            
\********** Operators dealing with the feeder structure and power flows

\* Get node IDs as the union of all nodes in branches
allNodes == UNION {branchNodes[x] : x \in branchIDs}

\* For a node with a given load and cost sequence, set load
\* costSeq and loadSeq form a supply curve. Customer will use loadSeq[i]
\* at up to costSeq[i], and loadSeq[Len(loadSeq)] for costs above max(costSeq)
chooseLoad(loadSeq, costSeq, rate)==
    LET
        consumerSurplusIndices == {i \in DOMAIN costSeq : costSeq[i] >= rate}
        index == 
            IF consumerSurplusIndices = {} THEN Len(loadSeq)
            ELSE Min(consumerSurplusIndices)
    IN
        loadSeq[index]

\* Finds the branch that a given node directly belongs to
containingBranch(node) == {x \in branchIDs : node \in branchNodes[x]}

\* Recursively finds all the branches (superbranches) containing this branch as a subbranch
superBranches(branch) == 
    LET 
        \* Superset should only ever have one element
        superSet == {x \in branchIDs : branch \in branchSubs[x]}
        parentBranch == CHOOSE y \in superSet : TRUE
    IN
        IF superSet = {} THEN {}
        ELSE superSet \union superBranches(parentBranch)

\* For a given node, get the branch it's on plus superbranches
nodeAllBranches(node) == 
    LET
        directBranch == containingBranch(node)
        higherBranches == 
            LET thisBranch == CHOOSE x \in directBranch : TRUE
            IN superBranches(thisBranch)
    IN directBranch \union higherBranches

\* Calculates the load in each branch based on node loads
branchPower(nodePower) ==
    [branch \in branchIDs |-> sumOverSet({n \in allNodes : branch \in nodeAllBranches(n)}, nodePower)]
    
\* Recursively finds all the branches (superbranches) containing this branch as a subbranch up to coord domain
coordDomainBranches(branch) == 
    LET 
        \* Superset should only ever have one element
        superSet == {x \in branchIDs : branch \in branchSubs[x]}
        parentBranch == CHOOSE y \in superSet : TRUE
    IN
        IF (branch \in coordDomains) \/ (superSet = {}) THEN {} 
        ELSE superSet \union coordDomainBranches(parentBranch)
    
\* For a given node, get the branch it's on plus superbranches within coord domain
\* The set returned includes the coord domain itself
nodeAllBranchesDomain(node) == 
    LET
        directBranch == containingBranch(node)
        higherBranches == 
            LET thisBranch == CHOOSE x \in directBranch : TRUE
            IN coordDomainBranches(thisBranch)
    IN directBranch \union higherBranches
    
\* For a given node, find its coordination domain (which is a branch name)
\* Returns a string
nodeCoordDomain(node) ==
    LET
        domainSet == coordDomains \intersect nodeAllBranchesDomain(node)
    IN
        CHOOSE x \in domainSet : TRUE
        
\* If this branch is a coordination domain, looks up and returns its power
\* Otherwise, adds power of all sub-branches (recursively) and nodes (at the end of recursion) 
calcPowerOfBranchWCDs(subBranches, thisBranch, nodePower, coordDomainPower) ==

    IF subBranches = {} THEN sumOverSet(branchNodes[thisBranch], nodePower) ELSE
        IF thisBranch \in coordDomains THEN coordDomainPower[thisBranch] ELSE
            LET
                chosenBranch == CHOOSE x \in subBranches : TRUE
                remainingBranches == subBranches \ {chosenBranch}
                toAdd == calcPowerOfBranchWCDs(branchSubs[chosenBranch], chosenBranch, nodePower, coordDomainPower)
            IN
                toAdd + calcPowerOfBranchWCDs(remainingBranches, thisBranch, nodePower, coordDomainPower)     
        
\* Assumes this is a coordination domain, and calculates power of nodes plus subbranches
\* This is run AT the thisDomain branch recursively over all its subBranches
\* So when calling, you have to provide both the branch and its subBranches
calcPowerOfCD(subBranches, thisDomain, nodePower, coordDomainPower) ==
    
    \* Recursively run on each branch 
    \* But evaluate using the function where if this branch is a coord domain it uses the reported answer
    \* When get to the empty set (end of recursion) add the nodes
    IF subBranches = {} THEN sumOverSet(branchNodes[thisDomain], nodePower) ELSE
        LET
            chosenBranch == CHOOSE x \in subBranches : TRUE
            remainingBranches == subBranches \ {chosenBranch}
            toAdd == calcPowerOfBranchWCDs(branchSubs[chosenBranch], chosenBranch, nodePower, coordDomainPower)
        IN
            toAdd + calcPowerOfCD(remainingBranches, thisDomain, nodePower, coordDomainPower)
            
\* domainsToCalc is the set of domains we will calculate the power of
\* Returns a function mapping each to its power
calcSetOfCoordDomains(domainsToCalc, nodePower) ==
    IF domainsToCalc = {} THEN [x \in {slackBusBranch} |-> 0] \* This will get written over
    ELSE
        LET
            thisDomain == CHOOSE x \in domainsToCalc : TRUE
            remainingDomains == domainsToCalc \ {thisDomain}
            remainingDomainsPower == calcSetOfCoordDomains(remainingDomains, nodePower)
        IN
            [x \in {thisDomain} |-> calcPowerOfCD(branchSubs[thisDomain], thisDomain, nodePower, remainingDomainsPower)] @@ remainingDomainsPower
            

(*--algorithm energy_modules_v6

variables
    
    \* Variables for dealing with module sequencing and simulation time
    time = 1,
    processSeq = <<"RE">>,
    processAvailable = [x \in range(processSeq) |-> TRUE],
    
    \* Variables used for control of module behavior
    OP_settings = {},
    
    \* Variables dealing with power transactions
    OP_rate = 0,
    OP_laminarDecomp_Rate = 0;
    OP_iterations = 1,
    OP_stepHistory = <<>>,
    OP_prices = <<>>,
    OP_stepSize = OP_initialStepSize,
    OP_netPower = <<>>,
    OP_remain = 0,
    OP_dP = 0,
    coordDomainPrice = [x \in coordDomains |-> 0],
    coordDomainPower = [x \in coordDomains |-> 0],
    OP_state = <<>>,
    OP_stateHistory = {},
    OP_skipped_iteration = <<>>,
    
    \* Variables tracking state of power flows in the system
    nodesActualLoad = [x \in allNodes |-> 0],
    branchesActualLoad = [x \in branchIDs |-> 0],
    slackBusDispatch = 0,
    
    \* Variables dealing with the latency of nodes
    latencyUnassigned = DOMAIN latencyOptions,
    \*latency = [None |-> "None"],
    latency = [x \in allNodes |-> 1],
    skipped = [x \in allNodes |-> <<>>],
    thisNode = "",
    currentFunc = [None |-> "None"],

\******* REGULATORY PROCESS **********
\* Decide the sequencing of different modules
\* Regulatory variables set in settings 
        
process Regulatory = "RE"
begin Regulate:
    while time \in timeSteps do
        await checkProcessAvailable("RE", processSeq, processAvailable);
        
        
        \* Check version for this protocol
        assert RE_ProtocolVersion = ProtocolVersion;
            
        processSeq := appendSet(<<"RE", "OP">>, allNodes) \o <<"SE", "OPI", "CL">>;
        processAvailable := [RE |-> FALSE] @@ [x \in range(processSeq) |-> TRUE];
        
        skipped := [x \in allNodes |-> <<>>];
        
        
        \* Communicate settings to individual modules
        
        if OP_SlackBusPower[time] = 0 then
            OP_settings := {"laminar"};
        else
            OP_settings := {"flat"};
        end if;
        
        \*OP_settings := RE_OP_settings;
        OP_iterations := 1;
        OP_state := <<>>;
        OP_stateHistory := {};
        
        \* Communication between control system and each node has a latency
        latencySetup:
            while Cardinality(latencyUnassigned) > 0 do
                thisNode := CHOOSE x \in latencyUnassigned : TRUE;
                if thisNode \in DOMAIN latencyOptions then
                    with thisLatency \in latencyOptions[thisNode] do
                        latency := [x \in {thisNode} |-> thisLatency] @@ latency;
                    end with;
                end if;
                latencyUnassigned := latencyUnassigned \ {thisNode};
            end while;
        
        
        
    end while;
end process; 


\******* OPTIMIZER PROCESS **********
process Optimize = "OP"
begin
optimize:
    while time \in timeSteps do
        await checkProcessAvailable("OP", processSeq, processAvailable);
        
        \* Choose the price for this timestep
        if "flat" \in OP_settings then
            OP_rate := RE_retailRate;
            
        elsif "laminar" \in OP_settings then
        
            \* The first iteration is a special case where we initialize the price
            OP_laminarDecomp_Rate := OP_initialPrice;
            OP_stepHistory := Append(OP_stepHistory, OP_laminarDecomp_Rate);
            OP_prices := Append(OP_prices, OP_laminarDecomp_Rate);
            
            \* Communicate the starting price to all coordination domains
            coordDomainPrice := [x \in coordDomains |-> OP_laminarDecomp_Rate];
            
            
            OP_stateHistory := OP_stateHistory \union {OP_state};
            OP_state := <<OP_laminarDecomp_Rate, OP_stepSize>>;
            OP_skipped_iteration := <<>>;
            
        end if;
        
        processAvailable["OP"] := FALSE;
        
    end while;
end process;

\******* COMMUNICATIONS SERVER MEASUREMENT PROCESS **********
process node \in allNodes
begin ProduceAndReport:
    while time \in timeSteps do
        await checkProcessAvailable(self, processSeq, processAvailable);

        \* Determine whether the node reports this iteration
        if Mod(OP_iterations, latency[self]) = 0 then
        
            \* In the case that this node is part of a laminar decomposition, receive price from coordination domain
            if "laminar" \in OP_settings then
            
                \* this node's coordination domain name is nodeCoordDomain(self)
                \* Then corresponding rate is coordDomainPrice[nodeCoordDomain(self)]
                nodesActualLoad[self] := chooseLoad(loadSequence[time][self], costSequence[time][self], coordDomainPrice[nodeCoordDomain(self)]);
            else
                nodesActualLoad[self] := chooseLoad(loadSequence[time][self], costSequence[time][self], OP_rate);
            end if;\* laminar
            
        else \* If this node skipped
            OP_skipped_iteration := Append(OP_skipped_iteration, self);
            skipped := [x \in {self} |-> skipped[self] \o <<OP_iterations>>] @@ skipped;
        end if;
        
        \* Flag this node as having completed
        processAvailable[self] := FALSE;
            
    end while;
end process;


\******* STATE ESTIMATOR PROCESS **********
process StateEstimator = "SE"
begin
Estimate:
    while time \in timeSteps do
        await checkProcessAvailable("SE", processSeq, processAvailable);
        
        \* Calculate the power in each coordination domain
        coordDomainPower := calcSetOfCoordDomains(coordDomains, nodesActualLoad);
        
        \* In parallel calculate the actual load in each branch
        branchesActualLoad := branchPower(nodesActualLoad);
        slackBusDispatch := Min({branchesActualLoad[slackBusBranch], OP_SlackBusPower[time]});
        
        \* Flag this process as having completed
        processAvailable["SE"] := FALSE;
        
        
    end while;
end process; 

\******************************************
\******* OP LAMINAR DECOMPOSITION ITERATOR **********
process OP_Iterator = "OPI"
begin
iterateNode:
    while time \in timeSteps do
        await checkProcessAvailable("OPI", processSeq, processAvailable);
            
        if "laminar" \in OP_settings then
            
            \* Accounting: increase iterations and log results of power estimates
            OP_netPower := Append(OP_netPower, coordDomainPower[slackBusBranch] - OP_SlackBusPower[time]);
            OP_stateHistory := OP_stateHistory \union {OP_state};
            if OP_iterations = 1 then
                OP_state := <<coordDomainPower[slackBusBranch], 0, OP_stepSize, OP_laminarDecomp_Rate>> \o OP_skipped_iteration;
            else
                OP_state := <<coordDomainPower[slackBusBranch], OP_netPower[OP_iterations-1], OP_stepSize, OP_laminarDecomp_Rate>> \o OP_skipped_iteration;
            end if;
            OP_skipped_iteration := <<>>;
            OP_iterations := OP_iterations + 1;

            \* End optimization if we are within tolerance
            if (OP_iterations >= OP_maxIterations)  \/ Abs(OP_netPower[OP_iterations-1]) < OP_tolerance_kW then
                processAvailable["OPI"] := FALSE;
            
            \* If have more iterations to go  
            else
                
                \* The second iteration is a special case because we don't have a slope yet
                if OP_iterations = 2 then
                    OP_stepSize := OP_initialStepSize;
                    
                    \* If power is too high, raise price
                    \* On iteration #2, looking at netPower for iteration #1
                    if (OP_netPower[OP_iterations-1]) > OP_tolerance_kW then
                        OP_laminarDecomp_Rate := OP_laminarDecomp_Rate + OP_stepSize;
                    \* If power is too low, lower price
                    elsif (OP_netPower[OP_iterations-1]) < OP_tolerance_kW then
                        OP_laminarDecomp_Rate := OP_laminarDecomp_Rate - OP_stepSize;
                    end if;
                    
                
                \* On successive iterations, use adaptive step size
                else
                    \* Calculate an adaptive step size that would get half way to target assuming linear
                    \* Again, we are calculating for the CURRENT iteration based on the PREVIOUS TWO netPower values
                    OP_dP := (OP_netPower[OP_iterations-1] - OP_netPower[OP_iterations-2]);
                    OP_remain := (OP_SlackBusPower[time] - OP_netPower[OP_iterations-1]);
                    
                    if OP_dP = 0 then
                        OP_stepSize := 2*OP_stepSize; \* If no change, double the step size
                    else
                        if (Abs(OP_remain) < Abs(2 * OP_dP)) /\ OP_remain < 0 then \* If step size would end up being 0
                            OP_stepSize := 1;
                        elsif (Abs(OP_remain) < Abs(2 * OP_dP)) /\ OP_remain > 0 then
                            OP_stepSize := -1;
                        else
                            OP_stepSize := (OP_remain * OP_stepSize) \div (2 * OP_dP);
                        end if;
                    end if;
                    OP_laminarDecomp_Rate := OP_laminarDecomp_Rate + OP_stepSize;
                end if;
                
                processAvailable := [SE |-> TRUE] @@ [x \in allNodes |-> TRUE] @@ processAvailable;
                OP_stepHistory := Append(OP_stepHistory, OP_stepSize);
                OP_prices := Append(OP_prices, OP_laminarDecomp_Rate);
            
            end if; \* Whether or not have more iterations to go
            
            \* Communicate the starting price to all coordination domains
            coordDomainPrice := [x \in coordDomains |-> OP_laminarDecomp_Rate];
            
            
        else \* ie if not laminar
            OP_rate := RE_retailRate;
            processAvailable["OPI"] := FALSE;
            
        end if;
            
    end while;
end process;

\******* CLOCK PROCESS **********
\* This process updates system variables to handle the passage of time

process Clock = "CL"
begin 

Tick:
    while time \in timeSteps do
        await checkProcessAvailable("CL", processSeq, processAvailable);
        
        time := time + 1; 
        
        if time \in timeSteps then 
            processAvailable := [RE |-> TRUE] @@ [x \in range(processSeq) |-> FALSE];
        else
            processAvailable := [x \in range(processSeq) |-> FALSE];
        end if;
        
        \* Recalculate system state for invariants
        branchesActualLoad := branchPower(nodesActualLoad);
        slackBusDispatch := branchesActualLoad[slackBusBranch];
        
    end while;
end process;

\******* FINISH SIMULATION PROCESS **********
\* Allows the model to finish successfully (instead of deadlock) if nothing goes wrong
process endSim = "FIN"
begin

FinishSimulation:
    while TRUE do
        await ~ time \in timeSteps;
        
        if crash then \* This is just a way of forcing the algorithm to output state when it would not otherwise
            assert FALSE;
        end if;
        
        skip;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7e1874e" /\ chksum(tla) = "638eea9e")
VARIABLES time, processSeq, processAvailable, OP_settings, OP_rate, 
          OP_laminarDecomp_Rate, OP_iterations, OP_stepHistory, OP_prices, 
          OP_stepSize, OP_netPower, OP_remain, OP_dP, coordDomainPrice, 
          coordDomainPower, OP_state, OP_stateHistory, OP_skipped_iteration, 
          nodesActualLoad, branchesActualLoad, slackBusDispatch, 
          latencyUnassigned, latency, skipped, thisNode, currentFunc, pc

vars == << time, processSeq, processAvailable, OP_settings, OP_rate, 
           OP_laminarDecomp_Rate, OP_iterations, OP_stepHistory, OP_prices, 
           OP_stepSize, OP_netPower, OP_remain, OP_dP, coordDomainPrice, 
           coordDomainPower, OP_state, OP_stateHistory, OP_skipped_iteration, 
           nodesActualLoad, branchesActualLoad, slackBusDispatch, 
           latencyUnassigned, latency, skipped, thisNode, currentFunc, pc >>

ProcSet == {"RE"} \cup {"OP"} \cup (allNodes) \cup {"SE"} \cup {"OPI"} \cup {"CL"} \cup {"FIN"}

Init == (* Global variables *)
        /\ time = 1
        /\ processSeq = <<"RE">>
        /\ processAvailable = [x \in range(processSeq) |-> TRUE]
        /\ OP_settings = {}
        /\ OP_rate = 0
        /\ OP_laminarDecomp_Rate = 0
        /\ OP_iterations = 1
        /\ OP_stepHistory = <<>>
        /\ OP_prices = <<>>
        /\ OP_stepSize = OP_initialStepSize
        /\ OP_netPower = <<>>
        /\ OP_remain = 0
        /\ OP_dP = 0
        /\ coordDomainPrice = [x \in coordDomains |-> 0]
        /\ coordDomainPower = [x \in coordDomains |-> 0]
        /\ OP_state = <<>>
        /\ OP_stateHistory = {}
        /\ OP_skipped_iteration = <<>>
        /\ nodesActualLoad = [x \in allNodes |-> 0]
        /\ branchesActualLoad = [x \in branchIDs |-> 0]
        /\ slackBusDispatch = 0
        /\ latencyUnassigned = DOMAIN latencyOptions
        /\ latency = [x \in allNodes |-> 1]
        /\ skipped = [x \in allNodes |-> <<>>]
        /\ thisNode = ""
        /\ currentFunc = [None |-> "None"]
        /\ pc = [self \in ProcSet |-> CASE self = "RE" -> "Regulate"
                                        [] self = "OP" -> "optimize"
                                        [] self \in allNodes -> "ProduceAndReport"
                                        [] self = "SE" -> "Estimate"
                                        [] self = "OPI" -> "iterateNode"
                                        [] self = "CL" -> "Tick"
                                        [] self = "FIN" -> "FinishSimulation"]

Regulate == /\ pc["RE"] = "Regulate"
            /\ IF time \in timeSteps
                  THEN /\ checkProcessAvailable("RE", processSeq, processAvailable)
                       /\ Assert(RE_ProtocolVersion = ProtocolVersion, 
                                 "Failure of assertion at line 244, column 9.")
                       /\ processSeq' = appendSet(<<"RE", "OP">>, allNodes) \o <<"SE", "OPI", "CL">>
                       /\ processAvailable' = [RE |-> FALSE] @@ [x \in range(processSeq') |-> TRUE]
                       /\ skipped' = [x \in allNodes |-> <<>>]
                       /\ IF OP_SlackBusPower[time] = 0
                             THEN /\ OP_settings' = {"laminar"}
                             ELSE /\ OP_settings' = {"flat"}
                       /\ OP_iterations' = 1
                       /\ OP_state' = <<>>
                       /\ OP_stateHistory' = {}
                       /\ pc' = [pc EXCEPT !["RE"] = "latencySetup"]
                  ELSE /\ pc' = [pc EXCEPT !["RE"] = "Done"]
                       /\ UNCHANGED << processSeq, processAvailable, 
                                       OP_settings, OP_iterations, OP_state, 
                                       OP_stateHistory, skipped >>
            /\ UNCHANGED << time, OP_rate, OP_laminarDecomp_Rate, 
                            OP_stepHistory, OP_prices, OP_stepSize, 
                            OP_netPower, OP_remain, OP_dP, coordDomainPrice, 
                            coordDomainPower, OP_skipped_iteration, 
                            nodesActualLoad, branchesActualLoad, 
                            slackBusDispatch, latencyUnassigned, latency, 
                            thisNode, currentFunc >>

latencySetup == /\ pc["RE"] = "latencySetup"
                /\ IF Cardinality(latencyUnassigned) > 0
                      THEN /\ thisNode' = (CHOOSE x \in latencyUnassigned : TRUE)
                           /\ IF thisNode' \in DOMAIN latencyOptions
                                 THEN /\ \E thisLatency \in latencyOptions[thisNode']:
                                           latency' = [x \in {thisNode'} |-> thisLatency] @@ latency
                                 ELSE /\ TRUE
                                      /\ UNCHANGED latency
                           /\ latencyUnassigned' = latencyUnassigned \ {thisNode'}
                           /\ pc' = [pc EXCEPT !["RE"] = "latencySetup"]
                      ELSE /\ pc' = [pc EXCEPT !["RE"] = "Regulate"]
                           /\ UNCHANGED << latencyUnassigned, latency, 
                                           thisNode >>
                /\ UNCHANGED << time, processSeq, processAvailable, 
                                OP_settings, OP_rate, OP_laminarDecomp_Rate, 
                                OP_iterations, OP_stepHistory, OP_prices, 
                                OP_stepSize, OP_netPower, OP_remain, OP_dP, 
                                coordDomainPrice, coordDomainPower, OP_state, 
                                OP_stateHistory, OP_skipped_iteration, 
                                nodesActualLoad, branchesActualLoad, 
                                slackBusDispatch, skipped, currentFunc >>

Regulatory == Regulate \/ latencySetup

optimize == /\ pc["OP"] = "optimize"
            /\ IF time \in timeSteps
                  THEN /\ checkProcessAvailable("OP", processSeq, processAvailable)
                       /\ IF "flat" \in OP_settings
                             THEN /\ OP_rate' = RE_retailRate
                                  /\ UNCHANGED << OP_laminarDecomp_Rate, 
                                                  OP_stepHistory, OP_prices, 
                                                  coordDomainPrice, OP_state, 
                                                  OP_stateHistory, 
                                                  OP_skipped_iteration >>
                             ELSE /\ IF "laminar" \in OP_settings
                                        THEN /\ OP_laminarDecomp_Rate' = OP_initialPrice
                                             /\ OP_stepHistory' = Append(OP_stepHistory, OP_laminarDecomp_Rate')
                                             /\ OP_prices' = Append(OP_prices, OP_laminarDecomp_Rate')
                                             /\ coordDomainPrice' = [x \in coordDomains |-> OP_laminarDecomp_Rate']
                                             /\ OP_stateHistory' = (OP_stateHistory \union {OP_state})
                                             /\ OP_state' = <<OP_laminarDecomp_Rate', OP_stepSize>>
                                             /\ OP_skipped_iteration' = <<>>
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << OP_laminarDecomp_Rate, 
                                                             OP_stepHistory, 
                                                             OP_prices, 
                                                             coordDomainPrice, 
                                                             OP_state, 
                                                             OP_stateHistory, 
                                                             OP_skipped_iteration >>
                                  /\ UNCHANGED OP_rate
                       /\ processAvailable' = [processAvailable EXCEPT !["OP"] = FALSE]
                       /\ pc' = [pc EXCEPT !["OP"] = "optimize"]
                  ELSE /\ pc' = [pc EXCEPT !["OP"] = "Done"]
                       /\ UNCHANGED << processAvailable, OP_rate, 
                                       OP_laminarDecomp_Rate, OP_stepHistory, 
                                       OP_prices, coordDomainPrice, OP_state, 
                                       OP_stateHistory, OP_skipped_iteration >>
            /\ UNCHANGED << time, processSeq, OP_settings, OP_iterations, 
                            OP_stepSize, OP_netPower, OP_remain, OP_dP, 
                            coordDomainPower, nodesActualLoad, 
                            branchesActualLoad, slackBusDispatch, 
                            latencyUnassigned, latency, skipped, thisNode, 
                            currentFunc >>

Optimize == optimize

ProduceAndReport(self) == /\ pc[self] = "ProduceAndReport"
                          /\ IF time \in timeSteps
                                THEN /\ checkProcessAvailable(self, processSeq, processAvailable)
                                     /\ IF Mod(OP_iterations, latency[self]) = 0
                                           THEN /\ IF "laminar" \in OP_settings
                                                      THEN /\ nodesActualLoad' = [nodesActualLoad EXCEPT ![self] = chooseLoad(loadSequence[time][self], costSequence[time][self], coordDomainPrice[nodeCoordDomain(self)])]
                                                      ELSE /\ nodesActualLoad' = [nodesActualLoad EXCEPT ![self] = chooseLoad(loadSequence[time][self], costSequence[time][self], OP_rate)]
                                                /\ UNCHANGED << OP_skipped_iteration, 
                                                                skipped >>
                                           ELSE /\ OP_skipped_iteration' = Append(OP_skipped_iteration, self)
                                                /\ skipped' = [x \in {self} |-> skipped[self] \o <<OP_iterations>>] @@ skipped
                                                /\ UNCHANGED nodesActualLoad
                                     /\ processAvailable' = [processAvailable EXCEPT ![self] = FALSE]
                                     /\ pc' = [pc EXCEPT ![self] = "ProduceAndReport"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED << processAvailable, 
                                                     OP_skipped_iteration, 
                                                     nodesActualLoad, skipped >>
                          /\ UNCHANGED << time, processSeq, OP_settings, 
                                          OP_rate, OP_laminarDecomp_Rate, 
                                          OP_iterations, OP_stepHistory, 
                                          OP_prices, OP_stepSize, OP_netPower, 
                                          OP_remain, OP_dP, coordDomainPrice, 
                                          coordDomainPower, OP_state, 
                                          OP_stateHistory, branchesActualLoad, 
                                          slackBusDispatch, latencyUnassigned, 
                                          latency, thisNode, currentFunc >>

node(self) == ProduceAndReport(self)

Estimate == /\ pc["SE"] = "Estimate"
            /\ IF time \in timeSteps
                  THEN /\ checkProcessAvailable("SE", processSeq, processAvailable)
                       /\ coordDomainPower' = calcSetOfCoordDomains(coordDomains, nodesActualLoad)
                       /\ branchesActualLoad' = branchPower(nodesActualLoad)
                       /\ slackBusDispatch' = Min({branchesActualLoad'[slackBusBranch], OP_SlackBusPower[time]})
                       /\ processAvailable' = [processAvailable EXCEPT !["SE"] = FALSE]
                       /\ pc' = [pc EXCEPT !["SE"] = "Estimate"]
                  ELSE /\ pc' = [pc EXCEPT !["SE"] = "Done"]
                       /\ UNCHANGED << processAvailable, coordDomainPower, 
                                       branchesActualLoad, slackBusDispatch >>
            /\ UNCHANGED << time, processSeq, OP_settings, OP_rate, 
                            OP_laminarDecomp_Rate, OP_iterations, 
                            OP_stepHistory, OP_prices, OP_stepSize, 
                            OP_netPower, OP_remain, OP_dP, coordDomainPrice, 
                            OP_state, OP_stateHistory, OP_skipped_iteration, 
                            nodesActualLoad, latencyUnassigned, latency, 
                            skipped, thisNode, currentFunc >>

StateEstimator == Estimate

iterateNode == /\ pc["OPI"] = "iterateNode"
               /\ IF time \in timeSteps
                     THEN /\ checkProcessAvailable("OPI", processSeq, processAvailable)
                          /\ IF "laminar" \in OP_settings
                                THEN /\ OP_netPower' = Append(OP_netPower, coordDomainPower[slackBusBranch] - OP_SlackBusPower[time])
                                     /\ OP_stateHistory' = (OP_stateHistory \union {OP_state})
                                     /\ IF OP_iterations = 1
                                           THEN /\ OP_state' = <<coordDomainPower[slackBusBranch], 0, OP_stepSize, OP_laminarDecomp_Rate>> \o OP_skipped_iteration
                                           ELSE /\ OP_state' = <<coordDomainPower[slackBusBranch], OP_netPower'[OP_iterations-1], OP_stepSize, OP_laminarDecomp_Rate>> \o OP_skipped_iteration
                                     /\ OP_skipped_iteration' = <<>>
                                     /\ OP_iterations' = OP_iterations + 1
                                     /\ IF (OP_iterations' >= OP_maxIterations)  \/ Abs(OP_netPower'[OP_iterations'-1]) < OP_tolerance_kW
                                           THEN /\ processAvailable' = [processAvailable EXCEPT !["OPI"] = FALSE]
                                                /\ UNCHANGED << OP_laminarDecomp_Rate, 
                                                                OP_stepHistory, 
                                                                OP_prices, 
                                                                OP_stepSize, 
                                                                OP_remain, 
                                                                OP_dP >>
                                           ELSE /\ IF OP_iterations' = 2
                                                      THEN /\ OP_stepSize' = OP_initialStepSize
                                                           /\ IF (OP_netPower'[OP_iterations'-1]) > OP_tolerance_kW
                                                                 THEN /\ OP_laminarDecomp_Rate' = OP_laminarDecomp_Rate + OP_stepSize'
                                                                 ELSE /\ IF (OP_netPower'[OP_iterations'-1]) < OP_tolerance_kW
                                                                            THEN /\ OP_laminarDecomp_Rate' = OP_laminarDecomp_Rate - OP_stepSize'
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED OP_laminarDecomp_Rate
                                                           /\ UNCHANGED << OP_remain, 
                                                                           OP_dP >>
                                                      ELSE /\ OP_dP' = (OP_netPower'[OP_iterations'-1] - OP_netPower'[OP_iterations'-2])
                                                           /\ OP_remain' = (OP_SlackBusPower[time] - OP_netPower'[OP_iterations'-1])
                                                           /\ IF OP_dP' = 0
                                                                 THEN /\ OP_stepSize' = 2*OP_stepSize
                                                                 ELSE /\ IF (Abs(OP_remain') < Abs(2 * OP_dP')) /\ OP_remain' < 0
                                                                            THEN /\ OP_stepSize' = 1
                                                                            ELSE /\ IF (Abs(OP_remain') < Abs(2 * OP_dP')) /\ OP_remain' > 0
                                                                                       THEN /\ OP_stepSize' = -1
                                                                                       ELSE /\ OP_stepSize' = ((OP_remain' * OP_stepSize) \div (2 * OP_dP'))
                                                           /\ OP_laminarDecomp_Rate' = OP_laminarDecomp_Rate + OP_stepSize'
                                                /\ processAvailable' = [SE |-> TRUE] @@ [x \in allNodes |-> TRUE] @@ processAvailable
                                                /\ OP_stepHistory' = Append(OP_stepHistory, OP_stepSize')
                                                /\ OP_prices' = Append(OP_prices, OP_laminarDecomp_Rate')
                                     /\ coordDomainPrice' = [x \in coordDomains |-> OP_laminarDecomp_Rate']
                                     /\ UNCHANGED OP_rate
                                ELSE /\ OP_rate' = RE_retailRate
                                     /\ processAvailable' = [processAvailable EXCEPT !["OPI"] = FALSE]
                                     /\ UNCHANGED << OP_laminarDecomp_Rate, 
                                                     OP_iterations, 
                                                     OP_stepHistory, OP_prices, 
                                                     OP_stepSize, OP_netPower, 
                                                     OP_remain, OP_dP, 
                                                     coordDomainPrice, 
                                                     OP_state, OP_stateHistory, 
                                                     OP_skipped_iteration >>
                          /\ pc' = [pc EXCEPT !["OPI"] = "iterateNode"]
                     ELSE /\ pc' = [pc EXCEPT !["OPI"] = "Done"]
                          /\ UNCHANGED << processAvailable, OP_rate, 
                                          OP_laminarDecomp_Rate, OP_iterations, 
                                          OP_stepHistory, OP_prices, 
                                          OP_stepSize, OP_netPower, OP_remain, 
                                          OP_dP, coordDomainPrice, OP_state, 
                                          OP_stateHistory, 
                                          OP_skipped_iteration >>
               /\ UNCHANGED << time, processSeq, OP_settings, coordDomainPower, 
                               nodesActualLoad, branchesActualLoad, 
                               slackBusDispatch, latencyUnassigned, latency, 
                               skipped, thisNode, currentFunc >>

OP_Iterator == iterateNode

Tick == /\ pc["CL"] = "Tick"
        /\ IF time \in timeSteps
              THEN /\ checkProcessAvailable("CL", processSeq, processAvailable)
                   /\ time' = time + 1
                   /\ IF time' \in timeSteps
                         THEN /\ processAvailable' = [RE |-> TRUE] @@ [x \in range(processSeq) |-> FALSE]
                         ELSE /\ processAvailable' = [x \in range(processSeq) |-> FALSE]
                   /\ branchesActualLoad' = branchPower(nodesActualLoad)
                   /\ slackBusDispatch' = branchesActualLoad'[slackBusBranch]
                   /\ pc' = [pc EXCEPT !["CL"] = "Tick"]
              ELSE /\ pc' = [pc EXCEPT !["CL"] = "Done"]
                   /\ UNCHANGED << time, processAvailable, branchesActualLoad, 
                                   slackBusDispatch >>
        /\ UNCHANGED << processSeq, OP_settings, OP_rate, 
                        OP_laminarDecomp_Rate, OP_iterations, OP_stepHistory, 
                        OP_prices, OP_stepSize, OP_netPower, OP_remain, OP_dP, 
                        coordDomainPrice, coordDomainPower, OP_state, 
                        OP_stateHistory, OP_skipped_iteration, nodesActualLoad, 
                        latencyUnassigned, latency, skipped, thisNode, 
                        currentFunc >>

Clock == Tick

FinishSimulation == /\ pc["FIN"] = "FinishSimulation"
                    /\ ~ time \in timeSteps
                    /\ IF crash
                          THEN /\ Assert(FALSE, 
                                         "Failure of assertion at line 485, column 13.")
                          ELSE /\ TRUE
                    /\ TRUE
                    /\ pc' = [pc EXCEPT !["FIN"] = "FinishSimulation"]
                    /\ UNCHANGED << time, processSeq, processAvailable, 
                                    OP_settings, OP_rate, 
                                    OP_laminarDecomp_Rate, OP_iterations, 
                                    OP_stepHistory, OP_prices, OP_stepSize, 
                                    OP_netPower, OP_remain, OP_dP, 
                                    coordDomainPrice, coordDomainPower, 
                                    OP_state, OP_stateHistory, 
                                    OP_skipped_iteration, nodesActualLoad, 
                                    branchesActualLoad, slackBusDispatch, 
                                    latencyUnassigned, latency, skipped, 
                                    thisNode, currentFunc >>

endSim == FinishSimulation

Next == Regulatory \/ Optimize \/ StateEstimator \/ OP_Iterator \/ Clock
           \/ endSim
           \/ (\E self \in allNodes: node(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Aug 31 23:41:25 EDT 2020 by Alan
\* Created Mon Aug 31 17:40:43 EDT 2020 by Alan

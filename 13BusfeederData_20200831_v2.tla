---------------------------- MODULE 13BusfeederData_20200831_v2 ----------------------------
\****** FEEDER DATA ******
\****** Automatically generated from OpenDSS file. Contains information on feeder structure,
\****** payments and crypto key pairs needed to run modular energy system.
EXTENDS Integers

\* Identifying strings of all the branches
branchIDs == {"650632l", "632670l", "670671l", "671680l", "671684l", "684611l", "684652l", "671692l", "692675l", "632633l", "632645l", "645646l"}

\* Load node structure: set of load nodes for each branch
\* Each load belongs to exactly one branch
branchNodes ==
    [650632l |-> {},
    632670l |-> {"670an", "670bn", "670cn"},
    670671l |-> {"671n"},
    671680l |-> {},
    671684l |-> {},
    684611l |-> {"611n"},
    684652l |-> {"652n"},
    671692l |-> {"692n"},
    692675l |-> {"675an", "675bn", "675cn"},
    632633l |-> {"634an", "634bn", "634cn"},
    632645l |-> {"645n"},
    645646l |-> {"646n"}]

\******************************************
\************* Set of branches defining coordination domains
\* Include slack bus branch
coordDomains == {"650632l", "632645l", "670671l"}
coordDomainsSecondStep == <<"650632lRecalc", "632645lRecalc", "670671lRecalc">>
secondStepCDKey ==
    [650632lRecalc |-> "650632l",
    632645lRecalc |-> "632645l",
    670671lRecalc |-> "670671l"]

\* function from each coordination domain to its sub domains
subDomains ==
    [650632l |-> {"632645l", "670671l"},
    632645l |-> {}, 
    670671l |-> {}]

\* Function from each coordination domain to its nodes
domainNodes ==
    [650632l |-> {"670an", "670bn", "670cn", "634an", "634bn", "634cn"},
    632645l |-> {"645n", "646n"}, 
    670671l |-> {"671n", "611n", "652n", "692n", "675an", "675bn", "675cn"}]


\******************************************



\* Branch structure: set of subbranches for each parent branch
\* Radial structure: each branch can have up to one parent
branchSubs ==
    [650632l |-> {"632670l", "632633l", "632645l"},
    632670l |-> {"670671l"},
    670671l |-> {"671680l", "671684l", "671692l"},
    671680l |-> {},
    671684l |-> {"684611l", "684652l"},
    684611l |-> {},
    684652l |-> {},
    671692l |-> {"692675l"},
    692675l |-> {},
    632633l |-> {},
    632645l |-> {"645646l"},
    645646l |-> {}]

\* Rating (max power) of each branch
branchRating ==
    [650632l |-> 3983,
    632670l |-> 3000,
    670671l |-> 4231,
    671680l |-> 1000,
    671684l |-> 1795,
    684611l |-> 297,
    684652l |-> 351,
    671692l |-> 1490,
    692675l |-> 970,
    632633l |-> 1055,
    632645l |-> 1424,
    645646l |-> 4326]

\* Load for every node at each timestep, and time sequence for these data
\* List is used to specify a cost curve. If l is <<15, 5, 1>> and c is <<2, 8>> then 
\* this node will use 15 kW if the price is less than or equal to 2, 5 kW if less than
\* or equal to 8, and 1 kW if above 8
t1l ==
    [671n |-> <<202, 75>>,
    634an |-> <<42, -26>>,
    634bn |-> <<21, -35>>,
    634cn |-> <<51, 2, -41>>,
    645n |-> <<181, 50>>,
    646n |-> <<159, 150, 32, -4, -34, -73>>,
    692n |-> <<73, 20>>,
    675an |-> <<236, 30>>,
    675bn |-> <<74, 16, -11>>,
    675cn |-> <<-26>>,
    611n |-> <<184, 148, 111, 56, -27, -36>>,
    652n |-> <<135, 29>>,
    670an |-> <<19, 5, -1, -2>>,
    670bn |-> <<72>>,
    670cn |-> <<121, 100, 63, 62, -21>>]

t1c ==
    [671n |-> <<34>>,
    634an |-> <<29>>,
    634bn |-> <<36>>,
    634cn |-> <<17, 37>>,
    645n |-> <<7>>,
    646n |-> <<17, 20, 22, 23, 39>>,
    692n |-> <<41>>,
    675an |-> <<47>>,
    675bn |-> <<34, 48>>,
    675cn |-> <<0>>,
    611n |-> <<12, 24, 26, 44, 48>>,
    652n |-> <<18>>,
    670an |-> <<5, 24, 37>>,
    670bn |-> <<0>>,
    670cn |-> <<13, 18, 26, 49>>]

t2l ==
    [671n |-> <<878, 872, 156, 90, -331>>,
    634an |-> <<58, 55, 35, 9, 0>>,
    634bn |-> <<51, 50, -4, -5, -6>>,
    634cn |-> <<133, 96, -19>>,
    645n |-> <<189, 93, -35>>,
    646n |-> <<247, 228, 129, -43>>,
    692n |-> <<184, 120, 87, 85, -18>>,
    675an |-> <<390, 158, -11>>,
    675bn |-> <<54, -17>>,
    675cn |-> <<259, 10, -50, -88>>,
    611n |-> <<177, 169, 54>>,
    652n |-> <<92, 87, 60, 24, 14>>,
    670an |-> <<17, 3>>,
    670bn |-> <<27, 24, 5>>,
    670cn |-> <<104, 97, 66, 51, 47, 30>>]

t2c ==
    [671n |-> <<13, 32, 41, 42>>,
    634an |-> <<25, 30, 35, 43>>,
    634bn |-> <<8, 9, 15, 33>>,
    634cn |-> <<20, 47>>,
    645n |-> <<20, 33>>,
    646n |-> <<18, 42, 45>>,
    692n |-> <<10, 10, 32, 43>>,
    675an |-> <<16, 21>>,
    675bn |-> <<2>>,
    675cn |-> <<2, 41, 47>>,
    611n |-> <<11, 16>>,
    652n |-> <<2, 25, 30, 39>>,
    670an |-> <<21>>,
    670bn |-> <<10, 29>>,
    670cn |-> <<1, 15, 17, 34, 46>>]

\*loadSequence == <<t1l, t2l>>
loadSequence == <<t1l, t2l>>
costSequence == <<t1c, t2c>>

\* Branch ID corresponding to the slack bus
slackBusBranch == "650632l"

\****** END FEEDER DATA ******

=============================================================================
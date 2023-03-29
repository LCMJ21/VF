------------------------- MODULE LeaderElectionRingInboxOnly -------------------------

EXTENDS Naturals, TLC

CONSTANTS N, succ

Node == 1..N

reachable(n) ==
  LET aux[i \in Nat] == 
    IF i = 1 THEN { succ[n] }
    ELSE aux[i-1] \cup { x \in Node : \E y \in aux[i-1] : x = succ[y] }
  IN aux[N]

ASSUME 
    /\ N > 0
    /\ succ \in [Node -> Node]
    /\ \A x \in Node : Node \subseteq reachable(x) 
    
VARIABLES inbox, elected

TypeOK == [] (inbox \in [Node -> SUBSET Node] /\ elected \in [Node -> BOOLEAN])

previous(id) == CHOOSE x \in Node : id = succ[x]

Init ==
    /\ inbox   = [id \in Node |-> {previous(id)}]
    /\ elected = [id \in Node |-> FALSE]

    
node(id) == \E m \in inbox[id] :
    /\ inbox'   = IF m >= id 
                  THEN [inbox EXCEPT ![id] = @ \ {m}, ![succ[id]] = @ \cup {m}]
                  ELSE [inbox EXCEPT ![id] = @ \ {m}]
    /\ elected' = IF m = id
                  THEN [elected EXCEPT ![id] = TRUE]
                  ELSE elected

Next == \E id \in Node : node(id)

vars == <<inbox, elected>>

Spec == Init /\ [][Next]_vars


AtMostOneLeader == [] (\A x,y \in Node : elected[x] /\ elected[y] => x = y)

LeaderStaysLeader == \A x \in Node : [] (elected[x] => [] (elected[x]))

AtLeastOneLeader == WF_vars(Next) => <> (\E x \in Node : elected[x])

ConfigSum == 5 :> 4 @@ 4:> 3 @@ 3:> 2 @@ 2:> 1 @@ 1:> 5
NoLeader == [] (\A x \in Node : ~elected[x])

=============================================================================
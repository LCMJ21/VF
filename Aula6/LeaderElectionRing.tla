------------------------- MODULE LeaderElectionRing -------------------------

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
    
VARIABLES outbox, inbox, elected

TypeOK == [] (outbox \in [Node -> SUBSET Node] /\ inbox \in [Node -> SUBSET Node] /\ elected \in [Node -> BOOLEAN])

Init ==
    /\ outbox  = [id \in Node |-> {id}]
    /\ inbox   = [id \in Node |-> {}]
    /\ elected = [id \in Node |-> FALSE]

previous(id) == CHOOSE x \in Node : id = succ[x]
    
transmit ==
    /\ outbox' = [ id \in Node |-> {}]
    /\ inbox'  = [ id \in Node |-> inbox[id] \cup outbox[previous(id)]]
    /\ UNCHANGED elected
    
node(id) == \E m \in inbox[id] :
    /\ inbox'   = [inbox EXCEPT ![id] = @ \ {m}]
    /\ outbox'  = IF m >= id 
                  THEN [outbox EXCEPT ![id] = @ \cup {m}]
                  ELSE outbox
    /\ elected' = IF m = id
                  THEN [elected EXCEPT ![id] = TRUE]
                  ELSE elected

Next == transmit \/ \E id \in Node : node(id)

vars == <<outbox, inbox, elected>>

Spec == Init /\ [][Next]_vars


AtMostOneLeader == [] (\A x,y \in Node : elected[x] /\ elected[y] => x = y)

LeaderStaysLeader == \A x \in Node : [] (elected[x] => [] (elected[x]))

AtLeastOneLeader == WF_vars(Next) => <> (\E x \in Node : elected[x])

ConfigSum == 5 :> 4 @@ 4:> 3 @@ 3:> 2 @@ 2:> 1 @@ 1:> 5
NoLeader == [] (\A x \in Node : ~elected[x])

=============================================================================
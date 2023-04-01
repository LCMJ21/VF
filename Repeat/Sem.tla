------------------------- MODULE Sem -------------------------

EXTENDS Naturals, TLC, Sequences

CONSTANTS N

VARIABLES sem, pc


TypeOK == [] (sem \in BOOLEAN /\ pc \in [1..N -> 0..2])

Init == /\ sem = TRUE
        /\ pc = [i \in 1..N |-> 0]
        
Start(i) ==
    /\ pc[i] = 0
    /\ pc' = [pc EXCEPT ![i] = 1]
    /\ UNCHANGED <<sem>>

Idle(i) ==
    /\ pc[i] = 1
    /\ sem = TRUE
    /\ pc' = [pc EXCEPT ![i] = 2]
    /\ sem' = FALSE

Critical(i) ==
    /\ pc[i] = 2
    /\ sem = FALSE
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ sem' = TRUE

Next ==(\E id \in 1..N : Start(id) \/ Idle(id) \/ Critical(id))

vars == <<sem, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion == \A i,j \in 1..N : (i /= j /\ pc[i] /= 2) => pc[j] # 2

NoStarvation == \A i \in 1..N : (pc[i] = 1) => <>(pc[i] = 2)

=============================================================================
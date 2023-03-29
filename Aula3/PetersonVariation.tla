--------------------------- MODULE PetersonVariation ---------------------------

EXTENDS Integers

CONSTANTS N

VARIABLES pc, level, last, l

TypeOK == [] (pc \in [0..N-1 -> 0..2] /\ level \in [0..N-1 -> -1..N-2] /\ last \in [0..N-2 -> 0..N-1] /\ l \in [0..N-1 -> Int])

Init == pc = [i \in 0..N-1 |-> 0] /\ level = [i \in 0..N-1 |-> -1] /\ last = [i \in 0..N-2 |-> 0] /\ l = [i \in 0..N-1 |-> 0]

Idlle(i) ==
    /\ pc[i] = 0
    /\ IF l[i] < N-1
         THEN /\ level' = [level EXCEPT ![i] = l[i]]
            /\ last' = [last EXCEPT ![l[i]] = i]
            /\ pc' = [pc EXCEPT ![i] = 1]
            /\ UNCHANGED <<l>>
         ELSE /\ pc' = [pc EXCEPT ![i] = 2]
                /\ UNCHANGED <<last, level, l>>

Loop(i) ==
    /\ pc[i] = 1
    /\ \A j \in 0..N-1 : (pc[j] # 2)
    /\ (level[l[i]] # i \/ \A k \in 0..N-1 : k # i => level[k] < l[i])
    /\ l' = [l EXCEPT ![i] = @ + 1]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<level, last>>

Critical(i) ==
    /\ pc[i] = 2
    /\ level' = [level EXCEPT ![i] = -1]
    /\ l' = [l EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = 0]
    /\ UNCHANGED <<last>> 

Next == \E i \in 0..N-1 : Idlle(i) \/ Loop(i) \/ Critical(i)

vars == <<pc, level, last, l>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion == \A i,j \in 0..N-1 : i # j /\ pc[i] = 2 => pc[j] # 2

NoStrarvation == [] \A i \in 0..N-1 : pc[i] = 1 => <> (pc[i] = 2)

AllInCritical == ~<>(\A i \in 0..N-1 : pc[i] = 2)

=============================================================================
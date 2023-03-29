----------------------------- MODULE sem -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 0

VARIABLES sem,pc

TypeOK == [] (sem \in 0..1 /\ pc \in [1..N -> 0..2])

Init == sem = 1 /\ pc = [i \in 1..N |-> 0]

Asking(i) == 
    /\ pc[i] = 0
    /\ sem' = sem
    /\ pc' = [pc EXCEPT ![i] = 1]

Enter(i) == 
    /\ pc[i] = 1
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![i] = 2]

Exit(i) == 
    /\ pc[i] = 2
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![i] = 0]

Next == \E i \in 1..N : Asking(i) \/ Enter(i) \/ Exit(i)

vars == <<sem,pc>>

Algorithm == Init /\ [][Next]_vars /\ SF_vars(Next)

MUTUAL_EXCLUSION == [] \A i,j \in 1..N : i /= j => pc[i] /= 2 \/ pc[j] /= 2

NO_STARVATION == [] \A i \in 1..N : pc[i] = 1 => <> (pc[i] = 2) 

=============================================================================
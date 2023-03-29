----------------------------- MODULE peterson -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 0

VARIABLES level, last, l, pc

TypeOK == [] (pc \in [0..N-1 -> 0..2] /\ level \in [0..N-1 -> -1..N-2] /\ last \in [0..N-2 -> 0..N-1] /\ l \in [0..N-1 -> Int])

Init == pc = [i \in 0..N-1 |-> 0] /\ level = [i \in 0..N-1 |-> -1] /\ last = [i \in 0..N-2 |-> 0] /\ l = [i \in 0..N-1 |-> 0]

It_0(i) == 
    /\ pc[i] = 0
    /\ level' = [level EXCEPT ![i] = l[i]]
    /\ last' = [last EXCEPT ![l[i]] = i]
    /\ l' = l
    /\ pc' = [pc EXCEPT ![i] = 1]

It_1(i) == 
    /\ pc[i] = 1
    /\ (\A p \in 0..N-1 : pc[p] /= 2)
    /\ (last[l[i]] /= i \/ \A k \in 0..N-2 : k /= i => last[k] < l[i])
    /\ last' = last
    /\ level' = level
    /\ l' = [l EXCEPT ![i] = l[i] + 1]
    /\ pc' = [pc EXCEPT ![i] = 2]

It_2(i) == 
    /\ pc[i] = 2
    /\ level' = [level EXCEPT ![i] = -1]
    /\ last' = last
    /\ l' = [l EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = 0]

Next == \E i \in 0..N-1 : It_0(i) \/ It_1(i) \/ It_2(i)

vars == <<level, last, l, pc>>

Algorithm == Init /\ [][Next]_vars

MUTUAL_EXCLUSION == [] \A i,j \in 0..N-1 : i /= j => pc[i] /= 2 \/ pc[j] /= 2

NO_STARVATION == [] \A i \in 0..N-1 : pc[i] = 1 => <> (pc[i] = 2)

=============================================================================
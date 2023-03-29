----------------------------- MODULE Increment -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 0

VARIABLES x,y,pc

TypeOK == [] (x \in Int /\ pc \in [1..N -> 0..2] /\ y \in [1..N -> Int] )

Init == x = 0 /\ pc = [i \in 1..N |-> 0] /\ y = [i \in 1..N |-> 0]

Increment_y(i) == 
    /\ pc[i] = 0
    /\ \A j \in 1..N : pc[j] # 1
    /\ x' = x
    /\ y' = [y EXCEPT ![i] = x] 
    /\ pc' = [pc EXCEPT ![i] = 1]

Increment_x(i) == 
    /\ pc[i] = 1
    /\ y' = y
    /\ x' = y[i] + 1 
    /\ pc' = [pc EXCEPT ![i] = 2]

Next == \E i \in 1..N : Increment_y(i) \/ Increment_x(i)

vars == <<x,y,pc>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

Finish == \A i \in 1..N : pc[i] = 2

PartialCorrectness == [](Finish => x \in 1..N)

MutualExclusion == [](\A i,j \in 1..N : pc[i] = 1 /\ i # j => pc[j] # 1)

NoStarvation == [](\A i \in 1..N : pc[i] = 1 => <>(pc[i] = 2))

Termination == <> Finish

=============================================================================
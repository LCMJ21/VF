----------------------------- MODULE filosofo -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 0

VARIABLES waiter,fork, pc

TypeOK == [] (waiter \in BOOLEAN /\ fork \in [0..N-1 -> BOOLEAN] /\ pc \in [0..N-1 -> 0..3])

Init == waiter = TRUE /\ fork = [i \in 0..N-1|-> TRUE] /\ pc = [i \in 0..N-1|-> 0]

left(i) == (i)

right(i) == (i - 1) % N

i_0(i) == 
    /\ pc[i] = 0
    /\ waiter = TRUE
    /\ fork' = fork
    /\ waiter' = FALSE
    /\ pc' = [pc EXCEPT ![i] = 1]

i_1(i) == 
    /\ pc[i] = 1
    /\ fork[left(i)] = TRUE
    /\ fork' = [fork EXCEPT ![left(i)] = FALSE]
    /\ waiter' = waiter
    /\ pc' = [pc EXCEPT ![i] = 2]

i_2(i) == 
    /\ pc [i] = 2   
    /\ fork[right(i)] = TRUE
    /\ fork' = [fork EXCEPT ![right(i)] = FALSE]
    /\ waiter' = TRUE
    /\ pc' = [pc EXCEPT ![i] = 3]

i_3(i) ==
    /\ pc[i] = 3    
    /\ fork' = [fork EXCEPT ![left(i)] = TRUE, ![right(i)] = TRUE]
    /\ waiter' = waiter
    /\ pc' = [pc EXCEPT ![i] = 0]

Next == \E i \in 0..N-1 : i_0(i) \/ i_1(i) \/ i_2(i) \/ i_3(i)

vars == <<waiter,fork,pc>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

Eating == [](\A i \in 0..N-1 : pc[i] /= 3)

Neighbour == [](\A i \in 0..N-1 : pc[i] = 3 => pc[right(i)] /= 3)

After_Waiter_Will_Eat == [](\A i \in 0..N-1 : pc[i] = 1 => <> (pc[i] = 3))

Everybody_Eats == []~(\A i \in 0..N-1 : <> (pc[i] = 3))

=============================================================================
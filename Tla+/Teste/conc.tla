----------------------------- MODULE conc -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 0

VARIABLES n, lock, waiting, pc

TypeOK == [] (n \in 0..N 
    /\ lock \in BOOLEAN 
    /\ waiting \in [1..N -> BOOLEAN] 
    /\ pc \in [1..N -> 0..3])

Init == n = 0
    /\ lock = TRUE
    /\ waiting = [i \in 1..N |-> FALSE]
    /\ pc = [i \in 1..N |-> 0]

Enter(i) == /\ pc[i] = 0
            /\ lock = TRUE
            /\ lock' = FALSE
            /\ n' = n + 1
            /\ pc' = [pc EXCEPT ![i] = 1]
            /\ UNCHANGED <<waiting>>

EnterLoop(i) == /\ pc[i] = 1
                /\ n < N
                /\ waiting' = [waiting EXCEPT ![i] = TRUE]
                /\ lock' = TRUE
                /\ pc' = [pc EXCEPT ![i] = 2]
                /\ UNCHANGED <<n>>

ExitLoop(i) == /\ pc[i] = 1
               /\ n >= N
               /\ waiting' = [j \in 1..N |-> FALSE]
               /\ lock' = TRUE
               /\ pc' = [pc EXCEPT ![i] = 3]
               /\ UNCHANGED <<n>>

RepeatUntil(i) == /\ pc[i] = 2
                  /\ (lock /\ ~ waiting[i]) 
                  /\ pc' = [pc EXCEPT ![i] = 1]
                  /\ lock' = FALSE
                  /\ UNCHANGED <<waiting, n>>

Next == \E i \in 1..N : Enter(i) \/ EnterLoop(i) \/ ExitLoop(i) \/ RepeatUntil(i)

vars == <<n, lock, waiting, pc>>

Algorithm == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Teste

EnforceTypeOK == TypeOK \* See all TypeOK

ImpossibleAllWait ==  [](pc # [i \in 1..N |-> 2])

AllReachPc3 ==  <>(\A i \in 1..N : pc[i] = 3)

OneEndsOtherHaveStarted == [](\E i \in 1..N : pc[i] = 3) => (\A i \in 1..N : pc[i] # 0)

\* Test Wrong bit on Waiting


SomethingWentWrong(i) == /\ waiting' = [waiting EXCEPT ![i] = FALSE]
                         /\ UNCHANGED <<n, lock, pc>> 
        
NextSWW == \E i \in 1..N : Enter(i) \/ EnterLoop(i) \/ ExitLoop(i) \/ RepeatUntil(i) \/ SomethingWentWrong(i)

FairnessSWW == (\A i \in 1..N : SF_vars(NextSWW))

AlgorithmSWW == Init /\ [][NextSWW]_vars /\ FairnessSWW

\* Others

ForceAllReachPc3 ==  ~AllReachPc3 \* See all Reaching pc = 3

=============================================================================
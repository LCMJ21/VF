------------------------- MODULE dist -------------------------

EXTENDS Naturals, TLC, Sequences
    
VARIABLES inbox, result, try, pc

TypeOK == [] (inbox \in [0..1 -> Seq(1..2)] 
                /\ result \in [0..1 -> 0..2]
                /\ try \in [0..1 -> 1..2]
                /\ pc \in [0..1 -> 0..1])

Init ==
    /\ inbox   = [id \in 0..1 |-> <<>>]
    /\ result = [id \in 0..1 |-> 0]
    /\ \E r \in 1..2 : try = [id \in 0..1 |-> r]
    /\ pc     = [id \in 0..1 |-> 0]

    
Start(i) ==
        /\ pc[i] = 0
        /\ pc' = [pc EXCEPT ![i] = 1]
        /\ inbox' = [inbox EXCEPT ![1-i] = Append(@,try[i])]
        /\ UNCHANGED <<result, try>>

ReceiveAndSend(i) == 
        /\ result[i] = 0
        /\ inbox[i] # <<>>
        /\ pc[i] = 1
        /\ Head(inbox[i]) = try[i]
        /\ \E r \in 1..2 : try' = [try EXCEPT ![i] = r] 
        /\ inbox' = [inbox EXCEPT ![i] = Tail(@),
                                  ![1-i] = Append(@,try'[i])]
        /\ UNCHANGED <<pc, result>>

Receive(i) ==
        /\ result[i] = 0
        /\ inbox[i] # <<>>
        /\ pc[i] = 1
        /\ Head(inbox[i]) # try[i]
        /\ result' = [result EXCEPT ![i] = try[i]]
        /\ inbox' = [inbox EXCEPT ![i] = Tail(@)]
        /\ UNCHANGED <<pc, try>>

BackToLoop(i) == /\ (result[i] # 0 \/ inbox[i] = <<>>)
              /\ UNCHANGED <<inbox, result, try, pc>>


Next == \/ \E i \in 0..1 : Start(i) \/ ReceiveAndSend(i) \/  Receive(i) \/ BackToLoop(i)

vars == <<inbox, result, try, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


DiffResult == ([] (\E i \in 0..1 : result[i] # 0 => result[i] # result[1-i]))

NoMoreThan2 == [] (\A i \in 0..1 : Len(inbox[i]) <= 2)

NoMoreZero == [] (\E i \in 0..1 : result[i] # 0 => <>(result[1-i] # 0))

\* See results

ResultEqual == ~DiffResult

=============================================================================
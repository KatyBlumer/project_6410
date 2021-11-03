------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

ctx0 == [id |-> 0, pc |-> 1, stack |-> <<>>, vars |-> <<>>]

VARIABLES CTXBAG, SHARED, pc

Init == (* global variables *)
        /\ pc = 1 (* code program counter *)
        /\ CTXBAG = {ctx0} (* a set of contexts *)
        /\ SHARED = <<>> (* start empty *)
        
(* push val onto head of ctx stack *)
Push(ctx,val) == /\ ctx0.pc = pc
                 /\ pc' = pc + 1
                 /\ ctx0' = [ctx0 EXCEPT !.pc = pc', !.stack = <<val>> \o <<ctx0.stack>>]
                 /\ UNCHANGED CTXBAG
                 /\ UNCHANGED SHARED

(* store val onto ctx var record *)
Store(ctx,var) == /\ ctx0.pc = pc
                  /\ pc' = pc + 1
                  /\ ctx0' = [ctx0 EXCEPT !.pc = pc', !.stack = Tail(ctx0.stack), !.vars = [var |-> Head(ctx0.stack)]]
                  /\ UNCHANGED CTXBAG
                  /\ UNCHANGED SHARED

=============================================================================
\* Modification History
\* Last modified Tue Nov 02 21:17:44 EDT 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

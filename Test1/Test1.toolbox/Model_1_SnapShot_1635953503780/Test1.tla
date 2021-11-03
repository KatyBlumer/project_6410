------------------------------- MODULE Test1 -------------------------------
EXTENDS Integers, Sequences

ctx0 == [pc |-> 1, stack |-> <<>>, vars |-> <<>>]

VARIABLE CTXBAG, SHARED

(*INSTANCE Harmony WITH CTXBAG <- CTXBAG, SHARED <-SHARED*)

vars == << CTXBAG, SHARED >>

Init == (* global variables *)
        /\ CTXBAG = {ctx0} (* a set of contexts *)
        /\ SHARED = <<>> (* start empty *) 
        
pc1(ctx) == 
/\ ctx = ctx0
/\ctx.pc = 1
   /\ ctx' = [ctx EXCEPT !.pc = 2 , !.stack = <<3>> \o ctx.stack]
   /\ UNCHANGED << SHARED >>
            
pc2(ctx) == 
ctx= ctx0
/\ctx.pc = 2
 /\ ctx' = [ctx EXCEPT !.pc = 3, !.stack = Tail(ctx.stack), !.vars = [ a |-> Head(ctx.stack)]]
 /\ UNCHANGED <<SHARED>>
 
(*pc1(ctx) == /\ pc = 1
            /\ pc' = pc + 1
            /\ Push(ctx0,3,pc,pc')

pc2(ctx) == /\ pc = 2
            /\ pc' = pc + 1
            /\ Store(ctx0,"a",pc,pc')

pc3(ctx) == /\ pc = 3
            /\ pc' = 5
            /\ Jump(ctx0, pc, pc')
            
pc4(ctx) == /\ pc = 4
            /\ pc' = pc + 1
            /\ Push(ctx0,TRUE,pc,pc')

pc5(ctx) == /\ pc = 5
            /\ pc' = pc + 1
            /\ Push(ctx0,FALSE,pc,pc')
            
pc6(ctx) == /\ pc = 6
            /\ pc' = pc + 1
            /\ Store(ctx0,"b",pc,pc')
            
TypeOK == pc \in Nat
          /\ (\E ctx \in CTXBAG: ctx.id = 4)*)
            
Next == pc1(ctx0) 

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 03 11:31:34 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

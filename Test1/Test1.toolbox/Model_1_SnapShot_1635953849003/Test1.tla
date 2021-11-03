------------------------------- MODULE Test1 -------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED, ctx0

vars == << CTXBAG, SHARED, ctx0>>

Init == (* global variables *)
        /\ ctx0 = [pc |-> 1, stack |-> <<>>, vars |-> <<>>]
        /\ CTXBAG = {ctx0} (* a set of contexts *)
        /\ SHARED = <<>> (* start empty *) 
     
        
pc1(ctx) == 
/\ ctx = ctx0
/\ctx.pc = 1
   /\ ctx' = [ctx EXCEPT !.pc = 2 , !.stack = <<3>> \o ctx.stack]
   /\ CTXBAG' = {ctx'}
   /\ UNCHANGED << SHARED>>
            
pc2(ctx) == 
/\ctx= ctx0
/\ctx.pc = 2
 /\ ctx' = [ctx EXCEPT !.pc = 1, !.stack = Tail(ctx.stack), !.vars = [ a |-> Head(ctx.stack)]]
    /\ CTXBAG' = {ctx'}
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
            
Next == pc1(ctx0) /\ pc2(ctx0)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 03 11:37:21 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

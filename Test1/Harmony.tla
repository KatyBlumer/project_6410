------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED, ctx0

HarmonyInit == (* global variables *)
        /\ ctx0 = [pc |-> 1, stack |-> <<>>, vars |-> <<>>]
        /\ CTXBAG = {ctx0} (* a set of contexts *)
        /\ SHARED = <<>> (* start empty *) 
        
(* push val onto head of ctx stack *)
Push(ctx,val,pc,new_pc) == 
    /\ ctx.pc = pc
    /\ ctx' = [ctx EXCEPT !.pc = new_pc , !.stack = <<val>> \o ctx.stack]
    /\ CTXBAG' = {ctx'}
    /\ UNCHANGED << SHARED>>

(* store val onto ctx var record *)
Store(ctx,var,pc,new_pc) == 
    /\ctx.pc = pc
    /\ ctx' = [ctx EXCEPT !.pc = new_pc, !.stack = Tail(ctx.stack), !.vars = [ a |-> Head(ctx.stack)]]
    /\ CTXBAG' = {ctx'}
    /\ UNCHANGED <<SHARED>>
                  
Jump(ctx,pc,new_pc) == 
    /\ ctx.pc = pc
    /\ ctx' = [ctx EXCEPT !.pc = new_pc]
    /\ CTXBAG' = {ctx'}
    /\ UNCHANGED SHARED
                               

=============================================================================
\* Modification History
\* Last modified Wed Nov 03 12:12:09 EDT 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

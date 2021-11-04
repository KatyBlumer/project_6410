------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED

NMap(var,val,map) == [x \in (DOMAIN map) \union {var} |-> IF x \in DOMAIN map THEN map[x] ELSE val] 

HarmonyInit == (* global variables *)
        /\ SHARED = <<>> (* start empty *) 
/\ CTXBAG = [c0 |-> [pc |-> 1, stack |-> <<>>, vars|->[FALSE|->FALSE]], 
c1 |-> [pc |-> 0, stack |-> <<>>, vars|->[FALSE|->FALSE]]]
     
        
(* push val onto head of ctx stack *)
Push(ctx,val,old_pc,new_pc) == 
/\ CTXBAG[ctx].pc = old_pc
/\ CTXBAG' = [CTXBAG EXCEPT ![ctx] = [pc|->new_pc, stack|-> <<val>> \o CTXBAG[ctx].stack, vars |-> CTXBAG[ctx].vars]]
    /\ UNCHANGED SHARED
    
(* store val onto ctx var record *)
Store(ctx,var,old_pc,new_pc) == 
/\ CTXBAG[ctx].pc = old_pc
/\ CTXBAG' = [CTXBAG EXCEPT ![ctx]  = [pc|->new_pc, stack|-> Tail(CTXBAG[ctx].stack), vars |-> NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars)] ]
    /\ UNCHANGED SHARED
                  
Jump(ctx,old_pc,new_pc) == 
/\ CTXBAG[ctx].pc = old_pc
/\ CTXBAG' = [CTXBAG EXCEPT ![ctx]  = [pc|->new_pc, stack|->CTXBAG[ctx].stack, vars |-> CTXBAG[ctx].vars]]
    /\ UNCHANGED SHARED
  (*  
Spawn(ctxa,ctxb,old_pc,new_pc) ==
    /\ CTXBAG[ctxa].pc = old_pc
    /\ ctxa' = [ctxa EXCEPT !.pc = new_pc]
    /\ ctxb' = [ctxb EXCEPT !.pc = new_pc, !.stack = ctxa.stack, !.vars = ctxa.vars ]
    /\ CTXSTACK' = Tail(CTXSTACK)
    /\ UNCHANGED <<SHARED>>*)

=============================================================================
\* Modification History
\* Last modified Thu Nov 04 15:58:35 EDT 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

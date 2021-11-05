------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED

NMap(var,val,map) == [x \in (DOMAIN map) \union {var} |-> IF x \in DOMAIN map THEN map[x] ELSE val] 
Update(new_pc, new_stack, new_thread) == [pc |-> new_pc, stack |-> new_stack, thread |-> new_thread]
UpdateG(ctx, new_pc, new_stack, new_thread) == [CTXBAG EXCEPT ![ctx] = Update(new_pc, new_stack, new_thread)]
HarmonyInit == (* global variables *)
        /\ SHARED = [FALSE|->FALSE] (* start empty *) 
        /\ CTXBAG = [c0 |-> [pc |-> 1, stack |-> <<>>, thread|->[FALSE|->FALSE]], 
                     c1 |-> [pc |-> 0, stack |-> <<>>, thread|->[FALSE|->FALSE]]]
     
        
(* push val onto head of ctx stack *)
Push(ctx,val,old_pc,new_pc) == 
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx] = [pc|->new_pc, stack|-> <<val>> \o CTXBAG[ctx].stack, thread |-> CTXBAG[ctx].thread]]
    /\ UNCHANGED SHARED


new_Push(ctx, val, old_pc, new_pc) ==
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = UpdateG(ctx, new_pc, <<val>> \o CTXBAG[ctx].stack, CTXBAG[ctx].thread)
    /\ UNCHANGED SHARED

Pop(ctx,old_pc,new_pc) ==
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx] = [pc |-> new_pc, stack |-> Tail(CTXBAG[ctx].stack), thread |-> CTXBAG[ctx].thread]]
    /\ UNCHANGED SHARED
                            

(* store val onto ctx var record *)
StoreVar(ctx,var,old_pc,new_pc) == 
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx]  = [pc|->new_pc, stack|-> Tail(CTXBAG[ctx].stack), thread |-> NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].thread)] ]
    /\ UNCHANGED SHARED

Store(ctx,var,old_pc,new_pc) == 
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx]  = [pc|->new_pc, stack|-> Tail(CTXBAG[ctx].stack), thread |-> CTXBAG[ctx].thread] ]
    /\ SHARED' = NMap(var, Head(CTXBAG[ctx].stack), SHARED)   
            
Jump(ctx,old_pc,new_pc) == 
    /\ CTXBAG[ctx].pc = old_pc
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx]  = [pc|->new_pc, stack|->CTXBAG[ctx].stack, thread |-> CTXBAG[ctx].thread]]
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
\* Last modified Thu Nov 04 20:01:27 EDT 2021 by noah
\* Last modified Thu Nov 04 15:58:35 EDT 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison


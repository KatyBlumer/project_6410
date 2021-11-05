------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED, CTXSET

NMap(var,val,map) == [x \in ((DOMAIN map) \union {var}) \ {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE val] 

HarmonyInit == (* global variables *)
 /\ SHARED = [FALSE |-> FALSE] (* start empty *) 
 /\ CTXBAG = [c0 |-> [pc |-> 1, stack |-> <<>>, vars|->[FALSE|->FALSE]], 
  c1 |-> [pc |-> 0, stack |-> <<>>, vars|->[FALSE|->FALSE]]]
 /\ CTXSET = DOMAIN CTXBAG \ {"c0"} (* all possible threads to spawn *)
     
        
(* push val onto head of ctx stack *)
Push(ctx,val,old_pc,new_pc) == 
 /\ CTXBAG[ctx].pc = old_pc
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = new_pc, ![ctx].stack = <<val>> \o CTXBAG[ctx].stack, ![ctx].vars = CTXBAG[ctx].vars]
 /\ UNCHANGED <<SHARED,CTXSET>>
    
(* thread store *)
StoreVar(ctx,var,old_pc,new_pc) == 
 /\ CTXBAG[ctx].pc = old_pc
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = new_pc, ![ctx].stack =  Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars) ]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
(* shared store *)
Store(ctx,var,old_pc,new_pc) == 
 /\ CTXBAG[ctx].pc = old_pc
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = new_pc, ![ctx].stack =  Tail(CTXBAG[ctx].stack)]
 /\ SHARED' = NMap(var,Head(CTXBAG[ctx].stack),SHARED)
 /\ UNCHANGED CTXSET
                  
Jump(ctx,old_pc,new_pc) == 
 /\ CTXBAG[ctx].pc = old_pc
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = new_pc]
 /\ UNCHANGED <<SHARED,CTXSET>>
   
Spawn(ctxa,ctxb,old_pc,new_pc) ==
 /\ CTXBAG[ctxa].pc = old_pc
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctxa].pc = new_pc, ![ctxb].pc = new_pc, ![ctxb].stack = CTXBAG[ctxa].stack, ![ctxb].vars = CTXBAG[ctxa].vars]
 /\ CTXSET' = CTXSET \ {ctxb}
 /\ UNCHANGED SHARED

=============================================================================
\* Modification History
\* Last modified Thu Nov 04 21:36:38 EDT 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

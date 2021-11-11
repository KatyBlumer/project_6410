------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED(*, CTXSET*)

NMap(var,val,map)  == [x \in ((DOMAIN map) \union {var}) \ {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE val] 
NMap2(var,map) == [x \in ((DOMAIN map) \ {var}) \union {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE FALSE] 
NMapReturn(var,map) == [x \in ((DOMAIN map) \ {var}) |-> map[x]] 
RECURSIVE NTail (_, _)
RECURSIVE NHead (_, _)
NTail(n,tup)      == IF n = 1 THEN Tail(tup) ELSE NTail(n-1,Tail(tup))  
NHead(n,tup)      == IF n = 1 THEN <<Head(tup)>> ELSE NHead(n-1,Tail(tup)) \o <<Head(tup)>>
SpawnHead(ctx)    == NHead(3,CTXBAG[ctx].stack)    
SpawnTail(ctx)    == NTail(3,CTXBAG[ctx].stack)

HarmonyInit == (* global variables *)
 /\ SHARED = [FALSE |-> FALSE] (* start empty *) 
 /\ CTXBAG = [c0 |-> [pc |-> 0, stack |-> <<<<>>>>, vars|->[FALSE|->FALSE]], c1 |-> [pc |-> 0, stack |-> <<<<>>>>, vars|->[FALSE|->FALSE]]]
(* /\ CTXSET = DOMAIN CTXBAG \ {"c0"} (* all possible threads to spawn *)*)
            
(* push val onto head of ctx stack *)
Push(ctx,val,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<val>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
    
(* thread store *)
StoreVar(ctx,var,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars) ]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
(* shared store *)
Store(ctx,var,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ SHARED' = NMap(var,Head(CTXBAG[ctx].stack),SHARED)
 (*/\ UNCHANGED CTXSET*)
                  
Jump(ctx,PC,PC_new) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC_new]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
(* push the value of a shared variable onto the context stack *)
Load(ctx,var_name,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 (* push the value of a shared variable onto the stack *) 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<SHARED[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
(* push the value of a thread variable onto the stack *)
LoadVar(ctx,var_name,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<CTXBAG[ctx].vars[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
Spawn(ctxa,ctxb,PC) ==
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = LET SpStk == SpawnHead(ctxa) IN [CTXBAG EXCEPT ![ctxa].pc = PC + 1, ![ctxa].stack = SpawnTail(ctxa), ![ctxb].pc = Head(SpStk), ![ctxb].stack = Tail(SpStk)]
(* /\ CTXSET' = CTXSET \ {ctxb}*)
 /\ UNCHANGED SHARED
 
 (* delete thread variable var*)
DelVar(ctx,var,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].vars = NMap2(var,CTXBAG[ctx].vars)]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
(* take top of the context's stack and assign it to Frame instruction arguments args *)
(* TODO want to do store var on possibly a tuple, only works for single var now *) 
Frame(ctx,args,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(args,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars)]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
 
Frame0(ctx,args,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
  /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1]
 /\ UNCHANGED <<SHARED(*,CTXSET*)>>
  
FrameEnd(ctx,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
     /\ SHARED' = [FALSE |-> FALSE] (* start empty *) 
 /\ CTXBAG' = [c0 |-> [pc |-> 0, stack |-> <<<<>>>>, vars|->[FALSE|->FALSE]], c1 |-> [pc |-> 0, stack |-> <<<<>>>>, vars|->[FALSE|->FALSE]]]
(* /\ CTXSET' = DOMAIN CTXBAG' \ {"c0"} (* all possible threads to spawn *)*)

 
(* niave implementation*)
Return(ctx,PC) == 
 /\ \E ct \in DOMAIN CTXBAG: CTXBAG[ct].pc = PC
 /\ CTXBAG' = NMapReturn(ctx,CTXBAG) (* remove the context from the context bag *)
 (*/\ CTXSET' = CTXSET \union {ctx} (* add context name back to the ctx set *)*)
 /\ UNCHANGED <<SHARED>>


=============================================================================
\* Modification History
\* Last modified Wed Nov 10 19:52:41 EST 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

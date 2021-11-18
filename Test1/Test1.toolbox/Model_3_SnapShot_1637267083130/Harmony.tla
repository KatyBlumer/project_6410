------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED, CTXSET

(* some helper functions *)
(* add var with val to map *)
NMap(var,val,map)  == [x \in ((DOMAIN map) \union {var}) \ {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE val] 
(* remove var from map, until empty map, i.e., FALSE |-> FALSE*)
NMap2(var,map) == [x \in ((DOMAIN map) \ {var}) \union {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE FALSE] 
(* remove var from map *)
NMapReturn(var,map) == [x \in ((DOMAIN map) \ {var}) |-> map[x]] 
RECURSIVE NTail (_, _)
RECURSIVE NHead (_, _)
(* the last n elements of the list *)
NTail(n,tup)      == IF n = 1 THEN Tail(tup) ELSE NTail(n-1,Tail(tup))  
(* the first n elements of a tup *)
NHead(n,tup)      == IF n = 1 THEN <<Head(tup)>> ELSE NHead(n-1,Tail(tup)) \o <<Head(tup)>>
SpawnHead(ctx)    == NHead(3,CTXBAG[ctx].stack)    
SpawnTail(ctx)    == NTail(3,CTXBAG[ctx].stack)
(* empty record *)
e_rec == [FALSE |-> FALSE] 
(* a new context *)
new_ctx == [pc |-> 0, stack |-> <<<<>>>>, vars|-> e_rec, active |-> FALSE]

(* Harmony Initial State *)
HarmonyInit == (* global variables *)
 /\ SHARED = e_rec (* start empty *) 
 /\ CTXBAG = [c0 |-> new_ctx, c1 |-> new_ctx, c2 |-> new_ctx]
 /\ CTXSET = {"c0","c1","c2","c3","c4","c5","c6","c7","c8","c9"}
            
(* push val onto head of ctx stack *)
Push(ctx,val,PC) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<val>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED,CTXSET>>
    
(* thread store *)
StoreVar(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars) ]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
(* shared store *)
Store(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ SHARED' = NMap(var,Head(CTXBAG[ctx].stack),SHARED)
 /\ UNCHANGED CTXSET
                  
Jump(ctx,PC,PC_new) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC_new]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
(* push the value of a shared variable onto the context stack *)
Load(ctx,var_name,PC) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 
 (* push the value of a shared variable onto the stack *) 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<SHARED[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
(* push the value of a thread variable onto the stack *)
LoadVar(ctx,var_name,PC) == 
 /\ CTXBAG[ctx].pc = PC
  /\ CTXBAG[ctx].active = TRUE
 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<CTXBAG[ctx].vars[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
Spawn(ctxa,PC) ==
 /\ CTXBAG[ctxa].pc = PC
 /\ CTXBAG[ctxa].active = TRUE
 /\ LET SpStk == SpawnHead(ctxa) IN
    LET ctxb == CHOOSE x \in DOMAIN CTXBAG : CTXBAG[x].active = FALSE IN
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctxa].pc = PC + 1, ![ctxa].stack = SpawnTail(ctxa), ![ctxb].pc = Head(SpStk), ![ctxb].stack = Tail(SpStk), ![ctxb].active = TRUE]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
 (* delete thread variable var*)
DelVar(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].vars = NMap2(var,CTXBAG[ctx].vars)]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
(* take top of the context's stack and assign it to Frame instruction arguments args *)
(* TODO want to do store var on possibly a tuple, only works for single var now *) 
Frame(ctx,args,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(args,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars)]
 /\ UNCHANGED <<SHARED,CTXSET>>
 
Frame0(ctx) == 
 /\ CTXBAG[ctx].pc = 0
 /\ CTXBAG[ctx].active = FALSE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = 1, ![ctx].active = TRUE]
 /\ UNCHANGED <<SHARED,CTXSET>>
  
ReturnEnd(ctx,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ SHARED' = e_rec
 /\ CTXBAG' = e_rec
 /\ UNCHANGED <<CTXSET>>
 
Return(ctx,PC) == 
 /\ CTXBAG[ctx].pc = PC
   /\ CTXBAG[ctx].active = TRUE
 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].active = FALSE] 
 /\ UNCHANGED <<SHARED,CTXSET>>


=============================================================================
\* Modification History
\* Last modified Thu Nov 18 15:24:19 EST 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

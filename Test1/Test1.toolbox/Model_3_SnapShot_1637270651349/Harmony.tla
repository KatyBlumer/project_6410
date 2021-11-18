------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences

VARIABLE CTXBAG, SHARED

(* some helper functions *)
(* add var with val to map *)
NMap(var,val,map)  == [x \in ((DOMAIN map) \union {var}) \ FALSE |-> IF x \in DOMAIN map THEN map[x] ELSE val] 
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
new_ctx == [pc |-> 0, stack |-> <<<<>>>>, vars|-> e_rec, active |-> FALSE, spn |-> FALSE]
(* initial context is marked as spawned;
 return checks if context is either in
 a "spawn state" or "applied state" *)
init_ctx == [pc |-> 0, stack |-> <<<<>>>>, vars|-> e_rec, active |-> TRUE, spn |-> TRUE]

(* Harmony Initial State *)
HarmonyInit == (* global variable *)
 /\ SHARED = e_rec (* start empty *) 
 /\ CTXBAG = [c0 |-> init_ctx, c1 |-> new_ctx, c2 |-> new_ctx]
            
(* push val onto head of ctx stack *)
Push(ctx,val,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<val>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
    
(* thread store *)
StoreVar(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars) ]
 /\ UNCHANGED SHARED
 
(* shared store *)
Store(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ SHARED' = NMap(var,Head(CTXBAG[ctx].stack),SHARED)
                  
Jump(ctx,PC,PC_new) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC_new]
 /\ UNCHANGED SHARED
 
(* push the value of a shared variable onto the context stack *)
Load(ctx,var_name,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 (* push the value of a shared variable onto the stack *) 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<SHARED[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
 
(* push the value of a thread variable onto the stack *)
LoadVar(ctx,var_name,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<CTXBAG[ctx].vars[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
 
Spawn(ctxa,PC) ==
 /\ CTXBAG[ctxa].pc = PC
 /\ CTXBAG[ctxa].active = TRUE
 /\ LET SpStk == SpawnHead(ctxa) IN
    LET ctxb == CHOOSE x \in DOMAIN CTXBAG : CTXBAG[x].active = FALSE IN
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctxa].pc = PC + 1, ![ctxa].stack = SpawnTail(ctxa), ![ctxb].pc = Head(SpStk), ![ctxb].stack = Tail(SpStk), ![ctxb].active = TRUE, ![ctxb].spn = TRUE]
 /\ UNCHANGED SHARED
 
 (* delete thread variable var*)
DelVar(ctx,var,PC) == 
 /\ CTXBAG[ctx].pc = PC 
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].vars = NMap2(var,CTXBAG[ctx].vars)]
 /\ UNCHANGED SHARED
 
(* take top of the context's stack and assign it to Frame instruction arguments args *)
(* TODO want to do store var on possibly a tuple, only works for single var now *) 
Frame(ctx,args,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG[ctx].spn = TRUE 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(args,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars)]
 /\ UNCHANGED SHARED
  
Return(ctx,PC) == 
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ IF CTXBAG[ctx].spn = TRUE THEN
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].active = FALSE] 
    ELSE 
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = Head(CTXBAG[ctx].stack), ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ UNCHANGED SHARED


=============================================================================
\* Modification History
\* Last modified Thu Nov 18 16:24:06 EST 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

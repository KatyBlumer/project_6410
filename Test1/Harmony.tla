------------------------------ MODULE Harmony ------------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLE CTXBAG, SHARED, FAILEDASSERT

(* some helper functions *)

Neg == [F |-> "T", T |-> "F"]
(* add var with val to map *)
NMap(var,val,map)  == [x \in ((DOMAIN map) \union {var}) \ {"FALSE"} |-> IF x = var THEN val ELSE map[x]] 
(* remove var from map, until empty map, i.e., FALSE |-> FALSE*)
NMap2(var,map) == [x \in ((DOMAIN map) \ {var}) \union {"FALSE"} |-> IF x \in DOMAIN map THEN map[x] ELSE FALSE] 
(* remove var from map *)
NMapReturn(var,map) == [x \in ((DOMAIN map) \ {var}) |-> map[x]] 
RECURSIVE NTail (_, _)
RECURSIVE NHead (_, _)
RECURSIVE AddMult (_, _, _)
AddMult(var_tup, val_tup, map) == IF Len(var_tup) = 1 THEN [x \in ((DOMAIN map) \union {Head(var_tup)}) \ {"FALSE"} |-> IF x = Head(var_tup) THEN Head(val_tup) ELSE map[x]]
                                     ELSE [x \in ((DOMAIN AddMult(Tail(var_tup), Tail(val_tup), map)) \union {Head(var_tup)}) \ {"FALSE"} |-> IF x = Head(var_tup) THEN Head(val_tup) ELSE AddMult(Tail(var_tup), Tail(val_tup), map)[x]]

(* the last n elements of the list *)
NTail(n,tup)      == IF n = 1 THEN Tail(tup) ELSE NTail(n-1,Tail(tup))  
(* the first n elements of a tup *)
NHead(n,tup)      == IF n = 1 THEN <<Head(tup)>> ELSE NHead(n-1,Tail(tup)) \o <<Head(tup)>>
(* nth element of a tup *)
SpawnHead(ctx)    == NHead(3,CTXBAG[ctx].stack)    
SpawnTail(ctx)    == NTail(3,CTXBAG[ctx].stack)

(* Number of contexts with specified PC *)
countLabel(This_PC) == Cardinality({ x \in DOMAIN CTXBAG : CTXBAG[x].pc = This_PC })

(* empty record *)
e_rec == [FALSE |-> FALSE] 
(* a new context *)
new_ctx == [pc |-> 0, stack |-> <<<<>>>>, vars|-> e_rec, active |-> FALSE, spn |-> FALSE, atomic |-> FALSE]
(* initial context is marked as spawned;
 return checks if context is either in
 a "spawn state" or "applied state" *)
init_ctx == [pc |-> 0, stack |-> <<<<>>>>, vars|-> e_rec, active |-> TRUE, spn |-> TRUE, atomic |-> FALSE]

(* Harmony Initial State *)
HarmonyInit == (* global variable *)
 /\ SHARED = e_rec (* start empty *) 
 /\ CTXBAG = [c0 |-> init_ctx, c1 |-> new_ctx, c2 |-> new_ctx]
 /\ FAILEDASSERT = FALSE
         
(* push val onto head of ctx stack *)
Push(ctx,val,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<val>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
    
(* thread store *)
StoreVar(ctx,var,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = NMap(var,Head(CTXBAG[ctx].stack),CTXBAG[ctx].vars) ]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
  
(* shared store *)
Store(ctx,var,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ SHARED' = IF var = ""
              THEN NMap(Head(Tail(Tail(CTXBAG[ctx].stack))), NMap(Head(Tail(CTXBAG[ctx].stack)), Head(CTXBAG[ctx].stack), SHARED[Head(Tail(Tail(CTXBAG[ctx].stack)))] ), SHARED)
              ELSE NMap(var,Head(CTXBAG[ctx].stack),SHARED)
 /\ UNCHANGED FAILEDASSERT
                   
Jump(ctx,PC,PC_new) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC_new]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
  
(* push the value of a shared variable onto the context stack *)
Load(ctx,var_name,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 (* push the value of a shared variable onto the stack *) 
 /\ CTXBAG' = IF var_name = ""
              THEN [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<SHARED[Head(Tail(CTXBAG[ctx].stack))][Head(CTXBAG[ctx].stack)]>> \o CTXBAG[ctx].stack]
              ELSE [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<SHARED[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
(* push the value of a thread variable onto the stack *)
LoadVar(ctx,var_name,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = <<CTXBAG[ctx].vars[var_name]>> \o CTXBAG[ctx].stack]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
Spawn(ctxa,PC) ==
 /\ (CTXBAG[ctxa].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctxa].pc = PC
 /\ CTXBAG[ctxa].active = TRUE
 /\ LET SpStk == SpawnHead(ctxa) IN
    LET ctxb == CHOOSE x \in DOMAIN CTXBAG : CTXBAG[x].active = FALSE IN
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctxa].pc = PC + 1, ![ctxa].stack = SpawnTail(ctxa), ![ctxb].pc = Head(SpStk), ![ctxb].stack = Tail(SpStk), ![ctxb].active = TRUE, ![ctxb].spn = TRUE]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
 (* delete thread variable var*)
DelVar(ctx,var,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC 
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].vars = NMap2(var,CTXBAG[ctx].vars)]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
(* take top of the context's stack and assign it to Frame instruction arguments args *)
(* TODO want to do store var on possibly a tuple, only works for single var now *) 
Frame(ctx,args,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG[ctx].spn = TRUE 
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack), ![ctx].vars = AddMult(args, CTXBAG[ctx].stack, CTXBAG[ctx].vars)]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
Return(ctx,PC) == 
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ IF CTXBAG[ctx].spn = TRUE THEN
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].active = FALSE] 
    ELSE 
    /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = Head(CTXBAG[ctx].stack), ![ctx].stack = Tail(CTXBAG[ctx].stack)]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
AssertH(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ UNCHANGED SHARED
 /\ IF Head(CTXBAG[ctx].stack) = TRUE THEN
    (/\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)]
     /\ UNCHANGED FAILEDASSERT)
    ELSE 
    (/\ CTXBAG' = [x \in DOMAIN CTXBAG |->  [pc |-> CTXBAG[x].pc, stack |-> CTXBAG[x].stack, vars|-> CTXBAG[x].vars, active |-> FALSE, spn |-> CTXBAG[x].spn, atomic |-> CTXBAG[x].atomic]]
     /\ FAILEDASSERT' = TRUE)

JumpCond(ctx, PC, exp, PC_new) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 /\ IF Head(CTXBAG[ctx].stack) = exp THEN
    (/\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC_new, ![ctx].stack = Tail(CTXBAG[ctx].stack)])
    ELSE
    (/\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = Tail(CTXBAG[ctx].stack)])

AtomicInc(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].atomic = TRUE]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
 AtomicDec(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].atomic = FALSE]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT

NotOp(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = << Neg[Head(CTXBAG[ctx].stack)]>> \o Tail(CTXBAG[ctx].stack)]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
EqOp(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1, ![ctx].stack = << (Head(CTXBAG[ctx].stack) = Head(Tail(CTXBAG[ctx].stack))) >> \o Tail(CTXBAG[ctx].stack)]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
 
Dummy(ctx, PC) ==
 /\ (CTXBAG[ctx].atomic = TRUE \/ (\forall x \in DOMAIN CTXBAG : CTXBAG[x].atomic = FALSE))
 /\ CTXBAG[ctx].pc = PC
 /\ CTXBAG[ctx].active = TRUE
 /\ CTXBAG' = [CTXBAG EXCEPT ![ctx].pc = PC + 1]
 /\ UNCHANGED SHARED
 /\ UNCHANGED FAILEDASSERT
=============================================================================
\* Modification History
\* Last modified Fri Dec 10 19:54:36 EST 2021 by noah
\* Last modified Thu Nov 18 16:26:44 EST 2021 by arielkellison
\* Created Tue Nov 02 18:59:20 EDT 2021 by arielkellison

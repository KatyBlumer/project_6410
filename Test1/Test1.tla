------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED

INSTANCE harmonywithbags WITH  CTXBAG <- CTXBAG, SHARED <- SHARED

vars == <<CTXBAG, SHARED>>
 
Init == HarmonyInit
      
pc1(ctx) == /\ ctx = "c0"
            /\ new_Push(ctx,3,1,2)
            
pc2(ctx) == /\ ctx = "c0"
            /\ StoreVar(ctx,"a",2,3)

pc3(ctx) == /\ ctx = "c0"
            /\ new_Push(ctx,TRUE,3,4) 

pc4(ctx) ==/\ ctx =  "c0"
            /\ StoreVar(ctx,"b",4,5)
            
pc5(ctx) == /\ ctx = "c0"
            /\ new_Push(ctx, "Hello!", 5, 6)
            
pc6(ctx) == /\ ctx = "c0"
            /\ Pop(ctx, 6, 7)
            
pc7(ctx) == /\ ctx = "c0"
            /\ Jump(ctx, 7, 1)
(*          
pc5(ctx) == /\ ctx =  "c0"
            /\ Jump(ctx,5,3)*)

(*pc6(ctx) == /\ ctx = CTXBAG["c0"] 
            /\ Spawn(ctx,CTXBAG[Head(CTXSTACK)],6,1)*)
            
Next == pc1("c0") \/ pc2("c0") \/pc3("c0") \/pc4("c0") \/pc5("c0") \/ pc6("c0") \/ pc7("c0")

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Thu Nov 04 20:03:22 EDT 2021 by noah
\* Last modified Thu Nov 04 16:00:25 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison


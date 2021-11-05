------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED, CTXSET

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, CTXSET <-CTXSET

vars == << CTXBAG, SHARED, CTXSET>>
 
Init == HarmonyInit
      
pc1(ctx) == /\ ctx = "c0"
            /\ Push(ctx,3,1,2)
            
pc2(ctx) == /\ ctx = "c0"
            /\ Store(ctx,"a",2,1)
   (*         
pc3(ctx) == /\ ctx = "c0"
            /\ Push(ctx,TRUE,3,4) 

pc4(ctx) ==/\ ctx =  "c0"
            /\ Store(ctx,"b",4,5)
          
pc5(ctx) == /\ ctx =  "c0"
            /\ Jump(ctx,5,6)

pc6(ctx) == /\ ctx = CTXBAG["c0"] 
            /\ Spawn(ctx,CTXBAG[CHOOSE x \in DOMAIN CTXSET: TRUE],6,1)*)
            
Next == pc1("c0") \/ pc2("c0")(* \/pc3("c0") \/ pc4("c0") \/ pc5("c0") \/ pc6("c0")*)

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Thu Nov 04 19:42:07 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

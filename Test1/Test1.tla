------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED, ctx0

INSTANCE Harmony WITH ctx0 <-ctx0, CTXBAG <- CTXBAG, SHARED <- SHARED

vars == << ctx0, CTXBAG, SHARED>>
 
Init == HarmonyInit
      
pc1(ctx) == /\ ctx = ctx0 
            /\ Push(ctx,3,1,2)
            
pc2(ctx) == /\ ctx = ctx0 
            /\ Store(ctx,"a",2,3)
            
pc3(ctx) == /\ ctx = ctx0
            /\ Push(ctx,TRUE,3,4) 

pc4(ctx) == /\ ctx = ctx0
            /\ Store(ctx,"b",4,5)
            
pc5(ctx) == /\ ctx = ctx0
            /\ Jump(ctx,5,3)
            
Next == pc1(ctx0) \/ pc2(ctx0) \/ pc3(ctx0) \/ pc4(ctx0) \/ pc5(ctx0)

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Nov 03 12:32:23 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

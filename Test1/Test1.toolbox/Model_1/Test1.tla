------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED, ctx0

INSTANCE Harmony WITH ctx0 <-ctx0, CTXBAG <- CTXBAG, SHARED <- SHARED

vars == << ctx0, CTXBAG, SHARED>>
 
Init == HarmonyInit
      
pc1(ctx) == 
/\ ctx = ctx0 /\ Push(ctx,3,1,2)
            
pc2(ctx) == 
/\ctx= ctx0 /\ Store(ctx,"a",2,1)

Next == pc1(ctx0) \/ pc2(ctx0)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 03 11:47:58 EDT 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

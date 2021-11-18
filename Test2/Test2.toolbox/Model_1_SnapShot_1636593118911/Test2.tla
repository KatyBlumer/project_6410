------------------------------- MODULE Test2 -------------------------------
VARIABLE CTXBAG, SHARED

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED

vars == << CTXBAG, SHARED>>
 
Init == HarmonyInit

pc0(ctx) == /\ Frame0(ctx,<<>>,0)
pc1(ctx) == /\ Push(ctx,3,1)
pc2(ctx) == /\ Store(ctx,"a",2)
pc3(ctx) == /\ Push(ctx,FALSE,3)
pc4(ctx) == /\ Store(ctx,"b",4)
pc5(ctx) == /\ ReturnEnd(ctx,5)

Next == pc0("c0") \/ pc1("c0") \/ pc2("c0") \/ pc3("c0") 
\/ pc4("c0") \/ pc5("c0") 
    
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Nov 10 20:11:33 EST 2021 by arielkellison
\* Created Wed Nov 10 20:06:12 EST 2021 by arielkellison

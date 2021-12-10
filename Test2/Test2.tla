------------------------------- MODULE Test2 -------------------------------
VARIABLE CTXBAG, SHARED

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED

vars == << CTXBAG, SHARED>>
 
Init == HarmonyInit

pc0(ctx) == /\ Frame(ctx,<<"Init">>,0)
pc1(ctx) == /\ Push(ctx,3,1)
pc2(ctx) == /\ Store(ctx,"a",2)
pc3(ctx) == /\ Push(ctx,FALSE,3)
pc4(ctx) == /\ Store(ctx,"b",4)
pc5(ctx) == /\ Return(ctx,5)

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self)
    \/ pc4(self) \/ pc5(self) 

Next == (\E self \in {"c0"}: proc(self))
    
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Mon Nov 29 22:50:29 EST 2021 by noah
\* Last modified Thu Nov 18 17:02:38 EST 2021 by arielkellison
\* Created Wed Nov 10 20:06:12 EST 2021 by arielkellison

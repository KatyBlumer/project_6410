------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED

vars == << CTXBAG, SHARED>>
 
Init == HarmonyInit
      
pc0(ctx) == /\ Frame0(ctx,<<>>,0)
            
pc1(ctx) == /\ Push(ctx,FALSE,1)
            
pc2(ctx) == /\ Store(ctx,"c",2)
           
pc3(ctx) == /\ Jump(ctx,3,9) 

pc4(ctx) == /\ Frame(ctx,"arg1",4)

pc5(ctx) == /\ LoadVar(ctx,"arg1",5)
          
pc6(ctx) == /\ DelVar(ctx,"arg1",6)

pc7(ctx) == /\ Store(ctx,"a",7)

pc8(ctx) == /\ Return(ctx,8)
            
pc9(ctx) == /\ Push(ctx,4,9)
            
pc10(ctx) == /\ Load(ctx,"c",10)
             
pc11(ctx) == /\ Push(ctx,<<>>,11)
            
pc12(ctx) == /\ Spawn(ctx, CHOOSE x \in (DOMAIN CTXBAG \ {ctx}): TRUE, 12)
            
pc13(ctx) == /\ ReturnEnd(ctx,13)

Next == pc0("c0") \/ pc1("c0") \/ pc2("c0") \/ pc3("c0") 
\/ pc4("c1") \/ pc5("c1") \/ pc6("c1") \/ pc7("c1") \/ pc8("c1") 
\/ pc9("c0") \/ pc10("c0") \/ pc11("c0") \/ pc12("c0") \/ pc13("c0")
    
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Nov 10 20:10:57 EST 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

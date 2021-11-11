------------------------------- MODULE Test1 -------------------------------
VARIABLE CTXBAG, SHARED, CTXSET

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, CTXSET <-CTXSET

vars == << CTXBAG, SHARED, CTXSET>>
 
Init == HarmonyInit
      
pc0(ctx) == /\ ctx = "c0"
            /\ Frame0(ctx,<<>>,0)
            
pc1(ctx) == /\ ctx = "c0" 
            /\ Push(ctx,FALSE,1)
            
pc2(ctx) == /\ ctx = "c0" 
            /\ Store(ctx,"c",2)
           
pc3(ctx) == /\ ctx = "c0"
            /\ Jump(ctx,3,9) 

pc4(ctx) == /\ ctx = "c1"
            /\ Frame(ctx,"arg1",4)

pc5(ctx) == /\ ctx =  "c1"
            /\ LoadVar(ctx,"arg1",5)
          
pc6(ctx) == /\ ctx =  "c1"
            /\ DelVar(ctx,"arg1",6)

pc7(ctx) == /\ ctx =  "c1"
            /\ Store(ctx,"a",7)
            
pc8(ctx) == /\ ctx = "c1" 
            /\ Return(ctx,8)
            
pc9(ctx) == /\ ctx = "c0"
            /\ Push(ctx,4,9)
            
pc10(ctx) == /\ ctx = "c0"
             /\ Load(ctx,"c",10)
             
pc11(ctx) == /\ctx = "c0"
             /\ Push(ctx,<<>>,11)
            
pc12(ctx) == /\ ctx = "c0" 
             /\ Spawn(ctx,"c1",12)
            
pc13(ctx) == /\ ctx = "c0"
             /\ Return(ctx,13)
            
Next == (pc0("c0") \/ pc1("c0") \/ pc2("c0") \/pc3("c0") \/pc9("c0") \/ pc10("c0") \/ pc11("c0")  \/ pc12("c0") \/
    pc13("c0") ) /\ (pc4("c1") \/ pc5("c1")  \/ pc6("c1") \/ 
    pc7("c1") \/ pc8("c1"))

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Nov 10 13:58:44 EST 2021 by arielkellison
\* Created Wed Nov 03 08:38:08 EDT 2021 by arielkellison

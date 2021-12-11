------------------------------- MODULE Test1_generated -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

pc0(ctx) == /\ Frame(ctx, 0, <<"INIT">>)
pc1(ctx) == /\ Push(ctx, 1, FALSE)
pc2(ctx) == /\ Store(ctx, 2, "c")
pc3(ctx) == /\ Jump(ctx, 3, 9)
pc4(ctx) == /\ Frame(ctx, 4, <<"arg1">>)
pc5(ctx) == /\ LoadVar(ctx, 5, "arg1")
pc6(ctx) == /\ DelVar(ctx, 6, "arg1")
pc7(ctx) == /\ Store(ctx, 7, "a")
pc8(ctx) == /\ Return(ctx, 8)
pc9(ctx) == /\ Push(ctx, 9, 4)
pc10(ctx) == /\ Load(ctx, 10, "c")
pc11(ctx) == /\ Push(ctx, 11, <<>>)
pc12(ctx) == /\ Spawn(ctx, 12)
pc13(ctx) == /\ Return(ctx, 13)

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self) \/ pc4(self) \/ pc5(self) \/ pc6(self) \/ pc7(self) \/ pc8(self) \/ pc9(self) \/ pc10(self) \/ pc11(self) \/ pc12(self) \/ pc13(self)

Next == (\E self \in {"c0", "c1", "c2"}: proc(self))

Spec == Init /\ [][Next]_vars

=============================================================================

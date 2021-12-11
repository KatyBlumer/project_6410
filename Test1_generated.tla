------------------------------- MODULE Test1_generated -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

pc0(ctx) == /\ Frame(ctx, <<"INIT">>, 0)
pc1(ctx) == /\ Push(ctx, FALSE, 1)
pc2(ctx) == /\ Store(ctx, "c", 2)
pc3(ctx) == /\ Jump(ctx, 3, 9)
pc4(ctx) == /\ Frame(ctx, <<"arg1">>, 4)
pc5(ctx) == /\ LoadVar(ctx, "arg1", 5)
pc6(ctx) == /\ DelVar(ctx, "arg1", 6)
pc7(ctx) == /\ Store(ctx, "a", 7)
pc8(ctx) == /\ Return(ctx, 8)
pc9(ctx) == /\ Push(ctx, 4, 9)
pc10(ctx) == /\ Load(ctx, "c", 10)
pc11(ctx) == /\ Push(ctx, <<>>, 11)
pc12(ctx) == /\ Spawn(ctx, 12)
pc13(ctx) == /\ Return(ctx, 13)

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self) \/ pc4(self) \/ pc5(self) \/ pc6(self) \/ pc7(self) \/ pc8(self) \/ pc9(self) \/ pc10(self) \/ pc11(self) \/ pc12(self) \/ pc13(self)

Next == (\E self \in {"c0", "c1"}: proc(self))

Spec == Init /\ [][Next]_vars

=============================================================================

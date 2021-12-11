--------------------------- MODULE PetersonsTest ---------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>
 
Init == HarmonyInit
 
pc0(ctx) == /\ Frame(ctx,<<"INIT">>,0)     
      
pc1(ctx) == /\ Push(ctx, [F |-> "F", T |-> "F"], 1)
pc2(ctx) == /\ Store(ctx, "flags", 2)

pc3(ctx) == /\ \E x \in {"F", "T"} : Push(ctx, x, 3)
pc4(ctx) == /\ Dummy(ctx, 4)
pc5(ctx) == /\ Store(ctx, "turn", 5)

pc6(ctx) == /\ Jump(ctx, 6, 45)
pc7(ctx) == /\ Frame(ctx, <<"self">>, 7)

pc8(ctx) == /\ \E x \in {FALSE, TRUE} : Push(ctx, x, 8)
pc9(ctx) == /\ Dummy(ctx, 9)
pc10(ctx) == /\ JumpCond(ctx, 10, FALSE, 43)

pc11(ctx) == /\ Push(ctx, "flags", 11)
pc12(ctx) == /\ LoadVar(ctx, "self", 12)
pc13(ctx) == /\ Push(ctx, "T", 13)
pc14(ctx) == /\ Store(ctx, "", 14)

pc15(ctx) == /\ Push(ctx, "T", 15)
pc16(ctx) == /\ LoadVar(ctx, "self", 16)
pc17(ctx) == /\ NotOp(ctx, 17)
pc18(ctx) == /\ Store(ctx, "turn", 18)

pc19(ctx) == /\ Push(ctx, "flags", 19)
pc20(ctx) == /\ Dummy(ctx, 20)
pc21(ctx) == /\ LoadVar(ctx, "self", 21)
pc22(ctx) == /\ NotOp(ctx, 22)
pc23(ctx) == /\ Load(ctx, "", 23)
pc24(ctx) == /\ NotOp(ctx, 24)
pc25(ctx) == /\ JumpCond(ctx, 25, "T", 30)
pc26(ctx) == /\ Load(ctx, "turn", 26)
pc27(ctx) == /\ LoadVar(ctx, "self", 27)
pc28(ctx) == /\ EqOp(ctx, 28)
pc29(ctx) == /\ Jump(ctx, 29, 31)
pc30(ctx) == /\ Push(ctx, TRUE, 30)
pc31(ctx) == /\ JumpCond(ctx, 31, FALSE, 19)

pc32(ctx) == /\ AtomicInc(ctx, 32)
pc33(ctx) == /\ Push(ctx, countLabel(33), 33)
pc34(ctx) == /\ Push(ctx, 1, 34)
pc35(ctx) == /\ EqOp(ctx, 35)
pc36(ctx) == /\ AssertH(ctx, 36)
pc37(ctx) == /\ AtomicDec(ctx, 37)

pc38(ctx) == /\ Push(ctx, "flags", 38)
pc39(ctx) == /\ LoadVar(ctx, "self", 39)
pc40(ctx) == /\ Push(ctx, "F", 40)
pc41(ctx) == /\ Store(ctx, "", 41)
pc42(ctx) == /\ Jump(ctx, 42, 8)
pc43(ctx) == /\ DelVar(ctx, "self", 43)
pc44(ctx) == /\ Return(ctx, 44)

pc45(ctx) == /\ Push(ctx, 7, 45)
pc46(ctx) == /\ Push(ctx, "F", 46)
pc47(ctx) == /\ Push(ctx, <<>>, 47)
pc48(ctx) == /\ Spawn(ctx, 48)

pc49(ctx) == /\ Push(ctx, 7, 49)
pc50(ctx) == /\ Push(ctx, "T", 50)
pc51(ctx) == /\ Push(ctx, <<>>, 51)
pc52(ctx) == /\ Spawn(ctx, 52)
pc53(ctx) == /\ Return(ctx, 53)
pc54(ctx) == /\ DelVar(ctx, "result", 54)

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self)
    \/ pc4(self) \/ pc5(self) \/ pc6(self) \/ pc7(self) \/ pc8(self)
    \/ pc9(self) \/ pc10(self) \/ pc11(self) \/ pc12(self)
    \/ pc13(self) \/ pc14(self) \/ pc15(self) \/ pc16(self) \/ pc17(self) \/ pc18(self) \/ pc19(self) \/ pc20(self) \/ pc21(self) \/ pc22(self) \/ pc23(self) \/ pc24(self) \/ pc25(self) \/ pc26(self) \/ pc27(self) \/ pc28(self) \/ pc29(self) \/ pc30(self) \/ pc31(self) \/ pc32(self) \/ pc33(self) \/ pc34(self) \/ pc35(self) \/ pc36(self) \/ pc37(self)
    \/ pc38(self) \/ pc39(self) \/ pc40(self) \/ pc41(self) \/ pc42(self) \/ pc43(self) \/ pc44(self) \/ pc45(self) \/ pc46(self) \/ pc47(self) \/ pc48(self) \/ pc49(self) \/ pc50(self) \/ pc51(self) \/ pc52(self) \/ pc53(self) \/ pc54(self)

Next == (\E self \in {"c0", "c1", "c2"}: proc(self))
    
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Fri Dec 10 19:55:25 EST 2021 by noah
\* Created Fri Dec 10 12:27:48 EST 2021 by noah

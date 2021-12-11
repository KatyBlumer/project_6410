--------------------------- MODULE PetersonsTest ---------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>
 
Init == HarmonyInit
 
pc0(ctx) == /\ Frame(ctx, 0, <<"INIT">>)     
      
pc1(ctx) == /\ Push(ctx, 1, [F |-> "F", T |-> "F"])
pc2(ctx) == /\ Store(ctx, 2, "flags")

pc3(ctx) == /\ \E x \in {"F", "T"} : Push(ctx, 3, x)
pc4(ctx) == /\ Dummy(ctx, 4)
pc5(ctx) == /\ Store(ctx, 5, "turn")

pc6(ctx) == /\ Jump(ctx, 6, 45)
pc7(ctx) == /\ Frame(ctx, 7, <<"self">>)

pc8(ctx) == /\ \E x \in {FALSE, TRUE} : Push(ctx, 8, x)
pc9(ctx) == /\ Dummy(ctx, 9)
pc10(ctx) == /\ JumpCond(ctx, 10, FALSE, 43)

pc11(ctx) == /\ Push(ctx, 11, "flags")
pc12(ctx) == /\ LoadVar(ctx, 12, "self")
pc13(ctx) == /\ Push(ctx, 13, "T")
pc14(ctx) == /\ Store(ctx, 14, "")

pc15(ctx) == /\ Push(ctx, 15, "T")
pc16(ctx) == /\ LoadVar(ctx, 16, "self")
pc17(ctx) == /\ NotOp(ctx, 17)
pc18(ctx) == /\ Store(ctx, 18, "turn")

pc19(ctx) == /\ Push(ctx, 19, "flags")
pc20(ctx) == /\ Dummy(ctx, 20)
pc21(ctx) == /\ LoadVar(ctx, 21, "self")
pc22(ctx) == /\ NotOp(ctx, 22)
pc23(ctx) == /\ Load(ctx, 23, "")
pc24(ctx) == /\ NotOp(ctx, 24)
pc25(ctx) == /\ JumpCond(ctx, 25, "T", 30)
pc26(ctx) == /\ Load(ctx, 26, "turn")
pc27(ctx) == /\ LoadVar(ctx, 27, "self")
pc28(ctx) == /\ EqOp(ctx, 28)
pc29(ctx) == /\ Jump(ctx, 29, 31)
pc30(ctx) == /\ Push(ctx, 30, TRUE)
pc31(ctx) == /\ JumpCond(ctx, 31, FALSE, 19)

pc32(ctx) == /\ AtomicInc(ctx, 32)
pc33(ctx) == /\ Push(ctx, 33, countLabel(33))
pc34(ctx) == /\ Push(ctx, 34, 1)
pc35(ctx) == /\ EqOp(ctx, 35)
pc36(ctx) == /\ AssertH(ctx, 36)
pc37(ctx) == /\ AtomicDec(ctx, 37)

pc38(ctx) == /\ Push(ctx, 38, "flags")
pc39(ctx) == /\ LoadVar(ctx, 39, "self")
pc40(ctx) == /\ Push(ctx, 40, "F")
pc41(ctx) == /\ Store(ctx, 41, "")
pc42(ctx) == /\ Jump(ctx, 42, 8)
pc43(ctx) == /\ DelVar(ctx, 43, "self")
pc44(ctx) == /\ Return(ctx, 44)

pc45(ctx) == /\ Push(ctx, 45, 7)
pc46(ctx) == /\ Push(ctx, 46, "F")
pc47(ctx) == /\ Push(ctx, 47, <<>>)
pc48(ctx) == /\ Spawn(ctx, 48)

pc49(ctx) == /\ Push(ctx, 49, 7)
pc50(ctx) == /\ Push(ctx, 50, "T")
pc51(ctx) == /\ Push(ctx, 51, <<>>)
pc52(ctx) == /\ Spawn(ctx, 52)
pc53(ctx) == /\ Return(ctx, 53)
pc54(ctx) == /\ DelVar(ctx, 54, "result")

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self)
    \/ pc4(self) \/ pc5(self) \/ pc6(self) \/ pc7(self) \/ pc8(self)
    \/ pc9(self) \/ pc10(self) \/ pc11(self) \/ pc12(self)
    \/ pc13(self) \/ pc14(self) \/ pc15(self) \/ pc16(self) \/ pc17(self) \/ pc18(self) \/ pc19(self) \/ pc20(self) \/ pc21(self) \/ pc22(self) \/ pc23(self) \/ pc24(self) \/ pc25(self) \/ pc26(self) \/ pc27(self) \/ pc28(self) \/ pc29(self) \/ pc30(self) \/ pc31(self) \/ pc32(self) \/ pc33(self) \/ pc34(self) \/ pc35(self) \/ pc36(self) \/ pc37(self)
    \/ pc38(self) \/ pc39(self) \/ pc40(self) \/ pc41(self) \/ pc42(self) \/ pc43(self) \/ pc44(self) \/ pc45(self) \/ pc46(self) \/ pc47(self) \/ pc48(self) \/ pc49(self) \/ pc50(self) \/ pc51(self) \/ pc52(self) \/ pc53(self) \/ pc54(self)

Next == (\E self \in {"c0", "c1", "c2"}: proc(self))
    
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Fri Dec 10 20:54:25 EST 2021 by katyblumer
\* Last modified Fri Dec 10 19:55:25 EST 2021 by noah
\* Created Fri Dec 10 12:27:48 EST 2021 by noah

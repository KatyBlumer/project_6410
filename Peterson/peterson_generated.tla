------------------------------- MODULE peterson_generated -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

pc0(ctx) == /\ Frame(ctx, 0, <<"INIT">>)
pc1(ctx) == /\ Push(ctx, 1, "flags")
pc2(ctx) == /\ Dummy(ctx, 2)  (* Sequential *)
pc3(ctx) == /\ Push(ctx, 3, "turn")
pc4(ctx) == /\ Dummy(ctx, 4)  (* Sequential *)
pc5(ctx) == /\ Push(ctx, 5, [0 -> F, 1 -> F])
pc6(ctx) == /\ Store(ctx, 6, "flags")
pc7(ctx) == /\ Push(ctx, 7, {0, 1})
pc8(ctx) == /\ Dummy(ctx, 8)  (* Choose *)
pc9(ctx) == /\ Store(ctx, 9, "turn")
pc10(ctx) == /\ Jump(ctx, 10, 66)
pc11(ctx) == /\ Frame(ctx, 11, <<"self">>)
pc12(ctx) == /\ Push(ctx, 12, {F, T})
pc13(ctx) == /\ Dummy(ctx, 13)  (* Choose *)
pc14(ctx) == /\ JumpCond(ctx, 14, F, 64)
pc15(ctx) == /\ Push(ctx, 15, "flags")
pc16(ctx) == /\ LoadVar(ctx, 16, "self")
pc17(ctx) == /\ Dummy(ctx, 17)  (* Address *)
pc18(ctx) == /\ Push(ctx, 18, T)
pc19(ctx) == /\ Store(ctx, 19, "")
pc20(ctx) == /\ Push(ctx, 20, 1)
pc21(ctx) == /\ LoadVar(ctx, 21, "self")
----------- TODO-nary-[-] Unimplemented nary_type: - ----- {'op': 'Nary', 'arity': 2, 'value': '-'}
pc23(ctx) == /\ Store(ctx, 23, "turn")
pc24(ctx) == /\ Push(ctx, 24, "flags")
pc25(ctx) == /\ Push(ctx, 25, 1)
pc26(ctx) == /\ LoadVar(ctx, 26, "self")
----------- TODO-nary-[-] Unimplemented nary_type: - ----- {'op': 'Nary', 'arity': 2, 'value': '-'}
pc28(ctx) == /\ Dummy(ctx, 28)  (* Address *)
pc29(ctx) == /\ Load(ctx, 29, "")
pc30(ctx) == /\ NotOp(ctx, 30)
pc31(ctx) == /\ JumpCond(ctx, 31, T, 36)
pc32(ctx) == /\ Load(ctx, 32, "turn")
pc33(ctx) == /\ LoadVar(ctx, 33, "self")
pc34(ctx) == /\ EqOp(ctx, 34)
pc35(ctx) == /\ Jump(ctx, 35, 37)
pc36(ctx) == /\ Push(ctx, 36, T)
pc37(ctx) == /\ JumpCond(ctx, 37, F, 24)
----------- TODO-inst-AtomicInc Unrecognized instr_name: AtomicInc ----- {'op': 'AtomicInc', 'lazy': 'False'}
pc39(ctx) == /\ Dummy(ctx, 39)  (* ReadonlyInc *)
----------- TODO-inst-AtomicInc Unrecognized instr_name: AtomicInc ----- {'op': 'AtomicInc', 'lazy': 'True'}
pc41(ctx) == /\ Push(ctx, 41, 38)
----------- TODO-nary-[atLabel] Unimplemented nary_type: atLabel ----- {'op': 'Nary', 'arity': 1, 'value': 'atLabel'}
pc43(ctx) == /\ Push(ctx, 43, <<>>)
pc44(ctx) == /\ Push(ctx, 44, <<>>)
pc45(ctx) == /\ Push(ctx, 45, 0)
pc46(ctx) == /\ Push(ctx, 46, 11)
----------- TODO-nary-[DictAdd] Unimplemented nary_type: DictAdd ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
pc48(ctx) == /\ Push(ctx, 48, 1)
pc49(ctx) == /\ LoadVar(ctx, 49, "self")
----------- TODO-nary-[DictAdd] Unimplemented nary_type: DictAdd ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
pc51(ctx) == /\ Push(ctx, 51, 1)
----------- TODO-nary-[DictAdd] Unimplemented nary_type: DictAdd ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
pc53(ctx) == /\ EqOp(ctx, 53)
pc54(ctx) == /\ Assert(ctx, 54)
----------- TODO-inst-AtomicDec Unrecognized instr_name: AtomicDec ----- {'op': 'AtomicDec'}
pc56(ctx) == /\ Dummy(ctx, 56)  (* ReadonlyDec *)
----------- TODO-inst-AtomicDec Unrecognized instr_name: AtomicDec ----- {'op': 'AtomicDec'}
pc58(ctx) == /\ Push(ctx, 58, "flags")
pc59(ctx) == /\ LoadVar(ctx, 59, "self")
pc60(ctx) == /\ Dummy(ctx, 60)  (* Address *)
pc61(ctx) == /\ Push(ctx, 61, F)
pc62(ctx) == /\ Store(ctx, 62, "")
pc63(ctx) == /\ Jump(ctx, 63, 12)
pc64(ctx) == /\ DelVar(ctx, 64, "self")
pc65(ctx) == /\ Return(ctx, 65)
pc66(ctx) == /\ Push(ctx, 66, 11)
pc67(ctx) == /\ Push(ctx, 67, 0)
pc68(ctx) == /\ Push(ctx, 68, <<>>)
pc69(ctx) == /\ Spawn(ctx, 69)
pc70(ctx) == /\ Push(ctx, 70, 11)
pc71(ctx) == /\ Push(ctx, 71, 1)
pc72(ctx) == /\ Push(ctx, 72, <<>>)
pc73(ctx) == /\ Spawn(ctx, 73)
pc74(ctx) == /\ Return(ctx, 74)

proc(self) == pc0(self) \/ pc1(self) \/ pc2(self) \/ pc3(self) \/ pc4(self) \/ pc5(self) \/ pc6(self) \/ pc7(self) \/ pc8(self) \/ pc9(self) \/ pc10(self) \/ pc11(self) \/ pc12(self) \/ pc13(self) \/ pc14(self) \/ pc15(self) \/ pc16(self) \/ pc17(self) \/ pc18(self) \/ pc19(self) \/ pc20(self) \/ pc21(self) \/ pc22(self) \/ pc23(self) \/ pc24(self) \/ pc25(self) \/ pc26(self) \/ pc27(self) \/ pc28(self) \/ pc29(self) \/ pc30(self) \/ pc31(self) \/ pc32(self) \/ pc33(self) \/ pc34(self) \/ pc35(self) \/ pc36(self) \/ pc37(self) \/ pc38(self) \/ pc39(self) \/ pc40(self) \/ pc41(self) \/ pc42(self) \/ pc43(self) \/ pc44(self) \/ pc45(self) \/ pc46(self) \/ pc47(self) \/ pc48(self) \/ pc49(self) \/ pc50(self) \/ pc51(self) \/ pc52(self) \/ pc53(self) \/ pc54(self) \/ pc55(self) \/ pc56(self) \/ pc57(self) \/ pc58(self) \/ pc59(self) \/ pc60(self) \/ pc61(self) \/ pc62(self) \/ pc63(self) \/ pc64(self) \/ pc65(self) \/ pc66(self) \/ pc67(self) \/ pc68(self) \/ pc69(self) \/ pc70(self) \/ pc71(self) \/ pc72(self) \/ pc73(self) \/ pc74(self)

Next == (\E self \in {"c0", "c1", "c2"}: proc(self))

Spec == Init /\ [][Next]_vars

=============================================================================

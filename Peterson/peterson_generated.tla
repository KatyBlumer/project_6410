------------------------------- MODULE peterson_generated -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

pc0(ctx) == /\ Frame(ctx, 0, <<"INIT">>)
----------- Cannot yet handle the Harmony type [address]: {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]} ----- {'op': 'Push', 'value': {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]}}
pc2(ctx) == /\ Dummy(ctx, 2)
----------- Cannot yet handle the Harmony type [address]: {'type': 'address', 'value': [{'type': 'atom', 'value': 'turn'}]} ----- {'op': 'Push', 'value': {'type': 'address', 'value': [{'type': 'atom', 'value': 'turn'}]}}
pc4(ctx) == /\ Dummy(ctx, 4)
----------- Can't handle non-empty dict: [{'key': {'type': 'int', 'value': '0'}, 'value': {'type': 'bool', 'value': 'False'}}, {'key': {'type': 'int', 'value': '1'}, 'value': {'type': 'bool', 'value': 'False'}}] ----- {'op': 'Push', 'value': {'type': 'dict', 'value': [{'key': {'type': 'int', 'value': '0'}, 'value': {'type': 'bool', 'value': 'False'}}, {'key': {'type': 'int', 'value': '1'}, 'value': {'type': 'bool', 'value': 'False'}}]}}
pc6(ctx) == /\ Store(ctx, 6, "flags")
----------- Cannot yet handle the Harmony type [set]: {'type': 'set', 'value': [{'type': 'int', 'value': '0'}, {'type': 'int', 'value': '1'}]} ----- {'op': 'Push', 'value': {'type': 'set', 'value': [{'type': 'int', 'value': '0'}, {'type': 'int', 'value': '1'}]}}
----------- Unrecognized instr_name: Choose ----- {'op': 'Choose'}
pc9(ctx) == /\ Store(ctx, 9, "turn")
pc10(ctx) == /\ Jump(ctx, 10, 66)
pc11(ctx) == /\ Frame(ctx, 11, <<"self">>)
----------- Cannot yet handle the Harmony type [set]: {'type': 'set', 'value': [{'type': 'bool', 'value': 'False'}, {'type': 'bool', 'value': 'True'}]} ----- {'op': 'Push', 'value': {'type': 'set', 'value': [{'type': 'bool', 'value': 'False'}, {'type': 'bool', 'value': 'True'}]}}
----------- Unrecognized instr_name: Choose ----- {'op': 'Choose'}
----------- Unrecognized instr_name: JumpCond ----- {'op': 'JumpCond', 'pc': '64', 'cond': {'type': 'bool', 'value': 'False'}}
----------- Cannot yet handle the Harmony type [address]: {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]} ----- {'op': 'Push', 'value': {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]}}
pc16(ctx) == /\ LoadVar(ctx, 16, "self")
----------- Unrecognized instr_name: Address ----- {'op': 'Address'}
pc18(ctx) == /\ Push(ctx, 18, TRUE)
----------- 'value' ----- {'op': 'Store'}
pc20(ctx) == /\ Push(ctx, 20, 1)
pc21(ctx) == /\ LoadVar(ctx, 21, "self")
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 2, 'value': '-'}
pc23(ctx) == /\ Store(ctx, 23, "turn")
----------- Cannot yet handle the Harmony type [address]: {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]} ----- {'op': 'Push', 'value': {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]}}
pc25(ctx) == /\ Push(ctx, 25, 1)
pc26(ctx) == /\ LoadVar(ctx, 26, "self")
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 2, 'value': '-'}
----------- Unrecognized instr_name: Address ----- {'op': 'Address'}
----------- 'value' ----- {'op': 'Load'}
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 1, 'value': 'not'}
----------- Unrecognized instr_name: JumpCond ----- {'op': 'JumpCond', 'pc': '36', 'cond': {'type': 'bool', 'value': 'True'}}
pc32(ctx) == /\ Load(ctx, 32, "turn")
pc33(ctx) == /\ LoadVar(ctx, 33, "self")
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 2, 'value': '=='}
pc35(ctx) == /\ Jump(ctx, 35, 37)
pc36(ctx) == /\ Push(ctx, 36, TRUE)
----------- Unrecognized instr_name: JumpCond ----- {'op': 'JumpCond', 'pc': '24', 'cond': {'type': 'bool', 'value': 'False'}}
----------- Unrecognized instr_name: AtomicInc ----- {'op': 'AtomicInc', 'lazy': 'False'}
----------- Unrecognized instr_name: ReadonlyInc ----- {'op': 'ReadonlyInc'}
----------- Unrecognized instr_name: AtomicInc ----- {'op': 'AtomicInc', 'lazy': 'True'}
pc41(ctx) == /\ Push(ctx, 41, 38)
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 1, 'value': 'atLabel'}
pc43(ctx) == /\ Push(ctx, 43, <<>>)
pc44(ctx) == /\ Push(ctx, 44, <<>>)
pc45(ctx) == /\ Push(ctx, 45, 0)
pc46(ctx) == /\ Push(ctx, 46, 11)
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
pc48(ctx) == /\ Push(ctx, 48, 1)
pc49(ctx) == /\ LoadVar(ctx, 49, "self")
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
pc51(ctx) == /\ Push(ctx, 51, 1)
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 3, 'value': 'DictAdd'}
----------- Unrecognized instr_name: Nary ----- {'op': 'Nary', 'arity': 2, 'value': '=='}
----------- Unrecognized instr_name: Assert ----- {'op': 'Assert'}
----------- Unrecognized instr_name: AtomicDec ----- {'op': 'AtomicDec'}
----------- Unrecognized instr_name: ReadonlyDec ----- {'op': 'ReadonlyDec'}
----------- Unrecognized instr_name: AtomicDec ----- {'op': 'AtomicDec'}
----------- Cannot yet handle the Harmony type [address]: {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]} ----- {'op': 'Push', 'value': {'type': 'address', 'value': [{'type': 'atom', 'value': 'flags'}]}}
pc59(ctx) == /\ LoadVar(ctx, 59, "self")
----------- Unrecognized instr_name: Address ----- {'op': 'Address'}
pc61(ctx) == /\ Push(ctx, 61, FALSE)
----------- 'value' ----- {'op': 'Store'}
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

# A TLA+ Specification of Harmony VM Instructions 

This repository contains the Harmony TLA+ module, created by Noah Bertram, Katy Blumer, and Ariel Kellison for Cornell CS6410. The Harmony module contains TLA+ specifications of the Harmony initial state and the following Harmony VM instructions.

1. Push
2. StoreVar
3. Store
4. Jump
5. Load
6. LoadVar
7. Spawn
8. Frame
9. Return
10. AssertH
11. JumpCond
12. AtomicInc
13. AtomicDec
14. NotOp
15. EqOp
16. Dummy

There are three directories with examples of Harmony programs (.hny files) whose machine instructions (.hvm files) have been hand translated into TLA+ modules. Each directory contains the root Harmony module, for ease importing into TLA+.  The Test1 and Test2 directories are translations of very simple Harmony programs. The Peterson directory contains Peterson's algorithm, which uses all of the instructions implemented thus far. 

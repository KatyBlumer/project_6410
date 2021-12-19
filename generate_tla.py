import json
import os
import sys


FINAL_OUTPUT_FMT = """\
------------------------------- MODULE {output_module_name} -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

{tla_instr_block}

proc(self) == {instr_conjunction}

Next == (\E self \in {{"c0", "c1", "c2"}}: proc(self))

Spec == Init /\ [][Next]_vars

=============================================================================
"""

class BaseInstr(object):
  subclasses = {}

  def __init__(self, pc, har_instr):
    self.pc = pc
    self.har_instr = har_instr
    self.instr_name = har_instr["op"]

  # Credit to https://medium.com/@vadimpushtaev/python-choosing-subclass-cf5b1b67c696
  @classmethod
  def register_subclass(cls, instr_names):
    if isinstance(instr_names, str):
      instr_names = [instr_names]
    def decorator(subclass):
      for instr_name in instr_names:
        cls.subclasses[instr_name] = subclass
      return subclass
    return decorator
  @classmethod
  def create(cls, instr_name, *params):
    if instr_name not in cls.subclasses:
      raise ValueError(f"TODO-inst-{instr_name} Unrecognized instr_name: {instr_name}")
    return cls.subclasses[instr_name](*params)

  @staticmethod
  def tla_quotes(s):
    return f'"{s}"'

  @staticmethod
  def har_to_tla_val(val_json, required_type=None):
    if isinstance(val_json, list):
      if (len(val_json) > 1):
        raise NotImplementedError(f"Cannot yet handle multiple values (len {len(val_json)}): {val_json}")
      val_json = val_json[0]
    har_type, har_val = val_json["type"], val_json["value"]
    if (required_type is not None) and (har_type != required_type):
      raise ValueError(f"Harmony value type [{har_type}] is not of required type [{required_type}]")
    if har_type == "bool":
      har_val = har_val[0].upper()
    elif har_type == "atom":
      har_val = BaseInstr.tla_quotes(har_val)
    elif har_type in ["int", "pc"]:
      pass
    elif har_type == "dict":
      if not har_val:
        har_val = "<<>>"
      else:
        elem_strings = []
        for elem_json in har_val:
          elem_key = BaseInstr.har_to_tla_val(elem_json["key"])
          elem_val = BaseInstr.har_to_tla_val(elem_json["value"])
          elem_strings.append(f"{elem_key} -> {elem_val}")
        har_val = f"[{', '.join(elem_strings)}]"
    elif har_type == "set":
      elem_strings = []
      for elem_json in har_val:
        elem_strings.append(BaseInstr.har_to_tla_val(elem_json))
      har_val = "{" + ', '.join(elem_strings) + "}"
    elif har_type == "address":
      har_val = BaseInstr.har_to_tla_val(har_val, required_type="atom")
    else:
      raise NotImplementedError(f"Cannot yet handle the Harmony type [{har_type}]: {val_json}")

    return har_val

  def fmt_instr(self, *args):
    arg_list = ", ".join([f"{x}" for x in args])
    if arg_list:
      arg_list = f", {arg_list}"
    return f"pc{self.pc}(ctx) == /\ {self.instr_name}(ctx, {self.pc}{arg_list})"

  def tla_instr(self):
      raise NotImplementedError("Should be implemented by subclasses")


@BaseInstr.register_subclass("Frame")
class InstrFrame(BaseInstr):
  def tla_instr(self):
    arg = self.har_instr["args"]
    if arg == "()":
      arg = "INIT"
    return self.fmt_instr(f"<<{self.tla_quotes(arg)}>>")

@BaseInstr.register_subclass(["Push"])
class InstrHandleVal(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(BaseInstr.har_to_tla_val(self.har_instr["value"]))

@BaseInstr.register_subclass("Jump")
class InstrJump(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(self.har_instr["pc"])

@BaseInstr.register_subclass(["LoadVar", "DelVar"])
class InstrHandleStr(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(self.tla_quotes(self.har_instr["value"]))

@BaseInstr.register_subclass(["Load", "Store"])
class InstrLoad(BaseInstr):
  def tla_instr(self):
    var_name = (BaseInstr.har_to_tla_val(self.har_instr["value"], required_type="atom")
                if "value" in self.har_instr
                else self.tla_quotes(""))
    return self.fmt_instr(var_name)

@BaseInstr.register_subclass("JumpCond")
class InstrJumpCond(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(
        BaseInstr.har_to_tla_val(self.har_instr["cond"], required_type="bool"),
        self.har_instr["pc"])

@BaseInstr.register_subclass(["Return", "Spawn", "Assert"])
class InstrNoArg(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr()

@BaseInstr.register_subclass(["Sequential", "Choose", "ReadonlyInc",
                              "ReadonlyDec", "Address"])
class InstrDummy(BaseInstr):
  def __init__(self, pc, har_instr):
    super(InstrDummy, self).__init__(pc, har_instr)
    self.orig_instr_name = self.instr_name
    self.instr_name = "Dummy"

  def tla_instr(self):
    return self.fmt_instr() + f"  (* {self.orig_instr_name} *)"


@BaseInstr.register_subclass("Nary")
class InstrNary(BaseInstr):
  nary_types = {
      "not": "NotOp",
      "-": "TODO",  ## ?? I think we only use this as 1-<bool> so far but it should really be subtraction
      "==": "EqOp",
      "DictAdd": "TODO",
      "atLabel": "TODO"
  }
  def tla_instr(self):
    nary_type = self.har_instr["value"]
    nary_opname = self.nary_types[nary_type]
    if nary_opname == "TODO":
      raise NotImplementedError(
          f"TODO-nary-[{nary_type}] Unimplemented nary_type: {nary_type}")
    self.instr_name = nary_opname
    return self.fmt_instr()



def main():
  HARMONY_FILE = str(sys.argv[1])
  OUTPUT_TLA_FILE = str(sys.argv[2])
  print("parsing " + HARMONY_FILE + '\n')

  with open(HARMONY_FILE) as f:
    har_json = json.load(f)
  har_instr = har_json["code"]
  har_instr = har_instr[:-1]  # Skip last line (deleting "result" variable)

  tla_instr_lines = []
  for ii, instr in enumerate(har_instr):
    try:
      tla_instr_lines.append(BaseInstr.create(instr["op"], *(ii, instr)).tla_instr())
    except Exception as e:
      if str(e).startswith("TODO-"):
        tla_instr_lines.append(f"----------- {e} ----- {instr}")
      else:
        tla_instr_lines.append(f"----- {repr(e)} ----- {instr}")

  output_module_name = os.path.basename(OUTPUT_TLA_FILE).split(".")[0]
  tla_instr_block = '\n'.join(tla_instr_lines)
  instr_conjunction = " \/ ".join([f"pc{ii}(self)" for ii in range(len(tla_instr_lines))])
  with open(OUTPUT_TLA_FILE, "w") as f:
    f.write(FINAL_OUTPUT_FMT.format(
        output_module_name=output_module_name,
        tla_instr_block=tla_instr_block,
        instr_conjunction=instr_conjunction
        ))


if __name__ == "__main__":
    main()

# TODO:
#   - current contexts are hardcoded? (\E self \in {{"c0", "c1"}})
#   - have this run the harmony compiler too?
#   - force harmony module to be imported somehow? or to exist in same file as output?
#   - fix all the "*params" cruft

import json
import os
import sys


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
      raise ValueError("Unrecognized instr_name: {}".format(instr_name))
    return cls.subclasses[instr_name](*params)

  @staticmethod
  def tla_quotes(s):
    return f'"{s}"'

  @staticmethod
  def har_to_tla_val(val_json, required_type=None):
    if isinstance(val_json, list):
      if (len(val_json) > 1):
        print(val_json)
        raise NotImplementedError("TODO")
      val_json = val_json[0]
    har_type, har_val = val_json["type"], val_json["value"]
    if (required_type is not None) and (har_type != required_type):
      raise ValueError(f"Harmony value type [{har_type}] is not of required type [{required_type}]")
    if har_type == "bool":
      har_val = har_val.upper()
    elif har_type == "atom":
      har_val = BaseInstr.tla_quotes(har_val)
    elif har_type == "pc":
      pass
    elif har_type == "dict":
      if not har_val:
        har_val = "<<>>"
      else:
        raise NotImplementedError("TODO")
    else:
      raise NotImplementedError("TODO")

    return har_val

  def fmt_instr(self, *args):
    arg_list = ", ".join([f"{x}" for x in args])
    return f"pc{self.pc}(ctx) == /\ {self.instr_name}(ctx, {arg_list})"

  def tla_instr(self):
      raise NotImplementedError()  # TODO - add message


@BaseInstr.register_subclass("Frame")
class InstrFrame(BaseInstr):
  def tla_instr(self):
    arg = self.har_instr["args"]
    if arg == "()":
      arg = "INIT"
    return self.fmt_instr(f"<<{self.tla_quotes(arg)}>>", self.pc)

@BaseInstr.register_subclass(["Push", "Store"])
class InstrHandleVal(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(BaseInstr.har_to_tla_val(self.har_instr["value"]), self.pc)

@BaseInstr.register_subclass("Jump")
class InstrJump(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(self.pc, self.har_instr["pc"])

@BaseInstr.register_subclass(["LoadVar", "DelVar"])
class InstrHandleStr(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(self.tla_quotes(self.har_instr["value"]), self.pc)

@BaseInstr.register_subclass("Load")
class InstrLoad(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(
        BaseInstr.har_to_tla_val(self.har_instr["value"], required_type="atom"),
        self.pc)

@BaseInstr.register_subclass(["Return", "Spawn", "Dummy"])
class InstrNoArg(BaseInstr):
  def tla_instr(self):
    return self.fmt_instr(self.pc)


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
      tla_instr_lines.append(BaseInstr.create(instr["op"], *(ii, instr)).tla_instr())

  instr_conjunction = " \/ ".join([f"pc{ii}(self)" for ii in range(len(tla_instr_lines))])

  final_output_fmt = """------------------------------- MODULE {output_module_name} -------------------------------
VARIABLE CTXBAG, SHARED, FAILEDASSERT

INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED, FAILEDASSERT <- FAILEDASSERT

vars == << CTXBAG, SHARED, FAILEDASSERT >>

Init == HarmonyInit

{tla_instr_block}

proc(self) == {instr_conjunction}

Next == (\E self \in {{"c0", "c1"}}: proc(self))

Spec == Init /\ [][Next]_vars

=============================================================================
"""

  output_module_name = os.path.basename(OUTPUT_TLA_FILE).split(".")[0]
  tla_instr_block = '\n'.join(tla_instr_lines)
  with open(OUTPUT_TLA_FILE, "w") as f:
    f.write(final_output_fmt.format(**locals()))


if __name__ == "__main__":
    main()

# TODO:
#   - current contexts are hardcoded? (\E self \in {{"c0", "c1"}})
#   - have this run the harmony compiler too?
#   - Move final_output outside of main()
#   - force harmony module to be imported somehow? or to exist in same file as output?

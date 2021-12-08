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
  def create(cls, instr_name, params):
    if instr_name not in cls.subclasses:
      raise ValueError("Unrecognized instr_name: {}".format(instr_name))
    return cls.subclasses[instr_name](params)

  @classmethod
  def tla_quotes(s):
    return f'"{s}"'

  @classmethod
  def har_to_tla_val(val_json):
    har_type, har_val = val_json["type"], val_json["value"]
    if har_type == "bool":
      har_val = har_val.toupper()
    elif har_type == "atom":
      har_val = self.tla_quotes(har_val)
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
      return f"pc{self.pc}(ctx) == /\ {self.instr_name}(ctx, {", ".join(args)})"

  def tla_instr(self):
      raise NotImplementedError()  # TODO - add message


@BaseInstr.register_subclass("Frame")
class InstrFrame(BaseInstr):
  def tla_instr(self):
    arg = self.har_instr["args"]
    if arg == "()":
      arg = "INIT"
    return self.fmt_instr(f'"{arg}}"', self.pc)

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
    assert self.har_instr["value"]["type"] == "atom"
    return self.fmt_instr(self.tla_quotes(self.har_instr["value"]["value"]), self.pc)

@BaseInstr.register_subclass(["Return", "Spawn"])
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

  tla_instr_lines = []
  for ii, instr in enumerate(har_instr):
      tla_instr_lines.append(BaseInstr.create(instr["op"], ii, instr).tla_instr())

  instr_conjunction = " \/ ".join([f"pc{ii}(self)" for ii in range(len(tla_instr_lines))])

  final_output = f"""\
  ------------------------------- MODULE {os.path.basename(OUTPUT_TLA_FILE)} -------------------------------
  VARIABLE CTXBAG, SHARED

  INSTANCE Harmony WITH  CTXBAG <- CTXBAG, SHARED <- SHARED

  vars == << CTXBAG, SHARED>>

  Init == HarmonyInit

  {'\n'.join(tla_instr_lines)}

  proc(self) == {instr_conjunction}

  Next == (\E self \in {{"c0", "c1"}}: proc(self))

  Spec == Init /\ [][Next]_vars

  =============================================================================
  """

  with open(OUTPUT_TLA_FILE, "w") as f:
    f.write(final_output)


if __name__ == "__main__":
    main()

# TODO:
#   - write out final output
#   - force harmony module to be imported somehow? or to exist in same file as output?

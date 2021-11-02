import json
import sys

HARMONY_FILE = str(sys.argv[1])
print("parsing " + HARMONY_FILE + '\n')

with open(HARMONY_FILE) as f:
    har_json = json.load(f)

tla_nl = '\n \t /\\ '

def tla_tup(*args):
    """makes a TLA tuple out of args"""
    arg_list = []
    for arg in args:
        arg_list.append(str(arg))
    return '<<' + ','.join(arg_list) + '>>'

def tla_cxt_bag(ctxbag):
    """makes a TLA struct out of a context bag (which is a list of tuples)"""
    map = ' |-> '
    ctx_list = []
    for ctx in ctxbag:
        ctx_str = ctx.id + map + tla_tup(ctx.pc, ctx.stack,ctx.vars)
        ctx_list.append(ctx_str)
    return '[' + ','.join(ctx_list) + ']'

class Context():
    def __init__(self):
        # create a context
        self.id = '0' # a unique ID
        self.stack = []
        self.pc = 0
        self.vars = {}

class HState():
    def __init__(self):
        # create an initial Harmony state
        # see https://harmony.cs.cornell.edu/site/reference/language/harmony-vm/

        """a dictionary mapping variable names to values; starts empty"""
        self.shared = {}

        """a list of contexts; starts with init context """
        cxt0        = Context()
        self.ctxbag = [cxt0]

        self.pc     = 0

    def push(self,val):
        self.ctxbag[0].stack.append(val)

    def init_state(self):
        str1 = "Init == "
        str2 = tla_nl + "shared = " + tla_tup(' ')
        str3 = tla_nl + "ctxbag = " + tla_cxt_bag(self.ctxbag)
        print(str1 + str2 + str3)

def parse_line(line,state):
    if line['op'] == 'Frame':
        pass # deal with this later?
    elif line['op'] == 'Push':
        state.pc += 1
        val = line['value']['value']
        state.push(val)
    else :
        pass

def main():
    state = HState()
    state.init_state()
    for line in har_json['code']:
        instr = line['op']
        parse_line(line,state)

if __name__ == "__main__":
    main()

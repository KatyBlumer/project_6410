import json
import sys

HARMONY_FILE = str(sys.argv[1])
print("parsing " + HARMONY_FILE)

with open(HARMONY_FILE) as f:
    har_json = json.load(f)

class Context():
    def __init__(self):
        # create a context
        self.stack = []
        self.pc = []
        self.vars = {}

class HState():
    def __init__(self):
        # create an initial Harmony state
        # see https://harmony.cs.cornell.edu/site/reference/language/harmony-vm/
        #self.code = TODO
        #self.labels = TODO

        """a dictionary mapping variable names to values; starts empty"""
        self.variables = {}

        """a dictionary that maps contexts to values; starts with init context
           values represent number of equivalent contexts in state """
        cxt1        = Context()
        self.ctxbag = {cxt1: 1}

        #self.stopbag = TODO
        #self.choosing = TODO

    def updateState(instr):
        if instr == "Push"



def parse_line(line):
    if line['op'] == 'Frame':
        return ""
    elif line['op'] == 'Push':
        pass
    else :
        pass

def main():
    state = HState()
    for line in har_json['code']:
        instr = line['op']
        updateState(instr)
        #print(parse_line(line))

if __name__ == "__main__":
    main()

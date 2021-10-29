import json
import sys

HARMONY_FILE = str(sys.argv[1])
print("parsing " + HARMONY_FILE)

with open(HARMONY_FILE) as f:
    har_json = json.load(f)

def parse_line(line):
    if line['op'] == 'Frame':
        return ""
    elif line['op'] == 'Push':
        pass
    else :
        pass

def main():
    for line in har_json['code']:
        print(parse_line(line))

if __name__ == "__main__":
    main()

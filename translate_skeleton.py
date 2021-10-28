import json

HARMONY_FILE = "/Users/katyblumer/Documents/harmony-1.2/mycode/x.hvm"

with open(HARMONY_FILE) as f:
    har_json = json.load(f)

for line in har_json['code']:
  print(parse_line(line))


def parse_line(line):
    if line['op'] == 'Frame':
        return ""
    elif line['op'] == 'Push':
        pass  # TODO

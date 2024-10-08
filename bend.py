#!/bin/env python3
import sys
import re
import os

def resolve_line(line):
    if m := re.match(r"^from (?P<file>.*) import \*$", line):
        file = f'{m.group("file")}.bend'
        return resolve(file)
    else:
        return line

def resolve(filename, imports):
    imports.add(filename)
    content = open(filename).read()
    lines = content.split("\n")
    code = ""
    for line in lines:
        if m := re.match(r"^from (?P<file>.*) import \*$", line):
            file = f'{m.group("file")}.bend'
            if file not in imports:
                code += resolve(file, imports)
        else:
            code += line + "\n"
    return code

file = sys.argv[2]
resolved_file = f"{file}.resolved"
imports = set()
open(resolved_file, 'w').write(resolve(file, imports))
args = sys.argv[:]
args[0] = "bend"
args[2] = resolved_file
cmd = ' '.join(args)
os.system(cmd)
os.remove(resolved_file)

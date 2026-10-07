#!/usr/bin/env python3
"""Put Lean sources into the module-system form that Palomar requires.

`moduleize(text)` turns a source that starts with plain `import` lines into

    module

    public import ...

    @[expose] public section
    set_option backward.privateInPublic true

followed by the rest of the file. Exposing every definition keeps the finite
certificate data reducible in importing modules, exactly as before the port.
The transformation is idempotent. The generators call it on their output, and
running this file converts the given Lean files in place:

    python3 scripts/lean_module.py Sarkozy/*.lean ...
"""
from __future__ import annotations

import sys
from pathlib import Path

SECTION = '@[expose] public section\nset_option backward.privateInPublic true\n'


def moduleize(text: str) -> str:
    if text.startswith('module\n'):
        return text
    lines = text.split('\n')
    imports = []
    index = 0
    while index < len(lines) and (lines[index].startswith('import ') or not lines[index].strip()):
        if lines[index].strip():
            imports.append(lines[index])
        index += 1
    if not imports:
        raise ValueError('expected leading import lines')
    header = 'module\n\n' + '\n'.join('public ' + line for line in imports) + '\n\n' + SECTION
    rest = '\n'.join(lines[index:])
    return header + '\n' + rest


def main(paths: list[str]) -> None:
    changed = 0
    for name in paths:
        path = Path(name)
        text = path.read_text()
        new = moduleize(text)
        if new != text:
            path.write_text(new)
            changed += 1
    print(f'{changed} of {len(paths)} files converted')


if __name__ == '__main__':
    main(sys.argv[1:])

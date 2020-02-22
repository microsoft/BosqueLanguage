# SymTest -- The Bosque Language Symbolic Tester

SymTest is a powerful command line tool for symbolically testing Bosque source code. The tool takes the following parameters:

* `-e --entrypoint [entrypoint]` to optionally specify the entrypoint function for the testing -- defaults to `"NSMain::main"`
* `-m --model"` which can be used attempt to extract inputs that trigger a failure (if one it detected)
* `-b --bound [size]` to set the bound the symbolic tester uses -- defaults to 4


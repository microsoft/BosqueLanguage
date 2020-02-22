# ExeGen -- The Bosque Language AoT executable generator

ExeGen is a simple command line tool for producing self contained executable binaries from Bosque source code. The tool takes the following parameters:

* `-e --entrypoint [entrypoint]` to optionally specify the entrypoint function for the executable -- defaults to `"NSMain::main"`
* `-o --outfile [outfile]` to set the name of the output exe -- defaults to `a.exe` or `a.out`
* `-c --compiler [compiler]` to select the compiler to invoke -- defaults to `clang` on Windows and `g++` on Linux/MacOS
* `-l --level"` which can be used to set the compiler build level at:
    - debug -- all asserts/pre/post/invariant checks are enabled, debug symbols are produced, and no optimization is done
    - test -- only test/release checks are enabled, debug symbols are produced, and light optimization is performed
    - release -- only release checks are enabled, no symbols are produced, and aggressive + platform specific optimization is done

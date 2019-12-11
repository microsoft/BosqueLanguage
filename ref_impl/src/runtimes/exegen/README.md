# ExeGen -- The Bosque Language AoT executable generator

ExeGen is a simple command line tool for producing self contained executable binaries from Bosque source code. The tool takes the following parameters:
* `-e --entrypoint [entrypoint]` to optionally specify the entrypoint function for the executable -- defaults to `"NSMain::main"`
* `-o --outfile [outfile]` to set the name of the output exe -- defaults to `a.exe` or `a.out`
* `-c --compiler [compiler]` to select the compiler to invoke -- defaults to `clang` on Windows and `g++` on Linux/MacOS
* `-d --debug"` which can be used to set the compiler to build with debug flags and produce debugger symbols


A sample application for a `max` command line calculator would be to create a file called `max.bsq` with the contents:
```
namespace NSMain;

entrypoint function main(x: Int, y: Int): Int {
    if(x > y) {
        return x;
    }
    else {
        return y;
    }
}
```

Then run the following command to produce the `max.exe` (on Windows executable) which can then be invoked with:
```
> node ref_impl\bin\runtimes\exegen\exegen.js -o max.exe max.bsq
```
Which will create an executable named `max.exe` in the current directory.

Running this executable:
```
> max.exe 1 5
```
Will output `5`.
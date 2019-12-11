# SymTest -- The Bosque Language Symbolic Tester

SymTest is a powerful command line tool for symbolically testing Bosque source code. The tool takes the following parameters:
* `-e --entrypoint [entrypoint]` to optionally specify the entrypoint function for the testing -- defaults to `"NSMain::main"`
* `-m --model"` which can be used attempt to extract inputs that trigger a failure (if one it detected)
* `-b --bound [size]` to set the bound the symbolic tester uses -- defaults to 4

A sample application for a `division` command line calculator would be to create a file called `division.bsq` with the contents:
```
namespace NSMain;

entrypoint function main(x: Int, y: Int): Int 
    //requires y != 0;
{
    return x / y;
}
```

Then run the following command to check for errors:
```
> node bin\runtimes\symtest\symtest.js division.bsq
```
Which will report that an error is possible.

Re-running the symbolic tested with model generation on as follows:
```
> node bin\runtimes\symtest\symtest.js -m division.bsq
```
Will report that an error is possible when `x == 0` and `y == 0`.

By un-commenting the requires line the tester will assume that the required condition is always satisfied and re-running the tester will now report that the code has been verified up to the bound.

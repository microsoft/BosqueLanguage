//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRRegex } from "../../compiler/mir_assembly";
import { SMTExp, SMTValue } from "./smt_exp";
import * as assert from "assert";

//
//TODO: in compiler we need to parse and build AST for regex language we support then in here we need to actually compile it to SMTLib
//

function compileRegexSMTMatch(re: MIRRegex, str: string): SMTExp {
    //
    //TODO: this is a bit of a hack -- we need to implement our own regex lib and make sure it is consistent between typechecker, compiler, and here too!
    //          also need to compile regex str into Z3 version!!!
    //
    let smtre = "[INVALID]";
    if (re.re === "/^\\d$/") {
        smtre = `(re.range "0" "9")`;
    }
    else if (re.re === "/^\\w$/") {
        smtre = `(re.union (re.range "a" "z") (re.range "A" "Z"))`;
    }
    else {
        assert(!re.re.includes("\\") && !re.re.includes("*") && !re.re.includes("+") && !re.re.includes("|"), "Regex support is very limited!!!");
        smtre = `(str.to.re "${re.re.substring(1, re.re.length - 1)}"))`;
    }

    return new SMTValue(`(str.in.re ${str} ${smtre})`);
}

function compileRegexSMTSearch(re: MIRRegex): SMTExp {
    return new SMTValue(`[NOT IMPLEMENTED]`);
}

export {
    compileRegexSMTMatch, compileRegexSMTSearch
};

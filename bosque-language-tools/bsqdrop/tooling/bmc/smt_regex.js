"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const smt_exp_1 = require("./smt_exp");
const assert = require("assert");
//
//TODO: in compiler we need to parse and build AST for regex language we support then in here we need to actually compile it to SMTLib
//
function compileRegexSMTMatch(re, str) {
    //
    //TODO: this is a bit of a hack -- we need to implement our own regex lib and make sure it is consistent between typechecker, compiler, and here too!
    //          also need to compile regex str into Z3 version!!!
    //
    let smtre = "[INVALID]";
    if (re.re === "/\\d/") {
        smtre = `(re.range "0" "9")`;
    }
    else if (re.re === "/\\w/") {
        smtre = `(re.union (re.range "a" "z") (re.range "A" "Z"))`;
    }
    else {
        assert(!re.re.includes("\\") && !re.re.includes("*") && !re.re.includes("+") && !re.re.includes("|"), "Regex support is very limited!!!");
        smtre = `(str.to.re "${re.re.substring(1, re.re.length - 1)}"))`;
    }
    return new smt_exp_1.SMTValue(`(str.in.re ${str} ${smtre})`);
}
exports.compileRegexSMTMatch = compileRegexSMTMatch;
function compileRegexSMTSearch(re) {
    return new smt_exp_1.SMTValue(`[NOT IMPLEMENTED]`);
}
exports.compileRegexSMTSearch = compileRegexSMTSearch;
//# sourceMappingURL=smt_regex.js.map
"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
//
//TODO: in compiler we need to parse and build AST for regex language we support then in here we need to actually compile it to SMTLib
//
function compileRegexCppMatch(re, str, av) {
    const restr = `std::regex re("(${re.re.substring(1, re.re.length - 1).replace(/\\/g, "\\\\")})");`;
    return `${restr} auto ${av} = std::regex_match(${str}->sdata, re);`;
}
exports.compileRegexCppMatch = compileRegexCppMatch;
function compileRegexCppSearch(re) {
    return `[NOT IMPLEMENTED]`;
}
exports.compileRegexCppSearch = compileRegexCppSearch;
//# sourceMappingURL=cpp_regex.js.map
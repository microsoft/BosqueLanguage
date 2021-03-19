//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRRegex } from "../../compiler/mir_assembly";

//
//TODO: in compiler we need to parse and build AST for regex language we support then in here we need to actually compile it
//

function compileRegexCppMatch(re: MIRRegex, str: string, av: string): string {
    const restr = `std::regex re("(${re.re.substring(1, re.re.length - 1).replace(/\\/g, "\\\\")})");`;
    return `${restr} auto ${av} = std::regex_match(${str}->sdata, re);`;
}

function compileRegexCppSearch(re: MIRRegex): string {
    return `[NOT IMPLEMENTED]`;
}

export {
    compileRegexCppMatch, compileRegexCppSearch
};

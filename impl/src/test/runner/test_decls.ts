//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import {MIRFunctionParameter, MIRType} from "../../compiler/mir_assembly";

enum TestResultKind {
    ok,
    errors
}

class ICPPTest {
    readonly resultKind: TestResultKind;
    readonly fuzz: boolean;

    readonly filename: string;

    readonly namespace: string;
    readonly invk: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(resultKind: TestResultKind, fuzz: boolean, filename: string, namespace: string, invk: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.resultKind = resultKind;
        this.fuzz = fuzz;
        this.filename = filename;
        this.namespace = namespace;
        this.invk = invk;
        this.params = params;
        this.resultType = resultType;
    }
}

class SymTest {
    readonly resultKind: TestResultKind;
    readonly syminput: boolean;

    readonly filename: string;

    readonly namespace: string;
    readonly invk: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    readonly trgterror: { file: string, line: number, pos: number } | undefined;

    constructor(resultKind: TestResultKind, syminput: boolean, filename: string, namespace: string, invk: string, params: MIRFunctionParameter[], resultType: MIRType, trgterror: { file: string, line: number, pos: number } | undefined) {
        this.resultKind = resultKind;
        this.syminput = syminput;
        this.filename = filename;
        this.namespace = namespace;
        this.invk = invk;
        this.params = params;
        this.resultType = resultType;
        this.trgterror = trgterror;
    }
}

class SymTestInternalChkShouldFail {
    readonly filename: string;

    readonly namespace: string;
    readonly invk: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(filename: string, namespace: string, invk: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.filename = filename;
        this.namespace = namespace;
        this.invk = invk;
        this.params = params;
        this.resultType = resultType;
    }
}

export {
    TestResultKind,
    ICPPTest, SymTest, SymTestInternalChkShouldFail
};

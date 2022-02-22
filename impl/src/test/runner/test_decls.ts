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

    readonly namespace: string;
    readonly invk: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(resultKind: TestResultKind, fuzz: boolean, namespace: string, invk: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.resultKind = resultKind;
        this.fuzz = fuzz;
        this.namespace = namespace;
        this.invk = invk;
        this.params = params;
        this.resultType = resultType;
    }
}

class SymTest {
    readonly resultKind: TestResultKind;
    readonly fuzz: boolean;

    readonly namespace: string;
    readonly invk: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(resultKind: TestResultKind, fuzz: boolean, namespace: string, invk: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.resultKind = resultKind;
        this.fuzz = fuzz;
        this.namespace = namespace;
        this.invk = invk;
        this.params = params;
        this.resultType = resultType;
    }
}

export {
    TestResultKind,
    ICPPTest, SymTest
};

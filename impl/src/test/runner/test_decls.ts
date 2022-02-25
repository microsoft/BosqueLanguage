//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import {MIRFunctionParameter, MIRType, SymbolicActionMode} from "../../compiler/mir_assembly";

const PARALLEL_COUNT_ICPP = 4;
const PARALLEL_COUNT_SMT = 4;

const SMT_TIMEOUT = 30;

//TODO: should compute max consts in program and then set these limits (numerics) to make sure we can cover them 
const SMT_VOPTS_CHK = {
    INT_MIN: -255,
    INT_MAX: 256,
    SLEN_MAX: 48,
    BLEN_MAX: 32,

    CONTAINER_MAX: 3,
        
    ActionMode: SymbolicActionMode.ChkTestSymbolic
};

const SMT_VOPTS_ERR = {
    INT_MIN: -255,
    INT_MAX: 256,
    SLEN_MAX: 48,
    BLEN_MAX: 32,

    CONTAINER_MAX: 3,
        
    ActionMode: SymbolicActionMode.ErrTestSymbolic
};

enum TestResultKind {
    ok,
    errors
}

class ICPPTest {
    readonly resultKind: TestResultKind;
    readonly fuzz: boolean;

    readonly filename: string;
    readonly namespace: string;
    readonly fname: string;

    readonly invkey: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(resultKind: TestResultKind, fuzz: boolean, filename: string, namespace: string, fname: string, invkey: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.resultKind = resultKind;
        this.fuzz = fuzz;
        this.filename = filename;
        this.namespace = namespace;
        this.fname = fname;
        this.invkey = invkey;
        this.params = params;
        this.resultType = resultType;
    }
}

class SymTest {
    readonly resultKind: TestResultKind;
    
    readonly filename: string;
    readonly namespace: string;
    readonly fname: string;

    readonly invkey: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    readonly trgterror: { file: string, line: number, pos: number } | undefined;

    constructor(resultKind: TestResultKind, filename: string, namespace: string, fname: string, invkey: string, params: MIRFunctionParameter[], resultType: MIRType, trgterror: { file: string, line: number, pos: number } | undefined) {
        this.resultKind = resultKind;
        this.filename = filename;
        this.namespace = namespace;
        this.fname = fname;
        this.invkey = invkey;
        this.params = params;
        this.resultType = resultType;
        this.trgterror = trgterror;
    }
}

class SymTestInternalChkShouldFail {
    readonly filename: string;
    readonly namespace: string;
    readonly fname: string;

    readonly invkey: string;
    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    constructor(filename: string, namespace: string, fname: string, invkey: string, params: MIRFunctionParameter[], resultType: MIRType) {
        this.filename = filename;
        this.namespace = namespace;
        this.fname = fname;
        this.invkey = invkey;
        this.params = params;
        this.resultType = resultType;
    }
}

export {
    PARALLEL_COUNT_ICPP, PARALLEL_COUNT_SMT, SMT_TIMEOUT,
    SMT_VOPTS_CHK, SMT_VOPTS_ERR,
    TestResultKind,
    ICPPTest, SymTest, SymTestInternalChkShouldFail
};

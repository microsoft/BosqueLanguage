//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRConstructableEntityTypeDecl, MIREntityTypeDecl, MIRInvokeBodyDecl, MIRPCode, MIRPrimitiveListEntityTypeDecl, MIRType } from "../../compiler/mir_assembly";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTFunction, SMTFunctionUninterpreted } from "./smt_assembly";
import { BVEmitter, SMTCallGeneral, SMTCallSimple, SMTCond, SMTConst, SMTExists, SMTExp, SMTForAll, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

import * as assert from "assert";

class RequiredListConstructors {
    //always empty, 1, 2, 3
    //always slice
    //always concat2

    havoc: boolean = false;

    fill: boolean = false;
    
    filter: boolean = false;

    map: Map<string, {code: MIRPCode, fromtype: MIRType, totype: MIRType, isidx: boolean}> = new Map<string, {code: MIRPCode, fromtype: MIRType, totype: MIRType, isidx: boolean}>();
}

type SMTConstructorGenCode = {
    uf: SMTFunctionUninterpreted[],
    if: SMTFunction[],
    cons: { cname: string, cargs: { fname: string, ftype: SMTType }[] }
};

class RequiredListDestructors {
    //always get

    safecheckpred: Map<string, {code: MIRPCode, isidx: boolean}> = new Map<string, {code: MIRPCode, isidx: boolean}>();
    safecheckfn: Map<string, {code: MIRPCode, rtype: MIRType, isidx: boolean}> = new Map<string, {code: MIRPCode, rtype: MIRType, isidx: boolean}>();
    isequence: Map<string, {code: MIRPCode, isidx: boolean}> = new Map<string, {code: MIRPCode, isidx: boolean}>();

    haspredcheck: Map<string, {code: MIRPCode, isidx: boolean}> = new Map<string, {code: MIRPCode, isidx: boolean}>();

    findIndexOf: Map<string, {code: MIRPCode, isidx: boolean}> = new Map<string, {code: MIRPCode, isidx: boolean}>();
    findLastIndexOf: Map<string, {code: MIRPCode, isidx: boolean}> = new Map<string, {code: MIRPCode, isidx: boolean}>();

    sum: boolean = false;
    strconcat: boolean = false;
    strjoin: boolean = false;
}

type SMTDestructorGenCode = {
    uf: SMTFunctionUninterpreted[],
    if: SMTFunction[]
};

class ListOpsInfo {
    readonly ltype: MIRType;
    readonly ctype: MIRType;

    consops: RequiredListConstructors;
    dops: RequiredListDestructors;

    constructor(ltype: MIRType, ctype: MIRType) {
        this.ltype = ltype;
        this.ctype = ctype;

        this.consops = new RequiredListConstructors();
        this.dops = new RequiredListDestructors();
    }
}

class ListOpsManager {
    readonly vopts: VerifierOptions
    readonly temitter: SMTTypeEmitter;
    readonly numgen: BVEmitter;
    readonly safecalls: Set<MIRInvokeKey>; 

    rangenat: boolean = false;
    rangeint: boolean = false;

    ops: Map<string, ListOpsInfo> = new Map<string, ListOpsInfo>();

    private tmpvarctr = 0;

    private booltype: SMTType;
    private nattype: SMTType;
    
    generateTempName(): string {
        return `_@tmpvar_cc@${this.tmpvarctr++}`;
    }

    constructor(vopts: VerifierOptions, temitter: SMTTypeEmitter, numgen: BVEmitter, safecalls: Set<MIRInvokeKey>) {
        this.vopts = vopts;
        this.temitter = temitter;
        this.numgen = numgen;
        this.safecalls = safecalls;

        this.booltype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Bool"));
        this.nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));
    }

    private ensureOpsFor(encltype: MIRType): ListOpsInfo {
        if (!this.ops.has(encltype.typeID)) {
            const stypeinfo = this.temitter.assembly.entityDecls.get(encltype.typeID) as MIRPrimitiveListEntityTypeDecl;
            const ctype = stypeinfo.terms.get("T") as MIRType;

            this.ops.set(encltype.typeID, new ListOpsInfo(encltype, ctype));
        }

        return this.ops.get(encltype.typeID) as ListOpsInfo;
    }

    registerHavoc(ltype: MIRType): string {
        const ops = this.ensureOpsFor(ltype);

        ops.consops.havoc = true;
        return this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "havoc");
    }

    processHavoc(ltype: MIRType, path: SMTVar): SMTExp {
        const ops = this.ensureOpsFor(ltype);

        ops.consops.havoc = true;
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "havoc"), [path]);
    }

    processLiteralK_Pos(ltype: MIRType, values: SMTExp[]): SMTExp {
        const opname = `list_${values.length}`;
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), opname), values);
    }

    processGet(ltype: MIRType, l: SMTExp, n: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "get");
        //get always registered

        return new SMTCallSimple(op, [l, n]);
    }

    processSafePredCheck(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "safeCheckPred" + (isidx ? "_idx" : ""), code);

        ops.dops.safecheckpred.set(code, {code: pcode, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processSafeFnCheck(ltype: MIRType, rtype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp,capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "safeCheckFn" + (isidx ? "_idx" : ""), code);

        ops.dops.safecheckfn.set(code, {code: pcode, rtype: rtype, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processISequence(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "isequence" + (isidx ? "_idx" : ""), code);

        ops.dops.isequence.set(code, {code: pcode, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processHasPredCheck(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "hasPredCheck" + (isidx ? "_idx" : ""), code);

        ops.dops.haspredcheck.set(code, {code: pcode, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processFindIndexOf(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findIndexOf" + (isidx ? "_idx" : ""), code);

        ops.dops.findIndexOf.set(code, {code: pcode, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processFindLastIndexOf(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findLastIndexOf" + (isidx ? "_idx" : ""), code);

        ops.dops.findLastIndexOf.set(code, {code: pcode, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processConcat2(ltype: MIRType, l1: SMTExp, l2: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const op = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "concat2");
        //concat always registered

        return new SMTCallSimple(op, [l1, l2, count]);
    }

    processSlice(ltype: MIRType, l1: SMTExp, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const op = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "slice");
        //slice always registered 

        return new SMTCallSimple(op, [l1, start, end, count]);
    }

    processRangeOfIntOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        this.rangeint = true;

        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfInt"),  [start, end, count]);
    }

    processRangeOfNatOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        this.rangenat = true;
        
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfNat"),  [start, end, count]);
    }

    processFillOperation(ltype: MIRType, count: SMTExp, value: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "fill");
        ops.consops.fill = true;

        return new SMTCallSimple(op, [count, value]);
    }

    processMap(ltype: MIRType, intotype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTExp, count: SMTExp, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(intotype);
        const op = this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(intotype), "map" + (isidx ? "_idx" : ""), code);

        ops.consops.map.set(code, {code: pcode, fromtype: ltype, totype: intotype, isidx: isidx});
        return new SMTCallGeneral(op, [l, count, ...capturedargs]);
    }

    processFilter(ltype: MIRType, isidx: boolean, code: string, pcode: MIRPCode, l: SMTVar, isq: SMTVar, count: SMTVar, capturedargs: SMTVar[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "filter" + (isidx ? "_idx" : ""));

        ops.consops.filter = true;
        return new SMTCallGeneral(op, [l, isq, count, ...capturedargs]);
    }

    processSum(ltype: MIRType, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "sum");

        ops.dops.sum = true;
        return new SMTCallGeneral(op, [l]);
    }

    processStrConcat(ltype: MIRType, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "strconcat");

        ops.dops.strconcat = true;
        return new SMTCallGeneral(op, [l]);
    }

    processStrJoin(ltype: MIRType, l: SMTExp, sep: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "strjoin");

        ops.dops.strjoin = true;
        return new SMTCallGeneral(op, [l, sep]);
    }

    generateConsCallName(ltype: SMTType, opname: string): string {
        return `_@@consop_${ltype.name}_${opname}`;
    }

    generateConsCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `_@@consop_${ltype.name}_${opname}_using_${this.temitter.lookupFunctionName(code)}`;
    }

    generateDesCallName(ltype: SMTType, opname: string): string {
        return `_@@desop_${ltype.name}_${opname}`;
    }

    generateDesCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `_@@desop_${ltype.name}_${opname}_using_${this.temitter.lookupFunctionName(code)}`;
    }

    generateULITypeFor(ltype: SMTType): SMTType {
        return new SMTType(ltype.name + "$uli", "[INTERNAL TYPE]", ltype.typeID + "$uli");
    }

    generateULIFieldFor(ltype: SMTType, consname: string, fname: string): string {
        return this.generateConsCallName_Direct(ltype, consname) + "_" + fname;
    }

    generateULIFieldUsingFor(ltype: SMTType, consname: string, code: string, fname: string): string {
        return this.generateConsCallNameUsing_Direct(ltype, consname, code) + "_" + fname;
    }

    generateConsCallName_Direct(ltype: SMTType, opname: string): string {
        return `_@@cons_${ltype.name}_${opname}`;
    }

    generateConsCallNameUsing_Direct(ltype: SMTType, opname: string, code: string): string {
        return `_@@cons_${ltype.name}_${opname}_using_${this.temitter.lookupFunctionName(code)}`;
    }

    generateListSizeCall(exp: SMTExp, etype: SMTType): SMTExp {
        return new SMTCallSimple(`${etype.name}@size`, [exp]);
    }

    generateListContentsCall(exp: SMTExp, etype: SMTType): SMTExp {
        return new SMTCallSimple(`${etype.name}@uli`, [exp]);
    }

    generateGetULIFieldFor(ltype: SMTType, consname: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldFor(ltype, consname, fname), [arg]);
    }

    generateGetULIFieldUsingFor(ltype: SMTType, consname: string, code: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldUsingFor(ltype, consname, code, fname), [arg]);
    }

    emitConstructorEmpty(mtype: MIRType, ltype: SMTType): SMTConstructorGenCode {
        const ffunc = new SMTCallSimple(this.temitter.getSMTConstructorName(mtype).cons, [
            new SMTConst("BNat@zero"),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), [])
        ]);

        return {
            cons: {
                cname: this.generateConsCallName_Direct(ltype, "empty"), 
                cargs: []
            },
            if: [new SMTFunction(this.generateConsCallName(ltype, "empty"), [], undefined, 0, ltype, ffunc)],
            uf: []
        }
    }

    ////////
    //Slice
    emitConstructorSlice(mtype: MIRType, ltype: SMTType): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            new SMTVar("count"),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [new SMTVar("l"), new SMTVar("start"), new SMTVar("end")])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "slice"), cargs: [{ fname: this.generateULIFieldFor(ltype, "slice", "l"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "slice", "start"), ftype: this.nattype }, { fname: this.generateULIFieldFor(ltype, "slice", "end"), ftype: this.nattype }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, "slice"), [{ vname: "l", vtype: ltype }, { vname: "start", vtype: this.nattype }, { vname: "end", vtype: this.nattype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Concat
    emitConstructorConcat2(mtype: MIRType, ltype: SMTType): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            new SMTVar("count"),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [new SMTVar("l1"), new SMTVar("l2")])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "concat2"), cargs: [{ fname: this.generateULIFieldFor(ltype, "concat2", "left"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "concat2", "right"), ftype: ltype }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, "concat2"), [{ vname: "l1", vtype: ltype }, { vname: "l2", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Havoc
    emitConstructorHavoc(mtype: MIRType, ltype: SMTType, ctype: MIRType): SMTConstructorGenCode {
        assert(this.vopts.EnableCollection_SmallHavoc || this.vopts.EnableCollection_LargeHavoc);

        const lcons = this.temitter.getSMTConstructorName(mtype).cons;
        const ptype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::HavocSequence"));

        const size = "_@size";
        const sizev = new SMTVar(size);

        const emptyopt = {
            test: SMTCallSimple.makeEq(sizev, new SMTConst("BNat@zero")),
            result: this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTConst(`${this.temitter.lookupTypeName(mtype.typeID)}@empty_const`))
        };

        const smallmodeopts = [
            {
                test: SMTCallSimple.makeEq(sizev, this.numgen.emitSimpleNat(1)),
                result: new SMTLetMulti([
                    { vname: "_@val0", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(0)) }
                    ],
                    new SMTIf(this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val0")),
                        this.temitter.generateErrorResultAssert(mtype),
                        this.temitter.generateResultTypeConstructorSuccess(mtype,
                            new SMTCallSimple(this.generateConsCallName(ltype, "list_1"), [
                                this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val0"))
                            ])
                        )
                    )
                )
            },
            {
                test: SMTCallSimple.makeEq(sizev, this.numgen.emitSimpleNat(2)),
                result: new SMTLetMulti([
                    { vname: "_@val0", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(0)) },
                    { vname: "_@val1", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(1)) }
                ],
                    new SMTIf(SMTCallSimple.makeOrOf(
                        this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val0")),
                        this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val1"))
                    ),
                        this.temitter.generateErrorResultAssert(mtype),
                        this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "list_2"), [
                            this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val0")), 
                            this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val1"))
                        ]))
                    )
                )
            },
            {
                test: SMTCallSimple.makeEq(sizev, this.numgen.emitSimpleNat(3)),
                result: new SMTLetMulti([
                    { vname: "_@val0", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(0)) },
                    { vname: "_@val1", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(1)) },
                    { vname: "_@val2", value: this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), this.numgen.emitSimpleNat(2)) }
                ],
                    new SMTIf(new SMTCallSimple("or", [
                        this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val0")),
                        this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val1")),
                        this.temitter.generateResultIsErrorTest(ctype, new SMTVar("_@val2"))
                    ]),
                        this.temitter.generateErrorResultAssert(mtype),
                        this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "list_3"), [
                            this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val0")), 
                            this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val1")), 
                            this.temitter.generateResultGetSuccess(ctype, new SMTVar("_@val2"))
                        ]))
                    )
                )
            }
        ];

        let largemodeopts = new SMTIf(new SMTForAll([{ vname: "_@n", vtype: this.nattype }],
            new SMTCallSimple("=>", [
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), sizev]),
                    this.temitter.generateResultIsSuccessTest(ctype, this.temitter.generateHavocConstructorCall(ctype, new SMTVar("path"), new SMTVar("_@n")))
                ])
            ),
            this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(lcons, [sizev, new SMTCallSimple(this.generateConsCallName_Direct(ltype, "havoc"), [new SMTVar("path")])])),
            this.temitter.generateErrorResultAssert(mtype)
        );

        let ffunc: SMTExp = new SMTConst("[UNINIT]");
        if(this.vopts.EnableCollection_SmallHavoc && !this.vopts.EnableCollection_LargeHavoc) {
            ffunc = new SMTLet(size, new SMTCallSimple("ListSize@UFCons_API", [new SMTVar("path")]),
                new SMTCond([emptyopt, ...smallmodeopts.slice(0, smallmodeopts.length - 1)], smallmodeopts[smallmodeopts.length - 1].result)
            );
        }
        else if (!this.vopts.EnableCollection_SmallHavoc && this.vopts.EnableCollection_LargeHavoc) {
            ffunc = new SMTLet(size, new SMTCallSimple("ListSize@UFCons_API", [new SMTVar("path")]),
                new SMTIf(emptyopt.test, emptyopt.result, largemodeopts)
            );
        }
        else {
            ffunc = new SMTLet(size, new SMTCallSimple("ListSize@UFCons_API", [new SMTVar("path")]), 
                new SMTCond([emptyopt, ...smallmodeopts], largemodeopts)
            );
        }

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "havoc"), cargs: [{ fname: this.generateULIFieldFor(ltype, "havoc", "path"), ftype: ptype }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, "havoc"), [{ vname: "path", vtype: ptype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Fill
    emitConstructorFill(mtype: MIRType, ltype: SMTType, ctype: MIRType): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            new SMTVar("count"),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "fill"), [new SMTVar("value")])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "fill"), cargs: [{ fname: this.generateULIFieldFor(ltype, "fill", "value"), ftype: this.temitter.getSMTTypeFor(ctype) }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, "fill"), [{ vname: "value", vtype: this.temitter.getSMTTypeFor(ctype) }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //RangeNat/Int
    emitConstructorRange(mtype: MIRType, ltype: SMTType, ctype: MIRType): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const opname = ctype.typeID === "NSCore::Nat" ? "rangeOfNat" : "rangeOfInt";
        const rtype = this.temitter.getSMTTypeFor(ctype);
        
        const ffunc = new SMTCallSimple(lcons, [
            new SMTCallSimple("bvsub", [new SMTVar("end"), new SMTVar("start")]),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), [new SMTVar("start"), new SMTVar("end")])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: [{ fname: this.generateULIFieldFor(ltype, opname, "start"), ftype: rtype }, { fname: this.generateULIFieldFor(ltype, opname, "end"), ftype: rtype }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), [{ vname: "start", vtype: rtype }, { vname: "end", vtype: rtype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //LiteralK
    emitConstructorLiteralK(mtype: MIRType, ltype: SMTType, ctype: MIRType, k: number): SMTConstructorGenCode {
        const smtctype = this.temitter.getSMTTypeFor(ctype);
        
        const opname = `list_${k}`;

        let kfields: {fname: string, ftype: SMTType}[] = [];
        let kfargs: {vname: string, vtype: SMTType}[] = [];
        for(let i = 0; i < k; ++i) {
            kfields.push({fname: this.generateULIFieldFor(ltype, opname, `_${i}_`), ftype: smtctype});
            kfargs.push({vname: `_${i}_`, vtype: smtctype});
        }

        //default construct
        const ffunc = new SMTCallSimple(this.temitter.getSMTConstructorName(mtype).cons, [
            this.numgen.emitSimpleNat(k),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), kfargs.map((arg) => new SMTVar(arg.vname)))
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: kfields },
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), kfargs, undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Filter
    emitConstructorFilter(ltype: SMTType, mtype: MIRType): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc: SMTExp = this.temitter.generateResultTypeConstructorSuccess(mtype,
            new SMTCallSimple(lcons, [
                new SMTCallSimple("ISequence@size", [new SMTVar("isq")]),
                new SMTCallSimple(this.generateConsCallName_Direct(ltype, "filter"), [new SMTVar("l"), new SMTVar("isq")])
            ])
        );

        const iseqtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::ISequence"));
        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "filter"), cargs: [{ fname: this.generateULIFieldFor(ltype, "filter", "l"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "filter", "isq"), ftype: iseqtype }] },
            if: [new SMTFunction(this.generateConsCallName(ltype, "filter"), [{ vname: "l", vtype: ltype }, { vname: "isq", vtype: iseqtype }, { vname: "osize", vtype: this.nattype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Map
    emitConstructorMap(ltype: SMTType, mtype: MIRType, fromtype: MIRType, isidx: boolean, code: string, pcode: MIRPCode): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;
        const constype = this.temitter.getSMTTypeFor(mtype);
        const mapname = "map" + (isidx ? "_idx" : "");

        const capturedfields = this.generateCapturedFieldInfoFor(ltype, mapname, isidx ? 2 : 1, code, pcode);
        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        const ffunc = this.temitter.generateResultTypeConstructorSuccess(mtype,
            new SMTCallSimple(lcons, [
                new SMTVar("count"),
                new SMTCallSimple(this.generateConsCallNameUsing_Direct(constype, mapname, code), [new SMTVar("l"), ...capturedargs])
            ])
        );

        return {
            cons: { cname: this.generateConsCallNameUsing_Direct(constype, mapname, code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, mapname, code, "l"), ftype: this.temitter.getSMTTypeFor(fromtype) }, ...capturedfields] },
            if: [new SMTFunction(this.generateConsCallNameUsing(constype, mapname, code), [{ vname: "l", vtype: this.temitter.getSMTTypeFor(fromtype) }, { vname: "count", vtype: this.nattype }, ...capturedparams], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Get
    emitDestructorGet_Slice(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        return new SMTCallSimple(getop, [
            this.generateGetULIFieldFor(ltype, "slice", "l", ll),
            new SMTCallSimple("bvadd", [
                n,
                this.generateGetULIFieldFor(ltype, "slice", "start", ll)
            ])
        ]);
    }

    emitDestructorGet_Concat2(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        const l1 = "_@l1";
        const l1v = new SMTVar(l1);

        const l1s = "_@l1size";
        const l1sv = new SMTVar(l1s);

        return new SMTLet(l1, this.generateGetULIFieldFor(ltype, "concat2", "left", ll),
            new SMTLet(l1s, this.generateListSizeCall(l1v, ltype),
                new SMTIf(new SMTCallSimple("bvult", [n, l1sv]),
                    new SMTCallSimple(getop, [l1v, n]),
                    new SMTCallSimple(getop, [this.generateGetULIFieldFor(ltype, "concat2", "right", ll), new SMTCallSimple("bvsub", [n, l1sv])])
                )
            )
        );
    }

    emitDestructorGet_K(ltype: SMTType, ll: SMTVar, n: SMTVar, k: number, ): SMTExp {
        if (k === 1) {
            return this.generateGetULIFieldFor(ltype, "list_1", "_0_", ll);
        }
        else {
            let kops: { test: SMTExp, result: SMTExp }[] = [];

            for (let i = 0; i < k - 1; ++i) {
                kops.push({
                    test: SMTCallSimple.makeEq(n, this.numgen.emitSimpleNat(i)),
                    result: this.generateGetULIFieldFor(ltype, `list_${k}`, `_${i}_`, ll)
                });
            }
            
            const klast = this.generateGetULIFieldFor(ltype, `list_${k}`, `_${k - 1}_`, ll)
            return new SMTCond(
                kops,
                klast
            );
        }
    }

    emitDestructorGet_Filter(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        return new SMTLet("_@olist", this.generateGetULIFieldFor(ltype, "filter", "l", ll),
            new SMTCallSimple(getop, [new SMTVar("_@olist"), new SMTCallSimple("ISequence@get", [this.generateGetULIFieldFor(ltype, "filter", "isq", ll), n])])
        );
    }

    emitDestructorGet_Map(ctype: MIRType, srcltype: SMTType, fromtype: MIRType, ll: SMTVar, n: SMTVar, isidx: boolean, code: string, pcode: MIRPCode): SMTExp {
        const getop = this.generateDesCallName(this.temitter.getSMTTypeFor(fromtype), "get");
        const mapname = "map" + (isidx ? "_idx" : "");

        const capturedfieldlets = this.generateCapturedFieldLetsInfoFor(srcltype, mapname, isidx ? 2 : 1, code, pcode, ll);
        const largs = isidx ? [new SMTCallSimple(getop, [new SMTVar("_@olist"), n]), n] :  [new SMTCallSimple(getop, [new SMTVar("_@olist"), n])];

        return new SMTLet("_@olist", this.generateGetULIFieldUsingFor(srcltype, mapname, code, "l", ll),
            this.processCapturedFieldLets(capturedfieldlets, 
                this.generateLambdaCallKnownSafe(code, ctype, largs, capturedfieldlets.map((cfl) => new SMTVar(cfl.vname)))
            )
        );
    }

    emitDestructorGet(ltype: SMTType, ctype: MIRType, consopts: RequiredListConstructors | undefined): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get");
        const llv = new SMTVar("_@list_contents");

        let tsops: { test: SMTExp, result: SMTExp }[] = [];

        for(let i = 1; i <= 3; ++i) {
            tsops.push({
                test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, `list_${i}`), llv),
                result: this.emitDestructorGet_K(ltype, llv, new SMTVar("n"), i)
            });
        }

        //always slice
        tsops.push({
            test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "slice"), llv),
            result: this.emitDestructorGet_Slice(getop, ltype, llv, new SMTVar("n"))
        });

        //always concat2
        tsops.push({
            test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "concat2"), llv),
            result: this.emitDestructorGet_Concat2(getop, ltype, llv, new SMTVar("n"))
        });

        if (consopts !== undefined) {
            if (consopts.havoc) {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "havoc"), llv),
                    result: this.temitter.generateResultGetSuccess(ctype, this.temitter.generateHavocConstructorCall(ctype, this.generateGetULIFieldFor(ltype, "havoc", "path", llv), new SMTVar("n")))
                });
            }

            if (consopts.fill) {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "fill"), llv),
                    result: this.generateGetULIFieldFor(ltype, "fill", "v", llv)
                });
            }

            if (this.rangenat && ctype.typeID === "NSCore::Nat") {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "rangeOfNat"), llv),
                    result: new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), new SMTVar("n")])
                });
            }

            if (this.rangeint && ctype.typeID === "NSCore::Int") {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "rangeOfInt"), llv),
                    result: new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), new SMTVar("n")])
                });
            }

            if(consopts.filter) {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallName_Direct(ltype, "filter"), llv),
                    result: this.emitDestructorGet_Filter(getop, ltype, llv, new SMTVar("n"))
                });
            }

            consopts.map.forEach((omi, code) => {
                tsops.push({
                    test: SMTCallSimple.makeIsTypeOp(this.generateConsCallNameUsing_Direct(ltype, omi.isidx ? "map_idx" : "map", code), llv),
                    result: this.emitDestructorGet_Map(ctype, ltype, omi.fromtype, llv, new SMTVar("n"), omi.isidx, code, omi.code)
                });
            });
        }

        const ffunc = new SMTLetMulti([{ vname: "_@list_contents", value: this.generateListContentsCall(new SMTVar("l"), ltype) }],
            new SMTCond(tsops.slice(0, tsops.length - 1), tsops[tsops.length - 1].result)
        );

        return {
            if: [new SMTFunction(this.generateDesCallName(ltype, "get"), [{ vname: "l", vtype: ltype }, { vname: "n", vtype: this.nattype}], undefined, 0, this.temitter.getSMTTypeFor(ctype), ffunc)],
            uf: []
        };
    }

    ////////
    //SafeCheck
    emitSafeCheckPred(ltype: SMTType, mtype: MIRType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const restype = this.temitter.getMIRType("NSCore::Bool");
        const safename = "safeCheckPred" + (isidx ? "_idx" : "");

        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@n")]);
        const largs = isidx ? [getcall, new SMTVar("_@n")] : [getcall];

        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        if (this.safecalls.has(code)) {
            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, safename, code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(mtype), this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTVar("l")))],
                uf: []
            };
        }
        else {
            const tecase = new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                SMTCallSimple.makeAndOf(
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTVar("count")]),
                    SMTCallSimple.makeEq(
                        this.generateLambdaCallGeneral(code, restype, largs, capturedargs), 
                        this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))
                    )
                )
            );

            const gecase = new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                SMTCallSimple.makeAndOf(
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTVar("count")]),
                    SMTCallSimple.makeEq(
                        this.generateLambdaCallGeneral(code, restype, largs, capturedargs), 
                        this.temitter.generateErrorResultAssert(restype)
                    )
                )
            );

            const ffunc = new SMTCond([
                { test: tecase, result: this.temitter.generateResultTypeConstructorError(mtype, new SMTConst("ErrorID_Target")) },
                { test: gecase, result: this.temitter.generateErrorResultAssert(mtype) }
            ],
                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTVar("l"))
            );

            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, safename, code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
                uf: []
            };
        }
    }

    emitSafeCheckFn(ltype: SMTType, mtype: MIRType, restype: MIRType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const safename = "safeCheckFn" + (isidx ? "_idx" : "");
        
        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@n")]);
        const largs = isidx ? [getcall, new SMTVar("_@n")] : [getcall];

        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        if (this.safecalls.has(code)) {
            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, safename, code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(mtype), this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTVar("l")))],
                uf: []
            };
        }
        else {
            const tecase = new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTVar("count")]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, largs, capturedargs), 
                        this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))
                    ])
                ])
            );

            const gecase = new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTVar("count")]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, largs, capturedargs), 
                        this.temitter.generateErrorResultAssert(restype)
                    ])
                ])
            );

            const ffunc = new SMTCond([
                { test: tecase, result: this.temitter.generateResultTypeConstructorError(mtype, new SMTConst("ErrorID_Target")) },
                { test: gecase, result: this.temitter.generateErrorResultAssert(mtype) }
            ],
                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTVar("l"))
            );

            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, safename, code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
                uf: []
            };
        }
    }

    ////////
    //ISequence
    emitDestructorISequence(ltype: SMTType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const iseqtype = this.temitter.getMIRType("NSCore::ISequence");
        const smtiseqtype = this.temitter.getSMTTypeFor(iseqtype);

        const [capturedargs, capturedparams, ufpickargs] = this.generateCapturedInfoFor(pcode, isidx ? 3 : 2);
        const cff = new SMTFunctionUninterpreted(this.generateConsCallNameUsing(smtiseqtype, "ISequence@@cons", code), [ltype, this.nattype, ...ufpickargs], smtiseqtype);

        const cvar = "_@cseq";
        const getop = this.generateDesCallName(ltype, "get");

        //size(res) <= size(arg0)
        const assertsize = new SMTCallSimple("bvule", [new SMTCallSimple("ISequence@size", [new SMTVar(cvar)]), new SMTVar("count")]);

        //\forall n \in [0, size(res)) get(res) < size(arg0)
        const assertrange = new SMTCallSimple("ISequence@assertValuesRange", [new SMTVar(cvar), new SMTVar("count")]);

        //sorted constraint
        const assertsorted = new SMTCallSimple("ISequence@assertSorted", [new SMTVar(cvar)]);

        //\forall j (j \in [lower, upper) /\ p(get(arg0, j))) => (\exists n \in [0, size(res)) /\ get(res, n) = j)
        const getarglj = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@j")]);
        const largslj = isidx ? [getarglj, new SMTVar("_@j")] : [getarglj];
        const fromassert = new SMTForAll([{ vname: "_@j", vtype: this.nattype }],
            new SMTCallSimple("=>", [
                SMTCallSimple.makeAndOf(
                    new SMTCallSimple("bvult", [new SMTVar("_@j"), new SMTVar("count")]),
                    this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), largslj, capturedargs)
                ),
                new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                    SMTCallSimple.makeAndOf(
                        new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTCallSimple("ISequence@size", [new SMTVar(cvar)])]),
                        SMTCallSimple.makeEq(
                            new SMTCallSimple("ISequence@get", [new SMTVar(cvar), new SMTVar("_@n")]),
                            new SMTVar("_@j")
                        )
                    )
                )
            ])
        );

        //\forall n (n \in [0, size(res)), get(res, n) = j) => p(get(arg0, j))) --- j \in [lower, upper) is checked by the ISequence@assertValuesRange action
        const getarglacc = new SMTCallSimple(getop, [new SMTVar("l"), new SMTCallSimple("ISequence@get", [new SMTVar(cvar), new SMTVar("_@n")])]);
        const largslacc = isidx ? [getarglacc, new SMTCallSimple("ISequence@get", [new SMTVar(cvar), new SMTVar("_@n")])] : [getarglacc];
        const toassert = new SMTForAll([{ vname: "_@n", vtype: this.nattype }],
            new SMTCallSimple("=>", [
                new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTCallSimple("ISequence@size", [new SMTVar(cvar)])]),
                this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), largslacc, capturedargs)
            ])
        );

        const icons = new SMTCallSimple(this.generateConsCallNameUsing(smtiseqtype, "ISequence@@cons", code), [new SMTVar("l"), new SMTVar("count"), ...capturedargs]);

        const fbody = new SMTLet(cvar, icons,
            new SMTIf(
                SMTCallSimple.makeAndOf(assertsize, assertrange, assertsorted, fromassert, toassert),
                new SMTCallSimple("$Result_ISequence@success", [new SMTVar(cvar)]),
                new SMTCallSimple("$Result_ISequence@error", [new SMTConst("ErrorID_AssumeCheck")])
            )
        );

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "isequence" + (isidx ? "_idx" : ""), code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }, ...capturedparams], undefined, 0, this.temitter.generateResultType(iseqtype), fbody)],
            uf: [cff]
        };
    }

    ////////
    //HasPredCheck
    emitDestructorHasPredCheck(ltype: SMTType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@n")]);
        const largs = isidx ? [getcall, new SMTVar("_@n")] : [getcall];

        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        const ffunc = this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Bool"),
            new SMTExists([{ vname: "_@n", vtype: this.nattype }],
                SMTCallSimple.makeAndOf(
                    new SMTCallSimple("bvult", [new SMTVar("_@n"), new SMTVar("count")]),
                    this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), largs, capturedargs)
                )
            )
        );

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "hasPredCheck" + (isidx ? "_idx" : ""), code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(this.temitter.getMIRType("NSCore::Bool")), ffunc)],
            uf: []
        };
    }

    ////////
    //FindIndexOf
    emitDestructorFindIndexOf(ltype: SMTType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const [nn, suf] = this.emitDestructorFindIndexOf_Shared(ltype, isidx, code, pcode, new SMTVar("l"), new SMTVar("count"), new SMTConst("BNat@zero"));
        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@j")]);
        const largs = isidx ? [getcall, new SMTVar("_@j")] : [getcall];

        const mirbool = this.temitter.getMIRType("NSCore::Bool");
        const mirnat = this.temitter.getMIRType("NSCore::Nat");

        const ffunc = new SMTLet("_@n", nn,
            new SMTIf(this.temitter.generateResultIsErrorTest(mirnat, new SMTVar("_@n")),
                new SMTVar("_@n"),
                new SMTIf(
                    new SMTForAll([{ vname: "_@j", vtype: this.nattype }],
                        new SMTCallSimple("=>", [
                            new SMTCallSimple("bvult", [new SMTVar("_@j"), this.temitter.generateResultGetSuccess(mirnat, new SMTVar("_@n"))]),
                            SMTCallSimple.makeNot(this.generateLambdaCallKnownSafe(code, mirbool, largs, capturedargs))
                        ])
                    ),
                    this.temitter.generateResultTypeConstructorSuccess(mirnat, new SMTCallSimple("bvadd", [new SMTVar("bidx"), this.temitter.generateResultGetSuccess(mirnat,new SMTVar("_@n"))])),
                    this.temitter.generateErrorResultAssert(mirnat)
                )
            )
        );

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "findIndexOf" + (isidx ? "_idx" : ""), code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, { vname: "bidx", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(this.temitter.getMIRType("NSCore::Nat")), ffunc)],
            uf: [suf]
        };
    }

    ////////
    //FindLastIndexOf
    emitDestructorFindIndexOfLast(ltype: SMTType, isidx: boolean, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const [nn, suf] = this.emitDestructorFindIndexOf_Shared(ltype, isidx, code, pcode, new SMTVar("l"), new SMTVar("count"), new SMTConst("BNat@max"));
        const [capturedargs, capturedparams] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [new SMTVar("l"), new SMTVar("_@j")]);
        const largs = isidx ? [getcall, new SMTVar("_@j")] : [getcall];

        const mirbool = this.temitter.getMIRType("NSCore::Bool");
        const mirnat = this.temitter.getMIRType("NSCore::Nat");

        const ffunc = new SMTLet("_@n", nn,
            new SMTIf(this.temitter.generateResultIsErrorTest(mirnat, new SMTVar("_@n")),
                new SMTVar("_@n"),
                new SMTIf(
                    new SMTForAll([{ vname: "_@j", vtype: this.nattype }],
                        new SMTCallSimple("=>", [
                            new SMTCallSimple("bvult", [this.temitter.generateResultGetSuccess(mirnat, new SMTVar("_@n")), new SMTVar("_@j")]),
                            SMTCallSimple.makeNot(this.generateLambdaCallKnownSafe(code, mirbool, largs, capturedargs))
                        ])
                    ),
                    this.temitter.generateResultTypeConstructorSuccess(mirnat, new SMTCallSimple("bvadd", [new SMTVar("bidx"), this.temitter.generateResultGetSuccess(mirnat,new SMTVar("_@n"))])),
                    this.temitter.generateErrorResultAssert(mirnat)
                )
            )
        );

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "findIndexOfLast" + (isidx ? "_idx" : ""), code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}, { vname: "bidx", vtype: this.nattype}, ...capturedparams], undefined, 0, this.temitter.generateResultType(this.temitter.getMIRType("NSCore::Nat")), ffunc)],
            uf: [suf]
        };
    }

    ////////
    //Sum
    emitDestructorSum(ltype: SMTType, ctype: MIRType): SMTDestructorGenCode {
        const restype = this.temitter.generateResultType(ctype);

        const cdecl = this.temitter.assembly.entityDecls.get(ctype.typeID) as MIREntityTypeDecl;
        const primtype = cdecl instanceof MIRConstructableEntityTypeDecl ? this.temitter.getMIRType(cdecl.fromtype as MIRResolvedTypeKey) : ctype; 

        let ufconsname: string = "[UN_INITIALIZED]";
        let ovfname: string | undefined = undefined;
        if (primtype.typeID === "NSCore::Int") {
            ufconsname = "@UFSumConsInt";
            ovfname = "@UFSumConsIntOVF";
        }
        else if (primtype.typeID === "NSCore::Nat") {
            ufconsname = "@UFSumConsNat";
            ovfname = "@UFSumConsNatOVF";
        }
        else if (primtype.typeID === "NSCore::BigInt") {
            ufconsname = "@UFSumConsBigInt";
        }
        else if (primtype.typeID === "NSCore::BigNat") {
            ufconsname = "@UFSumConsBigNat";
        }
        else if (primtype.typeID === "NSCore::Rational") {
            ufconsname = "@UFSumConsRational";
        }
        else if (primtype.typeID === "NSCore::Float") {
            ufconsname = "@UFSumConsFloat";
        }
        else {
            ufconsname = "@UFSumConsDecimal";
        }

        //
        //TODO: what about typed numbers -- also min/max
        //
        assert(!(cdecl instanceof MIRConstructableEntityTypeDecl) || cdecl.usingcons === undefined, "Yikes this has invariants so we need to havoc");

        let ufops = [new SMTFunctionUninterpreted(this.generateDesCallName(ltype, ufconsname), [ltype], this.temitter.getSMTTypeFor(ctype))];
        if(ovfname !== undefined) {
            ufops.push(new SMTFunctionUninterpreted(this.generateDesCallName(ltype, ovfname), [ltype], this.booltype))
        }
        
        let ffunc: SMTExp = new SMTConst("[UNINIT]");
        if(cdecl instanceof MIRConstructableEntityTypeDecl) {
            if(primtype.typeID !== "NSCore::BigNat") {
                if(cdecl.usingcons === undefined) {
                    ffunc = this.temitter.generateResultTypeConstructorSuccess(ctype, new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]));
                }
                else {
                    ffunc = new SMTCallGeneral(cdecl.usingcons, [new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")])]);
                }
            }
            else {
                if(cdecl.usingcons === undefined) {
                    ffunc = new SMTLet("@vval", new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]),
                        new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst("0")]), this.temitter.generateErrorResultAssert(ctype), this.temitter.generateResultTypeConstructorSuccess(ctype, new SMTVar("@vval")))
                    );
                }
                else {
                    ffunc = new SMTLet("@vval", new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]),
                    new SMTIf(new SMTCallSimple("<=", [new SMTConst("0"), new SMTVar("@vval")]),
                            new SMTCallGeneral(cdecl.usingcons, [new SMTVar("@vval")]),
                            this.temitter.generateErrorResultAssert(ctype) 
                        )
                    );
                }
            }
        }
        else {
            if(primtype.typeID !== "NSCore::BigNat") {
                ffunc = this.temitter.generateResultTypeConstructorSuccess(ctype, new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]));
            }
            else {
                ffunc = new SMTLet("@vval", new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]),
                    new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst("0")]), this.temitter.generateErrorResultAssert(ctype), this.temitter.generateResultTypeConstructorSuccess(ctype, new SMTVar("@vval")))
                );
            }
        }

        if (ovfname !== undefined) {
            ffunc = new SMTIf(
                new SMTCallSimple(this.generateDesCallName(ltype, ovfname), [new SMTVar("l")]),
                ffunc,
                this.temitter.generateErrorResultAssert(ctype)
            );
        }

        return {
            if: [new SMTFunction(this.generateDesCallName(ltype, "sum"), [{ vname: "l", vtype: ltype }], undefined, 0, restype, ffunc)],
            uf: ufops
        };
    }


    ////////
    //StrConcat
    emitDestructorStrConcat(ltype: SMTType): SMTDestructorGenCode {
        const mirstrtype = this.temitter.getMIRType("NSCore::String");
        const restype = this.temitter.generateResultType(mirstrtype);
        
        const ufconsname = "@UFStrConcatCons";
        const ufops = [new SMTFunctionUninterpreted(this.generateDesCallName(ltype, ufconsname), [ltype], this.temitter.getSMTTypeFor(mirstrtype))];
        
        const ffunc = this.temitter.generateResultTypeConstructorSuccess(mirstrtype, new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l")]));

        return {
            if: [new SMTFunction(this.generateDesCallName(ltype, "strconcat"), [{ vname: "l", vtype: ltype }], undefined, 0, restype, ffunc)],
            uf: ufops
        };
    }

    ////////
    //StrJoin
    emitDestructorStrJoin(ltype: SMTType): SMTDestructorGenCode {
        const mirstrtype = this.temitter.getMIRType("NSCore::String");
        const restype = this.temitter.generateResultType(mirstrtype);
        
        const ufconsname = "@UFStrJoinCons";
        const ufops = [new SMTFunctionUninterpreted(this.generateDesCallName(ltype, ufconsname), [ltype, this.temitter.getSMTTypeFor(mirstrtype)], this.temitter.getSMTTypeFor(mirstrtype))];
        
        const ffunc = this.temitter.generateResultTypeConstructorSuccess(mirstrtype, new SMTCallSimple(this.generateDesCallName(ltype, ufconsname), [new SMTVar("l"), new SMTVar("sep")]));

        return {
            if: [new SMTFunction(this.generateDesCallName(ltype, "strjoin"), [{ vname: "l", vtype: ltype }, { vname: "sep", vtype: this.temitter.getSMTTypeFor(mirstrtype) }], undefined, 0, restype, ffunc)],
            uf: ufops
        };
    }

    private emitDestructorFindIndexOf_Shared(ltype: SMTType, isidx: boolean, code: string, pcode: MIRPCode, sl: SMTVar, osize: SMTVar, k: SMTExp): [SMTExp, SMTFunctionUninterpreted] {
        const [capturedargs, , ufpickargs] = this.generateCapturedInfoFor(pcode, isidx ? 2 : 1);

        const skloemcc = this.generateConsCallNameUsing(ltype, "skolem_list_index" + (isidx ? "_idx" : ""), code);

        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [sl, new SMTVar("_@nn")]);
        const largs = isidx ? [getcall, new SMTVar("_@nn")] : [getcall];

        const findidx =
            new SMTLet("_@nn", this.generateListIndexPickCall_Kth(skloemcc, sl, k, capturedargs),
                new SMTIf(new SMTCallSimple("bvult", [new SMTVar("_@nn"), osize]),
                    new SMTIf(this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), largs, capturedargs),
                        this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Nat"), new SMTVar("_@nn")),
                        this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
                    ),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
                )
            );

        return [
            findidx,
            new SMTFunctionUninterpreted(skloemcc, [ltype, this.nattype, ...ufpickargs], this.nattype)
        ];
    }

    private generateCapturedInfoFor(pcode: MIRPCode, k: number): [SMTVar[], {vname: string, vtype: SMTType}[], SMTType[]] {
        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        let capturedargs: SMTVar[] = [];
        let capturedparams: {vname: string, vtype: SMTType}[] = [];
        let ufpickargs: SMTType[] = [];

        lambdainfo.params.slice(k).forEach((p) => {
            capturedargs.push(new SMTVar(p.name));
            capturedparams.push({vname: p.name, vtype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type))});
            ufpickargs.push(this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)));
        });

        return [capturedargs, capturedparams, ufpickargs];
    }

    private generateCapturedFieldInfoFor(ltype: SMTType, op: string, k: number, code: string, pcode: MIRPCode): { fname: string, ftype: SMTType }[] {
        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedfields = lambdainfo.params.slice(k).map((p) => {
            return { fname: this.generateULIFieldUsingFor(ltype, op, code, p.name), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)) }
        });

        return capturedfields;
    }

    private generateCapturedFieldLetsInfoFor(ltype: SMTType, op: string, k: number, code: string, pcode: MIRPCode, ll: SMTVar): { vname: string, value: SMTExp }[] {
        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedfieldlets = lambdainfo.params.slice(k).map((p) => {
            return { vname: "c@" + p.name, value: this.generateGetULIFieldUsingFor(ltype, op, code, p.name, ll) };
        });

        return capturedfieldlets;
    }

    private processCapturedFieldLets(clets: { vname: string, value: SMTExp }[], continuation: SMTExp): SMTExp {
        if(clets.length === 0) {
            return continuation;
        }
        else {
            return new SMTLetMulti(clets, continuation);
        }
    }

    private generateListIndexPickCall_Kth(ctxname: string, sl: SMTVar, k: SMTExp, capturedargs: SMTVar[]): SMTExp {
        return new SMTCallSimple(ctxname, [sl, k, ...capturedargs]);
    }

    private generateLambdaCallKnownSafe(code: string, restype: MIRType, args: SMTExp[], cargs: SMTExp[]): SMTExp {
        if(this.safecalls.has(code)) {
            return new SMTCallSimple(this.temitter.lookupFunctionName(code), [...args, ...cargs]);
        }
        else {
            return this.temitter.generateResultGetSuccess(restype, new SMTCallGeneral(this.temitter.lookupFunctionName(code), [...args, ...cargs]));
        }
    }

    private generateLambdaCallGeneral(code: string, restype: MIRType, args: SMTExp[], cargs: SMTExp[]): SMTExp {
        return new SMTCallGeneral(this.temitter.lookupFunctionName(code), [...args, ...cargs]);
    }
}

export {
    ListOpsManager, ListOpsInfo,
    SMTConstructorGenCode, SMTDestructorGenCode
};

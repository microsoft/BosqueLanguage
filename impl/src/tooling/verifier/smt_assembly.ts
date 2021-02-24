//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { BSQRegex } from "../../ast/bsqregex";
import { SMTConst, SMTExp, SMTType, VerifierOptions } from "./smt_exp";

type SMT2FileInfo = {
    TYPE_TAG_DECLS: string[],
    ABSTRACT_TYPE_TAG_DECLS: string[],
    INDEX_TAG_DECLS: string[],
    PROPERTY_TAG_DECLS: string[],
    SUBTYPE_DECLS: string[],
    TUPLE_HAS_INDEX_DECLS: string[],
    RECORD_HAS_PROPERTY_DECLS: string[],
    KEY_TYPE_TAG_RANK: string[],
    BINTEGRAL_TYPE_ALIAS: string[],
    BINTEGRAL_CONSTANTS: string[],
    BFLOATPOINT_TYPE_ALIAS: string[],
    BFLOATPOINT_CONSTANTS: string[],
    STRING_TYPE_ALIAS: string,
    KEY_TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TYPE_COLLECTION_INTERNAL_INFO: { decls: string[], constructors: string[] },
    TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] }
    EPHEMERAL_DECLS: { decls: string[], constructors: string[] },
    RESULT_INFO: { decls: string[], constructors: string[] },
    MASK_INFO: { decls: string[], constructors: string[] },
    GLOBAL_DECLS: string[],
    UF_DECLS: string[],
    FUNCTION_DECLS: string[],
    GLOBAL_DEFINITIONS: string[],
    ACTION: string[]
};

class SMTFunction {
    readonly fname: string;
    readonly args: { vname: string, vtype: SMTType }[];
    readonly maskname: string | undefined;
    readonly masksize: number;
    readonly result: SMTType;

    readonly body: SMTExp;

    constructor(fname: string, args: { vname: string, vtype: SMTType }[], maskname: string | undefined, masksize: number, result: SMTType, body: SMTExp) {
        this.fname = fname;
        this.args = args;
        this.maskname = maskname;
        this.masksize = masksize;
        this.result = result;

        this.body = body;
    }

    static create(fname: string, args: { vname: string, vtype: SMTType }[], result: SMTType, body: SMTExp): SMTFunction {
        return new SMTFunction(fname, args, undefined, 0, result, body);
    }

    static createWithMask(fname: string, args: { vname: string, vtype: SMTType }[], maskname: string, masksize: number, result: SMTType, body: SMTExp): SMTFunction {
        return new SMTFunction(fname, args, maskname, masksize, result, body);
    }

    emitSMT2(): string {
        const args = this.args.map((arg) => `(${arg.vname} ${arg.vtype.name})`);
        const body = this.body.emitSMT2("  ");

        if(this.maskname === undefined) {
            return `(define-fun ${this.fname} (${args.join(" ")}) ${this.result.name}\n${body}\n)`;
        }
        else {
            return `(define-fun ${this.fname} (${args.join(" ")} (${this.maskname} $Mask_${this.masksize})) ${this.result.name}\n${body}\n)`;
        }
    }

    emitSMT2_DeclOnly(): string {
        const args = this.args.map((arg) => `(${arg.vname} ${arg.vtype.name})`);

        if(this.maskname === undefined) {
            return `(${this.fname} (${args.join(" ")}) ${this.result.name})`;
        }
        else {
            return `(${this.fname} (${args.join(" ")} (${this.maskname} $Mask_${this.masksize})) ${this.result.name})`;
        }
    }
}

class SMTFunctionUninterpreted {
    readonly fname: string;
    readonly args: SMTType[];
    readonly result: SMTType;

    constructor(fname: string, args: SMTType[], result: SMTType) {
        this.fname = fname;
        this.args = args;
        this.result = result;
    }

    emitSMT2(): string {
        return `(declare-fun ${this.fname} (${this.args.map((arg) => arg.name).join(" ")}) ${this.result.name})`;
    }

    static areDuplicates(f1: SMTFunctionUninterpreted, f2: SMTFunctionUninterpreted): boolean {
        if (f1.fname !== f2.fname || f1.args.length !== f2.args.length) {
            return false;
        }

        if (f1.result.name !== f2.result.name) {
            return false;
        }

        for (let i = 0; i < f1.args.length; ++i) {
            if (f1.args[i].name !== f2.args[i].name) {
                return false;
            }
        }

        return true;
    }
}

class SMTEntityDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;

    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTListDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;

    readonly smtllisttype: string; //the uninterpreted list contents kind with multiple constructors 
    readonly listtypeconsf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[]; //the constructors for each list

    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtllisttype: string, listtypeconsf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[], smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtllisttype = smtllisttype;
        this.listtypeconsf = listtypeconsf;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTTupleDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTRecordDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTEphemeralListDecl {
    readonly smtname: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };

    constructor(smtname: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }) {
        this.smtname = smtname;
        this.consf = consf;
    }
}

class SMTConstantDecl {
    readonly gkey: string;
    readonly ctype: SMTType;

    readonly consf: string;

    constructor(gkey: string, ctype: SMTType, consf: string) {
        this.gkey = gkey;
        this.ctype = ctype;

        this.consf = consf;
    }
}

class SMTModelState {
    readonly arginits: { vname: string, vtype: SMTType, vchk: SMTExp | undefined, vinit: SMTExp, callexp: SMTExp }[];
    readonly argchk: SMTExp[] | undefined;
    readonly checktype: SMTType;
    readonly fcheck: SMTExp;

    constructor(arginits: { vname: string, vtype: SMTType, vchk: SMTExp | undefined, vinit: SMTExp, callexp: SMTExp }[], argchk: SMTExp[] | undefined, checktype: SMTType, echeck: SMTExp) {
        this.arginits = arginits;
        this.argchk = argchk;
        this.checktype = checktype;
        this.fcheck = echeck;
    }
}


type SMTCallGNode = {
    invoke: string,
    callees: Set<string>,
    callers: Set<string>
};

type SMTCallGInfo = {
    invokes: Map<string, SMTCallGNode>,
    topologicalOrder: SMTCallGNode[],
    roots: SMTCallGNode[],
    recursive: (Set<string>)[]
};

class SMTAssembly {
    readonly vopts: VerifierOptions;
    
    allErrors: { file: string, line: number, pos: number, msg: string }[] = [];

    entityDecls: SMTEntityDecl[] = [];
    listDecls: SMTListDecl[] = [];
    tupleDecls: SMTTupleDecl[] = [];
    recordDecls: SMTRecordDecl[] = [];
    ephemeralDecls: SMTEphemeralListDecl[] = [];

    typeTags: string[] = [
        "TypeTag_None",
        "TypeTag_Bool",
        "TypeTag_Int",
        "TypeTag_Nat",
        "TypeTag_BigInt",
        "TypeTag_BigNat",
        "TypeTag_Float",
        "TypeTag_Decimal",
        "TypeTag_Rational",
        "TypeTag_String",
        "TypeTag_Regex"
    ];
    keytypeTags: string[] = [
        "TypeTag_None",
        "TypeTag_Bool",
        "TypeTag_Int",
        "TypeTag_Nat",
        "TypeTag_BigInt",
        "TypeTag_BigNat",
        "TypeTag_String"
    ];

    abstractTypes: string[] = [];
    indexTags: string[] = [];
    propertyTags: string[] = [];

    subtypeRelation: { ttype: string, atype: string, value: boolean }[] = [];
    hasIndexRelation: { idxtag: string, atype: string, value: boolean }[] = [];
    hasPropertyRelation: { pnametag: string, atype: string, value: boolean }[] = [];

    literalRegexs: BSQRegex[] = [];
    validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    constantDecls: SMTConstantDecl[] = [];
    
    uninterpfunctions: SMTFunctionUninterpreted[] = [];

    maskSizes: Set<number> = new Set<number>();
    resultTypes: { hasFlag: boolean, rtname: string, ctype: SMTType }[] = [];
    functions: SMTFunction[] = [];

    entrypoint: string;
    havocfuncs: Set<string> = new Set<string>();
    model: SMTModelState = new SMTModelState([], undefined, new SMTType("[UNINIT]"), new SMTConst("bsq_none@literal"));

    modes: { refute: SMTExp, generate: SMTExp } = { 
        refute: new SMTConst("bsq_none@literal"), 
        generate: new SMTConst("bsq_none@literal")
    };

    constructor(vopts: VerifierOptions, entrypoint: string) {
        this.vopts = vopts;
        this.entrypoint = entrypoint;
    }

    private static sccVisit(cn: SMTCallGNode, scc: Set<string>, marked: Set<string>, invokes: Map<string, SMTCallGNode>) {
        if (marked.has(cn.invoke)) {
            return;
        }

        scc.add(cn.invoke);
        marked.add(cn.invoke);
        cn.callers.forEach((pred) => SMTAssembly.sccVisit(invokes.get(pred) as SMTCallGNode, scc, marked, invokes));
    }

    private static topoVisit(cn: SMTCallGNode, pending: SMTCallGNode[], tordered: SMTCallGNode[], invokes: Map<string, SMTCallGNode>) {
        if (pending.findIndex((vn) => vn.invoke === cn.invoke) !== -1 || tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
            return;
        }

        pending.push(cn);

        cn.callees.forEach((succ) => (invokes.get(succ) as SMTCallGNode).callers.add(cn.invoke));
        cn.callees.forEach((succ) => SMTAssembly.topoVisit(invokes.get(succ) as SMTCallGNode, pending, tordered, invokes));

        tordered.push(cn);
    }

    private static processBodyInfo(bkey: string, binfo: SMTExp, invokes: Set<string>): SMTCallGNode {
        let cn = { invoke: bkey, callees: new Set<string>(), callers: new Set<string>() };

        let ac = new Set<string>();
        binfo.computeCallees(ac);

        ac.forEach((cc) => {
            if(invokes.has(cc)) {
                cn.callees.add(cc);
            }
        });
        return cn;
    }

    private static constructCallGraphInfo(entryPoints: string[], assembly: SMTAssembly): SMTCallGInfo {
        let invokes = new Map<string, SMTCallGNode>();

        const okinv = new Set<string>(assembly.functions.map((f) => f.fname));
        assembly.functions.forEach((smtfun) => {
            invokes.set(smtfun.fname, SMTAssembly.processBodyInfo(smtfun.fname, smtfun.body, okinv));
        });

        let roots: SMTCallGNode[] = [];
        let tordered: SMTCallGNode[] = [];
        entryPoints.forEach((ivk) => {
            roots.push(invokes.get(ivk) as SMTCallGNode);
            SMTAssembly.topoVisit(invokes.get(ivk) as SMTCallGNode, [], tordered, invokes);
        });

        assembly.constantDecls.forEach((cdecl) => {
            roots.push(invokes.get(cdecl.consf) as SMTCallGNode);
            SMTAssembly.topoVisit(invokes.get(cdecl.consf) as SMTCallGNode, [], tordered, invokes);
        });

        tordered = tordered.reverse();

        let marked = new Set<string>();
        let recursive: (Set<string>)[] = [];
        for (let i = 0; i < tordered.length; ++i) {
            let scc = new Set<string>();
            SMTAssembly.sccVisit(tordered[i], scc, marked, invokes);

            if (scc.size > 1 || tordered[i].callees.has(tordered[i].invoke)) {
                recursive.push(scc);
            }
        }

        return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
    }

    computeBVMinSigned(bits: bigint): string {
        const bbn = ((2n ** bits) / 2n);
        return bbn.toString();
    }

    computeBVMaxSigned(bits: bigint): string {
        const bbn = ((2n ** bits) / 2n) - 1n;
        return bbn.toString();
    }

    computeBVMaxUnSigned(bits: bigint): string {
        const bbn = (2n ** bits) - 1n;
        return bbn.toString();
    }

    generateSMT2AssemblyInfo(mode: "Refute" | "Reach" | "Generate"): SMT2FileInfo {
        const subtypeasserts = this.subtypeRelation.map((tc) => tc.value ? `(assert (SubtypeOf@ ${tc.ttype} ${tc.atype}))` : `(assert (not (SubtypeOf@ ${tc.ttype} ${tc.atype})))`).sort();
        const indexasserts = this.hasIndexRelation.map((hi) => hi.value ? `(assert (HasIndex@ ${hi.idxtag} ${hi.atype}))` : `(assert (not (HasIndex@ ${hi.idxtag} ${hi.atype})))`).sort();
        const propertyasserts = this.hasPropertyRelation.map((hp) => hp.value ? `(assert (HasProperty@ ${hp.pnametag} ${hp.atype}))` : `(assert (not (HasProperty@ ${hp.pnametag} ${hp.atype})))`).sort();

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `(assert (= (TypeTagRank@ ${ktt}) ${i}))`);

        let integral_type_alias: string[] = [
            `(define-sort BInt () (_ BitVec ${this.vopts.ISize}))`,
            `(define-sort BNat () (_ BitVec ${this.vopts.ISize}))`,
            (this.vopts.BigXMode === "Int" ? "(define-sort BBigInt () Int)" : `(define-sort BBigInt () (_ BitVec ${2 * this.vopts.ISize}))`),
            (this.vopts.BigXMode === "Int" ? "(define-sort BBigNat () Int)" : `(define-sort BBigNat () (_ BitVec ${2 * this.vopts.ISize}))`)
        ];
        let integral_constants: string[] = [
            `(declare-const BInt@zero BInt) (assert (= BInt@zero (_ bv0 ${this.vopts.ISize})))`,
            `(declare-const BInt@one BInt) (assert (= BInt@one (_ bv1 ${this.vopts.ISize})))`,
            `(declare-const BInt@min BInt) (assert (= BInt@min (_ bv${this.computeBVMinSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`,
            `(declare-const BInt@max BInt) (assert (= BInt@max (_ bv${this.computeBVMaxSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`,

            `(declare-const BNat@zero BNat) (assert (= BNat@zero (_ bv0 ${this.vopts.ISize})))`,
            `(declare-const BNat@one BNat) (assert (= BNat@one (_ bv1 ${this.vopts.ISize})))`,
            `(declare-const BNat@min BNat) (assert (= BNat@min BNat@zero))`,
            `(declare-const BNat@max BNat) (assert (= BNat@max (_ bv${this.computeBVMaxUnSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`
        ];
        if(this.vopts.BigXMode === "Int") {
            integral_constants.push(`(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))`);
            integral_constants.push(`(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))`);

            integral_constants.push(`(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))`);
            integral_constants.push(`(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))`);
        }
        else {
            integral_constants.push(`(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero (_ bv0 ${2 * this.vopts.ISize})))`);
            integral_constants.push(`(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one (_ bv1 ${2 * this.vopts.ISize})))`);

            integral_constants.push(`(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero (_ bv0 ${2 * this.vopts.ISize})))`);
            integral_constants.push(`(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one (_ bv1 ${2 * this.vopts.ISize})))`);
        }

        let float_type_alias: string[] = [];
        let float_constants: string[] = [];
        if(this.vopts.FPOpt === "Real") {
            float_type_alias.push("(define-sort BFloat () Real)", "(define-sort BDecimal () Real)", "(define-sort BRational () Real)");

            float_constants.push(`(declare-const BFloat@zero BFloat) (assert (= BFloat@zero 0.0))`);
            float_constants.push(`(declare-const BFloat@one BFloat) (assert (= BFloat@one 1.0))`);
            float_constants.push(`(declare-const BFloat@pi BFloat) (assert (= BFloat@pi 3.141592653589793))`);
            float_constants.push(`(declare-const BFloat@e BFloat) (assert (= BFloat@e 2.718281828459045))`);

            float_constants.push(`(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero 0.0))`);
            float_constants.push(`(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one 1.0))`);
            float_constants.push(`(declare-const BDecimal@pi BDecimal) (assert (= BDecimal@pi 3.141592653589793))`);
            float_constants.push(`(declare-const BDecimal@e BDecimal) (assert (= BDecimal@e 2.718281828459045))`);

            float_constants.push(`(declare-const BRational@zero BRational) (assert (= BRational@zero 0.0))`);
            float_constants.push(`(declare-const BRational@one BRational) (assert (= BRational@one 1.0))`);
        }
        else {
            float_type_alias.push("(define-sort BFloat () UFloat)", "(define-sort BDecimal () UFloat)", "(define-sort BRational () UFloat)");

            float_constants.push(`(declare-const BFloat@zero BFloat) (assert (= BFloat@zero (BFloatCons_UF "0.0")))`);
            float_constants.push(`(declare-const BFloat@one BFloat) (assert (= BFloat@one (BFloatCons_UF "1.0")))`);
            float_constants.push(`(declare-const BFloat@pi BFloat) (assert (= BFloat@pi (BFloatCons_UF "3.141592653589793")))`);
            float_constants.push(`(declare-const BFloat@e BFloat) (assert (= BFloat@e (BFloatCons_UF "2.718281828459045")))`);

            float_constants.push(`(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero (BDecimalCons_UF "0.0")))`);
            float_constants.push(`(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one (BDecimalCons_UF "1.0")))`);
            float_constants.push(`(declare-const BDecimal@pi BDecimal) (assert (= BDecimal@pi (BDecimalCons_UF "3.141592653589793")))`);
            float_constants.push(`(declare-const BDecimal@e BDecimal) (assert (= BDecimal@e (BDecimalCons_UF "2.718281828459045")))`);

            float_constants.push(`(declare-const BRational@zero BRational) (assert (= BRational@zero (BRationalCons_UF "0/1")))`);
            float_constants.push(`(declare-const BRational@one BRational) (assert (= BRational@one (BRationalCons_UF "1/1")))`);
        }
        
        const keytupleinfo = this.tupleDecls
            .filter((tt) => tt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const termtupleinfo = this.tupleDecls
            .filter((tt) => !tt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const keyrecordinfo = this.recordDecls
            .filter((rt) => rt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const termrecordinfo = this.recordDecls
            .filter((rt) => !rt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const keytypeinfo = this.entityDecls
            .filter((et) => et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const termtypeinfo = this.entityDecls
            .filter((et) => !et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        let generalcollectioninternaldecls: {decl: string, consf: string}[] = [];
        this.listDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .forEach((kt) => {
                const iconsopts = kt.listtypeconsf.map((cf) => `(${cf.cname} ${cf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")})`)
                generalcollectioninternaldecls.push({
                    decl: `(${kt.smtllisttype} 0)`,
                    consf: `( ${iconsopts.join(" ")} )`
                });

                termtypeinfo.push({
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                });
            });

        const etypeinfo = this.ephemeralDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((et) => {
                return {
                    decl: `(${et.smtname} 0)`,
                    consf: `( (${et.consf.cname} ${et.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`).join(" ")}) )`
                };
            });

        const rtypeinfo = this.resultTypes
            .sort((t1, t2) => (t1.hasFlag !== t2.hasFlag) ? (t1.hasFlag ? 1 : -1) : t1.rtname.localeCompare(t2.rtname))
            .map((rt) => {
                if (rt.hasFlag) {
                    return {
                        decl: `($GuardResult_${rt.ctype.name} 0)`,
                        consf: `( ($GuardResult_${rt.ctype.name}@cons ($GuardResult_${rt.ctype.name}@result ${rt.ctype.name}) ($GuardResult_${rt.ctype.name}@flag Bool)) )`
                    };
                }
                else {
                    return {
                        decl: `($Result_${rt.ctype.name} 0)`,
                        consf: `( ($Result_${rt.ctype.name}@success ($Result_${rt.ctype.name}@success_value ${rt.ctype.name})) ($Result_${rt.ctype.name}@error ($Result_${rt.ctype.name}@error_value ErrorID)) )`
                    };
                }
            });

        const maskinfo = [...this.maskSizes]
            .sort()
            .map((msize) => {
                let entries: string[] = [];
                for(let i = 0; i < msize; ++i) {
                    entries.push(`($Mask_${msize}@${i} Bool)`);
                }

                return {
                    decl: `($Mask_${msize} 0)`,
                    consf: `( ($Mask_${msize}@cons ${entries.join(" ")}) )`
                };
            });

        const gdecls = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => `(declare-const ${c.gkey} ${c.ctype.name})`);

        const ufdecls = this.uninterpfunctions
            .sort((uf1, uf2) => uf1.fname.localeCompare(uf2.fname))
            .map((uf) => uf.emitSMT2());

        const gdefs = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => `(assert (= ${c.gkey} ${c.consf}))`);

        let action: string[] = [];
        this.model.arginits.map((iarg) => {
            action.push(`(declare-const ${iarg.vname} ${iarg.vtype.name})`);
            action.push(`(assert (= ${iarg.vname} ${iarg.vinit.emitSMT2(undefined)}))`);

            if(iarg.vchk !== undefined) {
                action.push(`(assert ${iarg.vchk.emitSMT2(undefined)})`);
            }
        });

        if(this.model.argchk !== undefined) {
            action.push(...this.model.argchk.map((chk) => `(assert ${chk.emitSMT2(undefined)})`));
        }

        if (mode === "Refute") {
            action.push(`(declare-const @smtres@ ${this.model.checktype.name})`);
            action.push(`(assert (= @smtres@ ${this.model.fcheck.emitSMT2(undefined)}))`);

            action.push(`(assert ${this.modes.refute.emitSMT2(undefined)})`);
            action.push("(check-sat)");
        }
        else if (mode === "Reach") {
            action.push(`(declare-const @smtres@ ${this.model.checktype.name})`);
            action.push(`(assert (= @smtres@ ${this.model.fcheck.emitSMT2(undefined)}))`);

            action.push(`(assert ${this.modes.generate.emitSMT2(undefined)})`);
            action.push("(check-sat)");
        }
        else {
            action.push(`(declare-const @smtres@ ${this.model.checktype.name})`);
            action.push(`(assert (= @smtres@ ${this.model.fcheck.emitSMT2(undefined)}))`);

            action.push(`(assert ${this.modes.generate.emitSMT2(undefined)})`);
            action.push("(check-sat)");
            //action.push("(get-model)");
        }

        let foutput: string[] = [];
        let doneset: Set<string> = new Set<string>();
        const cginfo = SMTAssembly.constructCallGraphInfo([this.entrypoint, ...this.havocfuncs], this);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const rf = this.functions.find((f) => f.fname === cn.invoke) as SMTFunction;
            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            if(cscc === undefined) {
                doneset.add(cn.invoke);
                foutput.push(rf.emitSMT2());
            }
            else {
                let worklist = [...cscc].sort();

                let decls: string[] = [];
                let impls: string[] = [];
                while(worklist.length !== 0) {
                    const cf = worklist.pop() as string;
                    const crf = this.functions.find((f) => f.fname === cf) as SMTFunction;

                    decls.push(crf.emitSMT2_DeclOnly());
                    impls.push(crf.body.emitSMT2("  "));
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }

                foutput.push(`(define-funs-rec (\n  ${decls.join("\n  ")}\n) (\n${impls.join("\n")}))`)
            }
        }   

        return {
            TYPE_TAG_DECLS: this.typeTags.sort().map((tt) => `(${tt})`),
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes.sort().map((tt) => `(${tt})`),
            INDEX_TAG_DECLS: this.indexTags.sort().map((tt) => `(${tt})`),
            PROPERTY_TAG_DECLS: this.propertyTags.sort().map((tt) => `(${tt})`),
            SUBTYPE_DECLS: subtypeasserts,
            TUPLE_HAS_INDEX_DECLS: indexasserts,
            RECORD_HAS_PROPERTY_DECLS: propertyasserts,
            KEY_TYPE_TAG_RANK: keytypeorder,
            BINTEGRAL_TYPE_ALIAS: integral_type_alias,
            BINTEGRAL_CONSTANTS: integral_constants,
            BFLOATPOINT_TYPE_ALIAS: float_type_alias,
            BFLOATPOINT_CONSTANTS: float_constants,
            STRING_TYPE_ALIAS: (this.vopts.StringOpt === "UNICODE" ? "(define-sort BString () (Seq (_ BitVec 16)))" : "(define-sort BString () String)"),
            KEY_TUPLE_INFO: { decls: keytupleinfo.map((kti) => kti.decl), constructors: keytupleinfo.map((kti) => kti.consf), boxing: keytupleinfo.map((kti) => kti.boxf) },
            KEY_RECORD_INFO: { decls: keyrecordinfo.map((kti) => kti.decl), constructors: keyrecordinfo.map((kti) => kti.consf), boxing: keyrecordinfo.map((kti) => kti.boxf) },
            KEY_TYPE_INFO: { decls: keytypeinfo.map((kti) => kti.decl), constructors: keytypeinfo.map((kti) => kti.consf), boxing: keytypeinfo.map((kti) => kti.boxf) },
            TUPLE_INFO: { decls: termtupleinfo.map((kti) => kti.decl), constructors: termtupleinfo.map((kti) => kti.consf), boxing: termtupleinfo.map((kti) => kti.boxf) },
            RECORD_INFO: { decls: termrecordinfo.map((kti) => kti.decl), constructors: termrecordinfo.map((kti) => kti.consf), boxing: termrecordinfo.map((kti) => kti.boxf) },
            TYPE_COLLECTION_INTERNAL_INFO: { decls: generalcollectioninternaldecls.map((kti) => kti.decl), constructors: generalcollectioninternaldecls.map((kti) => kti.consf) },
            TYPE_INFO: { decls: termtypeinfo.map((kti) => kti.decl), constructors: termtypeinfo.map((kti) => kti.consf), boxing: termtypeinfo.map((kti) => kti.boxf) },
            EPHEMERAL_DECLS: { decls: etypeinfo.map((kti) => kti.decl), constructors: etypeinfo.map((kti) => kti.consf) },
            RESULT_INFO: { decls: rtypeinfo.map((kti) => kti.decl), constructors: rtypeinfo.map((kti) => kti.consf) },
            MASK_INFO: { decls: maskinfo.map((mi) => mi.decl), constructors: maskinfo.map((mi) => mi.consf) },
            GLOBAL_DECLS: gdecls,
            UF_DECLS: ufdecls,
            FUNCTION_DECLS: foutput,
            GLOBAL_DEFINITIONS: gdefs,
            ACTION: action
        };
    }
}

export {
    SMTEntityDecl, SMTListDecl, SMTTupleDecl, SMTRecordDecl, SMTEphemeralListDecl,
    SMTConstantDecl,
    SMTFunction, SMTFunctionUninterpreted,
    SMTAssembly, SMTModelState,
    SMT2FileInfo
};

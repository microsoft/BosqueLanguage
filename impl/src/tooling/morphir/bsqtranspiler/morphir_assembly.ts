//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { BSQRegex } from "../../../ast/bsqregex";
import { MIRResolvedTypeKey } from "../../../compiler/mir_ops";
import { MorphirExp, MorphirTypeInfo } from "./morphir_exp";

type Morphir2FileInfo = {
    TYPE_TAG_DECLS: string[],
    ORDINAL_TYPE_TAG_DECLS: string[],
    ABSTRACT_TYPE_TAG_DECLS: string[],
    SUBTYPE_DECLS: string[],
    OF_TYPE_DECLS: string[],
    KEY_BOX_OPS: string[],
    TUPLE_INFO: { decls: string[], boxing: string[], unboxing: string[] },
    RECORD_INFO: { decls: string[], boxing: string[], unboxing: string[] },
    TYPE_INFO: { decls: string[], constructors: string[], boxing: string[], unboxing: string[] }
    EPHEMERAL_DECLS: { decls: string[] },
    MASK_INFO: { decls: string[], constructors: string[] },
    GLOBAL_DECLS: string[],
    UF_DECLS: string[],
    FUNCTION_DECLS: string[],
    GLOBAL_DEFINITIONS: string[],
    ACTION: string[]
};

class MorphirFunction {
    readonly fname: string;
    readonly args: { vname: string, vtype: MorphirTypeInfo }[];
    readonly maskname: string | undefined;
    readonly masksize: number;
    readonly result: MorphirTypeInfo;

    readonly body: MorphirExp;
    readonly implicitlambdas: string[] | undefined;

    constructor(fname: string, args: { vname: string, vtype: MorphirTypeInfo }[], maskname: string | undefined, masksize: number, result: MorphirTypeInfo, body: MorphirExp, implicitlambdas: string[] | undefined) {
        this.fname = fname;
        this.args = args;
        this.maskname = maskname;
        this.masksize = masksize;
        this.result = result;

        this.body = body;
        this.implicitlambdas = implicitlambdas;
    }

    static create(fname: string, args: { vname: string, vtype: MorphirTypeInfo }[], result: MorphirTypeInfo, body: MorphirExp): MorphirFunction {
        return new MorphirFunction(fname, args, undefined, 0, result, body, undefined);
    }

    static createWithImplicitLambdas(fname: string, args: { vname: string, vtype: MorphirTypeInfo }[], result: MorphirTypeInfo, body: MorphirExp, implicitlambdas: string[]): MorphirFunction {
        return new MorphirFunction(fname, args, undefined, 0, result, body, implicitlambdas);
    }

    static createWithMask(fname: string, args: { vname: string, vtype: MorphirTypeInfo }[], maskname: string, masksize: number, result: MorphirTypeInfo, body: MorphirExp): MorphirFunction {
        return new MorphirFunction(fname, args, maskname, masksize, result, body, undefined);
    }

    emitMorphir(): string {
        const declargs = this.args.map((arg) => `${arg.vtype.morphirtypename}`).join(" -> ");
        const implargs = this.args.map((arg) => `${arg.vname} `).join(" ");
        const body = this.body.emitMorphir("  ");

        if(this.maskname === undefined) {
            const decl = `${this.fname} ${declargs} -> ${this.result.morphirtypename}\n`;
            const impl = `${this.fname} ${implargs} = \n${body}\n`;
            return decl + impl;
        }
        else {
            const decl = `${this.fname} ${declargs} -> mask_${this.masksize} -> ${this.result.morphirtypename}\n`;
            const impl = `${this.fname} ${implargs} ${this.maskname} = \n${body}\n`;
            return decl + impl;
        }
    }
}

class MorphirEntityDecl {
    readonly iskeytype: boolean;
    readonly morphirname: string;
    readonly typetag: string;

    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, morphirname: string, typetag: string, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.morphirname = morphirname;
        this.typetag = typetag;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class MorphirEntityOfTypeDecl extends MorphirEntityDecl {
    readonly ofsmttype: string;

    constructor(iskeytype: boolean, morphirname: string, typetag: string, boxf: string, ubf: string, ofsmttype: string) {
        super(iskeytype, morphirname, typetag, boxf, ubf);
        this.ofsmttype = ofsmttype;
    }
}

class MorphirEntityInternalOfTypeDecl extends MorphirEntityDecl {
    readonly ofsmttype: string;

    constructor(morphirname: string, typetag: string, boxf: string, ubf: string, ofsmttype: string) {
        super(false, morphirname, typetag, boxf, ubf);
        this.ofsmttype = ofsmttype;
    }
}

class MorphirEntityCollectionEntryTypeDecl extends MorphirEntityDecl {
    readonly consf: { cname: string, cargs: { fname: string, ftype: string }[] };

    constructor(morphirname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: string }[] }) {
        super(false, morphirname, typetag, "INVALID_SPECIAL", "INVALID_SPECIAL");

        this.consf = consf;
    }
}

class MorphirEntityCollectionTypeDecl extends MorphirEntityDecl {
    readonly consf: { cname: string, cargs: { fname: string, ftype: string }[] };
    readonly emptyconst: {fkind: string, fname: string, fexp: string};
    readonly entrydecl: MorphirEntityCollectionEntryTypeDecl | undefined;

    constructor(morphirname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: string }[] }, boxf: string, ubf: string, emptyconst: {fkind: string, fname: string, fexp: string}, entrydecl: MorphirEntityCollectionEntryTypeDecl | undefined) {
        super(false, morphirname, typetag, boxf, ubf);

        this.consf = consf;
        this.emptyconst = emptyconst;
        this.entrydecl = entrydecl;
    }
}

class MorphirEntityStdDecl extends MorphirEntityDecl {
    readonly consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] };
    
    constructor(morphirname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] }, boxf: string, ubf: string) {
        super(false, morphirname, typetag, boxf, ubf);
        this.consf = consf;
    }
}

class MorphirTupleDecl {
    readonly morphirname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(morphirname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] }, boxf: string, ubf: string) {
        this.morphirname = morphirname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class MorphirRecordDecl {
    readonly morphirname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(morphirname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] }, boxf: string, ubf: string) {
        this.morphirname = morphirname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class MorphirEphemeralListDecl {
    readonly morphirname: string;
    readonly consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] };

    constructor(morphirname: string, consf: { cname: string, cargs: { fname: string, ftype: MorphirTypeInfo }[] }) {
        this.morphirname = morphirname;
        this.consf = consf;
    }
}

class MorphirConstantDecl {
    readonly gkey: string;
    readonly optenumname: [MIRResolvedTypeKey, string] | undefined;
    readonly ctype: MorphirTypeInfo;

    readonly consfinv: string;

    readonly consfexp: MorphirExp;
    readonly checkf: MorphirExp | undefined;

    constructor(gkey: string, optenumname: [MIRResolvedTypeKey, string] | undefined, ctype: MorphirTypeInfo, consfinv: string, consfexp: MorphirExp, checkf: MorphirExp | undefined) {
        this.gkey = gkey;
        this.optenumname = optenumname;
        this.ctype = ctype;

        this.consfinv = consfinv;

        this.consfexp = consfexp;
        this.checkf = checkf;
    }
}

type MorphirCallGNode = {
    invoke: string,
    callees: Set<string>,
    callers: Set<string>
};

type MorphirCallGInfo = {
    invokes: Map<string, MorphirCallGNode>,
    topologicalOrder: MorphirCallGNode[],
    roots: MorphirCallGNode[],
    recursive: (Set<string>)[]
};

class MorphirAssembly {
    entityDecls: MorphirEntityDecl[] = [];
    tupleDecls: MorphirTupleDecl[] = [];
    recordDecls: MorphirRecordDecl[] = [];
    ephemeralDecls: MorphirEphemeralListDecl[] = [];

    typeTags: string[] = [
        "TypeTag_None",
        "TypeTag_Nothing",
        "TypeTag_Bool",
        "TypeTag_Int",
        "TypeTag_Nat",
        "TypeTag_BigInt",
        "TypeTag_BigNat",
        "TypeTag_Float",
        "TypeTag_Decimal",
        "TypeTag_Rational",
        "TypeTag_String",
        "TypeTag_ByteBuffer",
        "TypeTag_DateTime",
        "TypeTag_UTCDateTime",
        "TypeTag_CalendarDate",
        "TypeTag_RelativeTime",
        "TypeTag_TickTime",
        "TypeTag_LogicalTime",
        "TypeTag_ISOTimeStamp",
        "TypeTag_UUID4",
        "TypeTag_UUID7",
        "TypeTag_ShaContentHash",
        "TypeTag_LatLongCoordinate",
        "TypeTag_Regex"
    ];
    keytypeTags: string[] = [
        "TypeTag_None",
        "TypeTag_Bool",
        "TypeTag_Int",
        "TypeTag_Nat",
        "TypeTag_BigInt",
        "TypeTag_BigNat",
        "TypeTag_String",
        "TypeTag_UTCDateTime",
        "TypeTag_CalendarDate",
        "TypeTag_RelativeTime",
        "TypeTag_TickTime",
        "TypeTag_LogicalTime",
        "TypeTag_ISOTimeStamp",
        "TypeTag_UUID4",
        "TypeTag_UUID7",
        "TypeTag_ShaContentHash",
    ];

    abstractTypes: string[] = [];

    subtypeRelation: { ttype: string, atype: string, value: boolean }[] = [];
    hasIndexRelation: { idxtag: string, atype: string, value: boolean }[] = [];
    hasPropertyRelation: { pnametag: string, atype: string, value: boolean }[] = [];

    literalRegexs: BSQRegex[] = [];
    validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    constantDecls: MorphirConstantDecl[] = [];

    maskSizes: Set<number> = new Set<number>();
    resultTypes: { hasFlag: boolean, rtname: string, ctype: SMTTypeInfo }[] = [];
    functions: MorphirFunction[] = [];

    entrypoint: string;

    constructor(entrypoint: string) {
        this.entrypoint = entrypoint;
    }

    private static sccVisit(cn: MorphirCallGNode, scc: Set<string>, marked: Set<string>, invokes: Map<string, MorphirCallGNode>) {
        if (marked.has(cn.invoke)) {
            return;
        }

        scc.add(cn.invoke);
        marked.add(cn.invoke);
        cn.callers.forEach((pred) => MorphirAssembly.sccVisit(invokes.get(pred) as MorphirCallGNode, scc, marked, invokes));
    }

    private static topoVisit(cn: MorphirCallGNode, pending: MorphirCallGNode[], tordered: MorphirCallGNode[], invokes: Map<string, MorphirCallGNode>) {
        if (pending.findIndex((vn) => vn.invoke === cn.invoke) !== -1 || tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
            return;
        }

        pending.push(cn);

        cn.callees.forEach((succ) => (invokes.get(succ) as MorphirCallGNode).callers.add(cn.invoke));
        cn.callees.forEach((succ) => MorphirAssembly.topoVisit(invokes.get(succ) as MorphirCallGNode, pending, tordered, invokes));

        tordered.push(cn);
    }

    private static processBodyInfo(bkey: string, binfo: MorphirExp, invokes: Set<string>): MorphirCallGNode {
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

    private static constructCallGraphInfo(entryPoints: string[], assembly: MorphirAssembly): MorphirCallGInfo {
        let invokes = new Map<string, MorphirCallGNode>();

        const okinv = new Set<string>(assembly.functions.map((f) => f.fname));
        assembly.functions.forEach((smtfun) => {
            const cn = MorphirAssembly.processBodyInfo(smtfun.fname, smtfun.body, okinv);
            if(smtfun.implicitlambdas !== undefined) {
                smtfun.implicitlambdas.forEach((cc) => {
                    if(okinv.has(cc)) {
                        cn.callees.add(cc);
                    }
                });
            }
            invokes.set(smtfun.fname, cn);
        });

        let roots: MorphirCallGNode[] = [];
        let tordered: MorphirCallGNode[] = [];
        entryPoints.forEach((ivk) => {
            roots.push(invokes.get(ivk) as MorphirCallGNode);
            MorphirAssembly.topoVisit(invokes.get(ivk) as MorphirCallGNode, [], tordered, invokes);
        });

        assembly.constantDecls.forEach((cdecl) => {
            roots.push(invokes.get(cdecl.consfinv) as MorphirCallGNode);
            MorphirAssembly.topoVisit(invokes.get(cdecl.consfinv) as MorphirCallGNode, [], tordered, invokes);
        });

        tordered = tordered.reverse();

        let marked = new Set<string>();
        let recursive: (Set<string>)[] = [];
        for (let i = 0; i < tordered.length; ++i) {
            let scc = new Set<string>();
            MorphirAssembly.sccVisit(tordered[i], scc, marked, invokes);

            if (scc.size > 1 || tordered[i].callees.has(tordered[i].invoke)) {
                recursive.push(scc);
            }
        }

        return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
    }

    generateMorphir2AssemblyInfo(): Morphir2FileInfo {
        const subtypeasserts = this.subtypeRelation.map((tc) => tc.value ? `(assert (SubtypeOf@ ${tc.ttype} ${tc.atype}))` : `(assert (not (SubtypeOf@ ${tc.ttype} ${tc.atype})))`).sort();
        const indexasserts = this.hasIndexRelation.map((hi) => hi.value ? `(assert (HasIndex@ ${hi.idxtag} ${hi.atype}))` : `(assert (not (HasIndex@ ${hi.idxtag} ${hi.atype})))`).sort();
        const propertyasserts = this.hasPropertyRelation.map((hp) => hp.value ? `(assert (HasProperty@ ${hp.pnametag} ${hp.atype}))` : `(assert (not (HasProperty@ ${hp.pnametag} ${hp.atype})))`).sort();

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `(assert (= (TypeTag_OrdinalOf ${ktt}) ${i}))`);

        const v_min_max: string[] = [
            `(declare-const @BINTMIN Int) (assert (= @BINTMIN ${this.vopts.INT_MIN}))`,
            `(declare-const @BINTMAX Int) (assert (= @BINTMAX ${this.vopts.INT_MAX}))`,
            `(declare-const @BNATMAX Int) (assert (= @BNATMAX ${this.vopts.NAT_MAX}))`,
            `(declare-const @SLENMAX Int) (assert (= @SLENMAX ${this.vopts.SLEN_MAX}))`,
            `(declare-const @BLENMAX Int) (assert (= @BLENMAX ${this.vopts.BLEN_MAX}))`,
            `(declare-const @CONTAINERMAX Int) (assert (= @CONTAINERMAX ${this.vopts.CONTAINER_MAX}))`
        ];

        const termtupleinfo = this.tupleDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.smttypename})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const termrecordinfo = this.recordDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `( (${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.smttypename})`).join(" ")}) )`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const keytypeinfo = this.entityDecls
            .filter((et) => (et instanceof SMTEntityOfTypeDecl) && et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(define-sort ${kt.smtname} () ${(kt as SMTEntityOfTypeDecl).ofsmttype})`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const oftypeinfo = this.entityDecls
            .filter((et) => (et instanceof SMTEntityOfTypeDecl) && !et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(define-sort ${kt.smtname} () ${(kt as SMTEntityOfTypeDecl).ofsmttype})`,
                    boxf: `(${kt.boxf} (${kt.ubf} ${kt.smtname}))`
                };
            });

        const termtypeinfo = this.entityDecls
            .filter((et) => et instanceof SMTEntityStdDecl)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((tt) => {
                return {
                    decl: `(${tt.smtname} 0)`,
                    consf: `( (${(tt as SMTEntityStdDecl).consf.cname} ${(tt as SMTEntityStdDecl).consf.cargs.map((te) => `(${te.fname} ${te.ftype.smttypename})`).join(" ")}) )`,
                    boxf: `(${tt.boxf} (${tt.ubf} ${tt.smtname}))`
                };
            });

        const ofinternaltypeinfo = this.entityDecls
            .filter((et) => et instanceof SMTEntityInternalOfTypeDecl)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((tt) => {
                return {
                    boxf: `(${tt.boxf} (${tt.ubf} ${(tt as SMTEntityInternalOfTypeDecl).ofsmttype}))`
                };
            });

        const collectiontypeinfo = this.entityDecls
            .filter((et) => (et instanceof SMTEntityCollectionTypeDecl))
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((tt) => {
                const ctype = tt as SMTEntityCollectionTypeDecl;
                return {
                    decl: `(${tt.smtname} 0)`,
                    consf: `( (${ctype.consf.cname} ${ctype.consf.cargs.map((te) => `(${te.fname} ${te.ftype})`).join(" ")}) )`,
                    boxf: `(${tt.boxf} (${tt.ubf} ${tt.smtname}))`
                };
            });

        const collectiontypeinfoconsts = this.entityDecls
            .filter((et) => (et instanceof SMTEntityCollectionTypeDecl))
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((tt) => {
                const ctype = tt as SMTEntityCollectionTypeDecl;
                return `(declare-const ${ctype.emptyconst.fname} ${ctype.emptyconst.fkind}) (assert (= ${ctype.emptyconst.fname} ${ctype.emptyconst.fexp}))`;
            });

        const collectionentrytypeinfo = this.entityDecls
            .filter((et) => (et instanceof SMTEntityCollectionTypeDecl) && (et as SMTEntityCollectionTypeDecl).entrydecl !== undefined)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((tt) => {
                const einfo = (tt as SMTEntityCollectionTypeDecl).entrydecl as SMTEntityCollectionEntryTypeDecl;
                return {
                    decl: `(${einfo.smtname} 0)`,
                    consf: `( (${einfo.consf.cname} ${einfo.consf.cargs.map((te) => `(${te.fname} ${te.ftype})`).join(" ")}) )`
                };
            });

        const etypeinfo = this.ephemeralDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((et) => {
                return {
                    decl: `(${et.smtname} 0)`,
                    consf: `( (${et.consf.cname} ${et.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.smttypename})`).join(" ")}) )`
                };
            });

        const rtypeinfo = this.resultTypes
            .sort((t1, t2) => (t1.hasFlag !== t2.hasFlag) ? (t1.hasFlag ? 1 : -1) : t1.rtname.localeCompare(t2.rtname))
            .map((rt) => {
                if (rt.hasFlag) {
                    return {
                        decl: `($GuardResult_${rt.ctype.smttypename} 0)`,
                        consf: `( ($GuardResult_${rt.ctype.smttypename}@cons ($GuardResult_${rt.ctype.smttypename}@result ${rt.ctype.smttypename}) ($GuardResult_${rt.ctype.smttypename}@flag Bool)) )`
                    };
                }
                else {
                    return {
                        decl: `($Result_${rt.ctype.smttypename} 0)`,
                        consf: `( ($Result_${rt.ctype.smttypename}@success ($Result_${rt.ctype.smttypename}@success_value ${rt.ctype.smttypename})) ($Result_${rt.ctype.smttypename}@error ($Result_${rt.ctype.smttypename}@error_value ErrorID)) )`
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
            .map((c) => `(declare-const ${c.gkey} ${c.ctype.smttypename})`);

        const ufdecls = this.uninterpfunctions
            .sort((uf1, uf2) => uf1.fname.localeCompare(uf2.fname))
            .map((uf) => uf.emitSMT2());

        const ufopdecls = this.uninterpOps
            .sort((pf1, pf2) => pf1.localeCompare(pf2));

        const gdefs = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => {
                if (c.checkf === undefined) {
                    return `(assert (= ${c.gkey} ${c.consfexp.emitSMT2(undefined)}))`;
                }
                else {
                    return `(assert ${c.checkf.emitSMT2(undefined)}) (assert (= ${c.gkey} ${c.consfexp.emitSMT2(undefined)}))`;
                }
            });

        const mmodel = this.model as SMTModelState;
        let action: string[] = [];
        mmodel.arginits.map((iarg) => {
            action.push(`(declare-const ${iarg.vname} ${iarg.vtype.smttypename})`);

            action.push(`(assert (= ${iarg.vname} ${iarg.vinit.emitSMT2(undefined)}))`);

            if(iarg.vchk !== undefined) {
                action.push(`(assert ${iarg.vchk.emitSMT2(undefined)})`);
            }
        });

        if(mmodel.argchk !== undefined) {
            action.push(...mmodel.argchk.map((chk) => `(assert ${chk.emitSMT2(undefined)})`));
        }

        action.push(`(declare-const _@smtres@ ${mmodel.checktype.smttypename})`);
        action.push(`(assert (= _@smtres@ ${mmodel.fcheck.emitSMT2(undefined)}))`);

        if (this.vopts.ActionMode === SymbolicActionMode.ErrTestSymbolic) {
            action.push(`(assert ${mmodel.targeterrorcheck.emitSMT2(undefined)})`);
        }
        else if(this.vopts.ActionMode === SymbolicActionMode.ChkTestSymbolic) {
            action.push(`(assert ${mmodel.isvaluecheck.emitSMT2(undefined)})`);
            action.push(`(assert ${mmodel.isvaluefalsechk.emitSMT2(undefined)})`)
        }
        else {
            action.push(`(assert ${mmodel.isvaluecheck.emitSMT2(undefined)})`);
        
            const resi = mmodel.resinit as { vname: string, vtype: SMTTypeInfo, vchk: SMTExp | undefined, vinit: SMTExp, callexp: SMTExp };
            action.push(`(declare-const ${resi.vname} ${resi.vtype.smttypename})`);
            action.push(`(assert (= ${resi.vname} ${resi.vinit.emitSMT2(undefined)}))`);
            if(resi.vchk !== undefined) {
                action.push(`(assert ${resi.vchk.emitSMT2(undefined)})`);
            }

            action.push(`(assert (= ${resi.vname} _@smtres@))`);
        }

        let foutput: string[] = [];
        let doneset: Set<string> = new Set<string>();
        const cginfo = SMTAssembly.constructCallGraphInfo([this.entrypoint, ...this.havocfuncs], this);
        const rcg = [...cginfo.topologicalOrder];

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
                if(worklist.length === 1) {
                    const cf = worklist.shift() as string;
                    const crf = this.functions.find((f) => f.fname === cf) as SMTFunction;

                    const decl = crf.emitSMT2_SingleDeclOnly();
                    const impl = crf.body.emitSMT2("  ");

                    if (cscc !== undefined) {
                        cscc.forEach((v) => doneset.add(v));
                    }

                    foutput.push(`(define-fun-rec ${decl}\n ${impl}\n)`);
                }
                else {
                    let decls: string[] = [];
                    let impls: string[] = [];
                    while (worklist.length !== 0) {
                        const cf = worklist.shift() as string;
                        const crf = this.functions.find((f) => f.fname === cf) as SMTFunction;

                        decls.push(crf.emitSMT2_DeclOnly());
                        impls.push(crf.body.emitSMT2("  "));
                    }

                    if (cscc !== undefined) {
                        cscc.forEach((v) => doneset.add(v));
                    }

                    foutput.push(`(define-funs-rec (\n  ${decls.join("\n  ")}\n) (\n${impls.join("\n")}))`);
                }
            }
        }   

        return {
            TYPE_TAG_DECLS: this.typeTags.sort().map((tt) => `(${tt})`),
            ORDINAL_TYPE_TAG_DECLS: keytypeorder,
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes.sort().map((tt) => `(${tt})`),
            INDEX_TAG_DECLS: this.indexTags.sort().map((tt) => `(${tt})`),
            PROPERTY_TAG_DECLS: this.propertyTags.sort().map((tt) => `(${tt})`),
            SUBTYPE_DECLS: subtypeasserts,
            TUPLE_HAS_INDEX_DECLS: indexasserts,
            RECORD_HAS_PROPERTY_DECLS: propertyasserts,
            STRING_TYPE_ALIAS: "(define-sort BString () String)",
            OF_TYPE_DECLS: [...keytypeinfo.map((kd) => kd.decl), ...oftypeinfo.map((td) => td.decl)],
            KEY_BOX_OPS: [...keytypeinfo.map((kd) => kd.boxf), ...oftypeinfo.map((td) => td.boxf)],
            TUPLE_INFO: { 
                decls: termtupleinfo.map((kti) => kti.decl), constructors: termtupleinfo.map((kti) => kti.consf), 
                boxing: termtupleinfo.map((kti) => kti.boxf) 
            },
            RECORD_INFO: { 
                decls: termrecordinfo.map((kti) => kti.decl), constructors: termrecordinfo.map((kti) => kti.consf), 
                boxing: termrecordinfo.map((kti) => kti.boxf) 
            },
            TYPE_INFO: { 
                decls: [
                    ...termtypeinfo.filter((tti) => tti.decl !== undefined).map((tti) => tti.decl as string),
                    ...collectiontypeinfo.map((clti) => clti.decl),
                    ...collectionentrytypeinfo.map((clti) => clti.decl)
                ], 
                constructors: [
                    ...termtypeinfo.filter((tti) => tti.consf !== undefined).map((tti) => tti.consf as string),
                    ...collectiontypeinfo.map((clti) => clti.consf),
                    ...collectionentrytypeinfo.map((clti) => clti.consf)
                ], 
                boxing: [
                    ...termtypeinfo.map((tti) => tti.boxf), 
                    ...ofinternaltypeinfo.map((ttofi) => ttofi.boxf), 
                    ...collectiontypeinfo.map((cti) => cti.boxf)
                ] 
            },
            EPHEMERAL_DECLS: { 
                decls: etypeinfo.map((kti) => kti.decl), 
                constructors: etypeinfo.map((kti) => kti.consf) 
            },
            RESULT_INFO: { 
                decls: rtypeinfo.map((kti) => kti.decl), 
                constructors: rtypeinfo.map((kti) => kti.consf) 
            },
            MASK_INFO: { 
                decls: maskinfo.map((mi) => mi.decl), 
                constructors: maskinfo.map((mi) => mi.consf) 
            },
            V_MIN_MAX: v_min_max,
            GLOBAL_DECLS: [
                ...collectiontypeinfoconsts,
                ...gdecls
            ],
            UF_DECLS: [...ufdecls, ...ufopdecls],
            FUNCTION_DECLS: foutput.reverse(),
            GLOBAL_DEFINITIONS: gdefs,
            ACTION: action
        };
    }

    buildSMT2file(smtruntime: string): string {
        const sfileinfo = this.generateSMT2AssemblyInfo();
    
        function joinWithIndent(data: string[], indent: string): string {
            if (data.length === 0) {
                return ";;NO DATA;;"
            }
            else {
                return data.map((d, i) => (i === 0 ? "" : indent) + d).join("\n");
            }
        }

        const contents = smtruntime
            .replace(";;TYPE_TAG_DECLS;;", joinWithIndent(sfileinfo.TYPE_TAG_DECLS, "      "))
            .replace(";;ORDINAL_TAG_DECLS;;", joinWithIndent(sfileinfo.ORDINAL_TYPE_TAG_DECLS, ""))
            .replace(";;ABSTRACT_TYPE_TAG_DECLS;;", joinWithIndent(sfileinfo.ABSTRACT_TYPE_TAG_DECLS, "      "))
            .replace(";;INDEX_TAG_DECLS;;", joinWithIndent(sfileinfo.INDEX_TAG_DECLS, "      "))
            .replace(";;PROPERTY_TAG_DECLS;;", joinWithIndent(sfileinfo.PROPERTY_TAG_DECLS, "      "))
            .replace(";;SUBTYPE_DECLS;;", joinWithIndent(sfileinfo.SUBTYPE_DECLS, ""))
            .replace(";;TUPLE_HAS_INDEX_DECLS;;", joinWithIndent(sfileinfo.TUPLE_HAS_INDEX_DECLS, ""))
            .replace(";;RECORD_HAS_PROPERTY_DECLS;;", joinWithIndent(sfileinfo.RECORD_HAS_PROPERTY_DECLS, ""))
            .replace(";;BSTRING_TYPE_ALIAS;;", sfileinfo.STRING_TYPE_ALIAS)
            .replace(";;OF_TYPE_DECLS;;", joinWithIndent(sfileinfo.OF_TYPE_DECLS, ""))
            .replace(";;KEY_BOX_OPS;;", joinWithIndent(sfileinfo.KEY_BOX_OPS, "      "))
            .replace(";;TUPLE_DECLS;;", joinWithIndent(sfileinfo.TUPLE_INFO.decls, "    "))
            .replace(";;RECORD_DECLS;;", joinWithIndent(sfileinfo.RECORD_INFO.decls, "    "))
            .replace(";;TYPE_DECLS;;", joinWithIndent(sfileinfo.TYPE_INFO.decls, "    "))
            .replace(";;TUPLE_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.TUPLE_INFO.constructors, "    "))
            .replace(";;RECORD_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.RECORD_INFO.constructors, "    "))
            .replace(";;TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.TYPE_INFO.constructors, "    "))
            .replace(";;TUPLE_TYPE_BOXING;;", joinWithIndent(sfileinfo.TUPLE_INFO.boxing, "      "))
            .replace(";;RECORD_TYPE_BOXING;;", joinWithIndent(sfileinfo.RECORD_INFO.boxing, "      "))
            .replace(";;TYPE_BOXING;;", joinWithIndent(sfileinfo.TYPE_INFO.boxing, "      "))
            .replace(";;EPHEMERAL_DECLS;;", joinWithIndent(sfileinfo.EPHEMERAL_DECLS.decls, "      "))
            .replace(";;EPHEMERAL_CONSTRUCTORS;;", joinWithIndent(sfileinfo.EPHEMERAL_DECLS.constructors, "      "))
            .replace(";;RESULT_DECLS;;", joinWithIndent(sfileinfo.RESULT_INFO.decls, "      "))
            .replace(";;MASK_DECLS;;", joinWithIndent(sfileinfo.MASK_INFO.decls, "      "))
            .replace(";;RESULTS;;", joinWithIndent(sfileinfo.RESULT_INFO.constructors, "    "))
            .replace(";;MASKS;;", joinWithIndent(sfileinfo.MASK_INFO.constructors, "    "))
            .replace(";;V_MIN_MAX;;", joinWithIndent(sfileinfo.V_MIN_MAX, ""))
            .replace(";;GLOBAL_DECLS;;", joinWithIndent(sfileinfo.GLOBAL_DECLS, ""))
            .replace(";;UF_DECLS;;", joinWithIndent(sfileinfo.UF_DECLS, "\n"))
            .replace(";;FUNCTION_DECLS;;", joinWithIndent(sfileinfo.FUNCTION_DECLS, "\n"))
            .replace(";;GLOBAL_DEFINITIONS;;", joinWithIndent(sfileinfo.GLOBAL_DEFINITIONS, ""))
            .replace(";;ACTION;;", joinWithIndent(sfileinfo.ACTION, ""));
    
        return contents;
    }
}

export {
    MorphirEntityDecl, MorphirEntityOfTypeDecl, MorphirEntityInternalOfTypeDecl, MorphirEntityCollectionTypeDecl, MorphirEntityCollectionEntryTypeDecl,
    MorphirEntityStdDecl,
    MorphirTupleDecl, MorphirRecordDecl, MorphirEphemeralListDecl,
    MorphirConstantDecl,
    MorphirFunction,
    MorphirAssembly, Morphir2FileInfo
};

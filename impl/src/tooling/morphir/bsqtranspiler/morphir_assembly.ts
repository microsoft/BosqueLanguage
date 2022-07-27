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
    INDEX_TAG_DECLS: string[],
    PROPERTY_TAG_DECLS: string[],
    SUBTYPE_DECLS: string[],
    TUPLE_HAS_INDEX_DECLS: string[],
    RECORD_HAS_PROPERTY_DECLS: string[],
    OF_TYPE_DECLS: string[],
    KEY_BOX_OPS: string[],
    KEY_UNBOX_OPS: string[],
    KEY_DEFAULT_OPS: string[],
    TUPLE_TYPE_DECLS: string[],
    RECORD_TYPE_DECLS: string[],
    TYPE_DECLS: string[],

    TUPLE_INFO: { decls: string[], boxing: string[], unboxing: string[] },
    RECORD_INFO: { decls: string[], boxing: string[], unboxing: string[] },
    TYPE_INFO: { decls: string[], constructors: string[], boxing: string[], unboxing: string[] }
    EPHEMERAL_DECLS: { decls: string[] },
    MASK_INFO: { decls: string[], constructors: string[] },
    GLOBAL_DECLS: string[],
    FUNCTION_DECLS: string[],
    GLOBAL_DEFINITIONS: string[],
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

class MorphirEntityCollectionTypeDecl extends MorphirEntityDecl {
    readonly underlyingtype: string;

    constructor(morphirname: string, typetag: string, underlyingtype: string, boxf: string, ubf: string) {
        super(false, morphirname, typetag, boxf, ubf);

        this.underlyingtype = underlyingtype;
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
        //"TypeTag_None",
        //"TypeTag_Nothing",
        //Already set in file
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
        const subtypeasserts = this.subtypeRelation.map((tc) => `    | (${tc.ttype} ${tc.atype}) -> \n        True`).sort();
        const indexasserts = this.hasIndexRelation.map((hi) => `    | (${hi.idxtag} ${hi.atype}) -> \n        True`).sort();
        const propertyasserts = this.hasPropertyRelation.map((hp) => `    | (${hp.pnametag} ${hp.atype}) -> \n        True`).sort();

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `    TypeTag_OrdinalOf ${ktt} -> \n        ${i}`);

        const termtupleinfo = this.tupleDecls
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((kt) => {
                return {
                    decl: `type alias ${kt.morphirname} = {${kt.consf.cargs.map((ke) => `${ke.fname}: ${ke.ftype.morphirtypename})`).join(" ")}}`,
                    consfdecl: `${kt.consf.cname} : ${kt.consf.cargs.map((ke) => `${ke.ftype.morphirtypename}`).join(" -> ")} -> ${kt.morphirname}`,
                    consfimpl: `${kt.consf.cname} ${kt.consf.cargs.map((ke) => `arg_${ke.fname}`).join(" ")} = {${kt.consf.cargs.map((ke) => `${ke.fname} = arg_${ke.fname})`).join(" ")}}`,
                    boxf: `${kt.boxf} ${kt.morphirname}`,
                    unboxfdecl: `${kt.ubf} : BTerm -> ${kt.morphirname}`,
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLocaleLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLocaleLowerCase()}_default = \n    {${kt.consf.cargs.map((ke) => `${ke.fname} = bsq${ke.ftype.typeID.toLocaleLowerCase()}_default`).join(" ")}}`
                };
            });

        const termrecordinfo = this.recordDecls
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((kt) => {
                return {
                    decl: `type alias ${kt.morphirname} = {${kt.consf.cargs.map((ke) => `${ke.fname}: ${ke.ftype.morphirtypename})`).join(" ")}}`,
                    consfdecl: `${kt.consf.cname} : ${kt.consf.cargs.map((ke) => `${ke.ftype.morphirtypename}`).join(" -> ")} -> ${kt.morphirname}`,
                    consfimpl: `${kt.consf.cname} ${kt.consf.cargs.map((ke) => `arg_${ke.fname}`).join(" ")} = {${kt.consf.cargs.map((ke) => `${ke.fname} = arg_${ke.fname})`).join(" ")}}`,
                    boxf: `${kt.boxf} ${kt.morphirname}`,
                    unboxfdecl: `${kt.ubf} : BTerm -> ${kt.morphirname}`,
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLocaleLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLocaleLowerCase()}_default = \n    {${kt.consf.cargs.map((ke) => `${ke.fname} = bsq${ke.ftype.typeID.toLocaleLowerCase()}_default`).join(" ")}}`
                };
            });

        const keyoftypeinfo = this.entityDecls
        .filter((et) => (et instanceof MorphirEntityOfTypeDecl) && et.iskeytype)
        .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
        .map((kt) => {
            const eokt = kt as MorphirEntityOfTypeDecl;

            return {
                decl: `type alias ${kt.morphirname} = ${eokt.ofsmttype}`,
                boxf: `${kt.boxf} ${kt.morphirname}`,
                unboxfdecl: `${kt.ubf} : BKey -> ${kt.morphirname}`,
                unboxfimpl: `${kt.ubf} k = \n    case k of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLocaleLowerCase()}_default`,
                defaultdecl: `bsq${kt.typetag.toLocaleLowerCase()}_default : ${kt.morphirname}`,
                defaultimpl: `bsq${kt.typetag.toLocaleLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLocaleLowerCase()}_default`
            };
        });

        const oftypeinfo = this.entityDecls
            .filter((et) => (et instanceof MorphirEntityOfTypeDecl) && !et.iskeytype)
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((kt) => {
                const eokt = kt as MorphirEntityOfTypeDecl;

                return {
                    decl: `type alias ${kt.morphirname} = ${eokt.ofsmttype}`,
                    boxf: `${kt.boxf} ${kt.morphirname}`,
                    unboxfdecl: `${kt.ubf} : BTerm -> ${kt.morphirname}`,
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLocaleLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLocaleLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLocaleLowerCase()}_default`
                };
            });

        const termtypeinfo = this.entityDecls
            .filter((et) => et instanceof MorphirEntityStdDecl)
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((tval) => {
                const tt = tval as MorphirEntityStdDecl;
                return {
                    decl: `type alias ${tt.morphirname} = {${tt.consf.cargs.map((te) => `${te.fname}: ${te.ftype.morphirtypename})`).join(" ")}}`,
                    consfdecl: `${tt.consf.cname} : ${tt.consf.cargs.map((te) => `${te.ftype.morphirtypename}`).join(" -> ")} -> ${tt.morphirname}`,
                    consfimpl: `${tt.consf.cname} ${tt.consf.cargs.map((te) => `arg_${te.fname}`).join(" ")} = {${tt.consf.cargs.map((te) => `${te.fname} = arg_${te.fname})`).join(" ")}}`,
                    boxf: `${tt.boxf} ${tt.morphirname}`,
                    unboxfdecl: `${tt.ubf} : BTerm -> ${tt.morphirname}`,
                    unboxfimpl: `${tt.ubf} t = \n    case t of\n        ${tt.boxf} v -> \n            v\n        _ -> \n            bsq${tt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${tt.typetag.toLocaleLowerCase()}_default : ${tt.morphirname}`,
                    defaultimpl: `bsq${tt.typetag.toLocaleLowerCase()}_default = \n    {${tt.consf.cargs.map((te) => `${te.fname} = bsq${te.ftype.typeID.toLocaleLowerCase()}_default`).join(" ")}}`
                };
            });

        const ofinternaltypeinfo = this.entityDecls
            .filter((et) => et instanceof MorphirEntityInternalOfTypeDecl)
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((kt) => {
                const eokt = kt as MorphirEntityInternalOfTypeDecl;

                return {
                    decl: `type alias ${kt.morphirname} = ${eokt.ofsmttype}`,
                    boxf: `${kt.boxf} ${kt.morphirname}`,
                    unboxfdecl: `${kt.ubf} : BTerm -> ${kt.morphirname}`,
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLocaleLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLocaleLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLocaleLowerCase()}_default`
                };
            });

        const collectiontypeinfo = this.entityDecls
            .filter((et) => (et instanceof MorphirEntityCollectionTypeDecl))
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((tt) => {
                const ctype = tt as MorphirEntityCollectionTypeDecl;

                tt.morphirname
                return {
                    decl: `type alias ${tt.morphirname} = ${ctype.underlyingtype}`,
                    boxf: `${tt.boxf} ${tt.morphirname}`,
                    unboxfdecl: `${tt.ubf} : BTerm -> ${tt.morphirname}`,
                    unboxfimpl: `${tt.ubf} t = \n    case t of\n        ${tt.boxf} v -> \n            v\n        _ -> \n            bsq${tt.typetag.toLocaleLowerCase()}_default`,
                    defaultdecl: `bsq${tt.typetag.toLocaleLowerCase()}_default : ${tt.morphirname}`,
                    defaultimpl: `bsq${tt.typetag.toLocaleLowerCase()}_default = \n    []`
                };
            });

        const etypeinfo = this.ephemeralDecls
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((et) => {
                return {
                    decl: `(${et.smtname} 0)`,
                    consf: `( (${et.consf.cname} ${et.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.smttypename})`).join(" ")}) )`
                };
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
        const cginfo = MorphirAssembly.constructCallGraphInfo([this.entrypoint], this);
        const rcg = [...cginfo.topologicalOrder];

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const rf = this.functions.find((f) => f.fname === cn.invoke) as MorphirFunction;
            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            if(cscc === undefined) {
                doneset.add(cn.invoke);
                foutput.push(rf.emitMorphir());
            }
            else {
                let worklist = [...cscc].sort();
                if(worklist.length === 1) {
                    const cf = worklist.shift() as string;
                    const crf = this.functions.find((f) => f.fname === cf) as MorphirFunction;

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
                        const crf = this.functions.find((f) => f.fname === cf) as MorphirFunction;

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
            TYPE_TAG_DECLS: this.typeTags.sort().map((tt) => `    | ${tt}`),
            ORDINAL_TYPE_TAG_DECLS: keytypeorder,
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes.sort().map((tt) => `    | ${tt}`),
            INDEX_TAG_DECLS: this.hasIndexRelation.map((ir) => ir.idxtag).sort().map((idxtag) => `    | ${idxtag}`),
            PROPERTY_TAG_DECLS: this.hasPropertyRelation.map((pr) => pr.pnametag).sort().map((pntag) => `    | ${pntag}`),
            SUBTYPE_DECLS: subtypeasserts,
            TUPLE_HAS_INDEX_DECLS: indexasserts,
            RECORD_HAS_PROPERTY_DECLS: propertyasserts,
            OF_TYPE_DECLS: [...keyoftypeinfo.map((kti) => kti.decl), ...oftypeinfo.map((oti) => oti.decl)],
            KEY_BOX_OPS: keyoftypeinfo.map((kb) =>  `    | ${kb.boxf}`),
            KEY_UNBOX_OPS: keyoftypeinfo.map((kb) => kb.unboxfdecl + kb.unboxfimpl),
            KEY_DEFAULT_OPS: keyoftypeinfo.map((kb) => kb.defaultdecl + kb.defaultimpl),
            TUPLE_TYPE_DECLS: termtupleinfo.map((ti) => ti.decl),
            RECORD_TYPE_DECLS: termrecordinfo.map((ri) => ri.decl),
            TYPE_DECLS: [...ofinternaltypeinfo.map((oti) => oti.decl), ...collectiontypeinfo.map((cti) => cti.decl), ...termtypeinfo.map((ti) => ti.decl)],
            

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
            
            MASK_INFO: { 
                decls: maskinfo.map((mi) => mi.decl), 
                constructors: maskinfo.map((mi) => mi.consf) 
            },
            GLOBAL_DECLS: gdecls,
            FUNCTION_DECLS: foutput.reverse(),
            GLOBAL_DEFINITIONS: gdefs
        };
    }

    buildMorphir2file(morphirruntime: string): string {
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
    MorphirEntityDecl, MorphirEntityOfTypeDecl, MorphirEntityInternalOfTypeDecl, MorphirEntityCollectionTypeDecl,
    MorphirEntityStdDecl,
    MorphirTupleDecl, MorphirRecordDecl, MorphirEphemeralListDecl,
    MorphirConstantDecl,
    MorphirFunction,
    MorphirAssembly, Morphir2FileInfo
};

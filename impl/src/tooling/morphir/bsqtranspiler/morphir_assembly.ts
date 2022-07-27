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
    TUPLE_TYPE_BOXING: string[],
    RECORD_TYPE_BOXING: string[],
    TYPE_BOXING: string[],
    TERM_DEFAULT: string[],
    TERM_UNBOX_OPS: string[],
    EPHEMERAL_DECLS: string[],
    MASK_INFO: string[],
    GLOBAL_DECLS: string[],
    FUNCTION_DECLS: string[],
    GLOBAL_DEFINITIONS: string[]
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
        const implargs = this.args.map((arg) => `${arg.vname}`).join(" ");
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

    constructor(gkey: string, optenumname: [MIRResolvedTypeKey, string] | undefined, ctype: MorphirTypeInfo, consfinv: string, consfexp: MorphirExp) {
        this.gkey = gkey;
        this.optenumname = optenumname;
        this.ctype = ctype;

        this.consfinv = consfinv;

        this.consfexp = consfexp;
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

    entrypoints: string[];

    constructor(entrypoints: string[]) {
        this.entrypoints = entrypoints;
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

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `        TypeTag_OrdinalOf ${ktt} -> \n            ${i}`);

        const termtupleinfo = this.tupleDecls
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((kt) => {
                return {
                    decl: `type alias ${kt.morphirname} = {${kt.consf.cargs.map((ke) => `${ke.fname}: ${ke.ftype.morphirtypename})`).join(" ")}}`,
                    consfdecl: `${kt.consf.cname} : ${kt.consf.cargs.map((ke) => `${ke.ftype.morphirtypename}`).join(" -> ")} -> ${kt.morphirname}`,
                    consfimpl: `${kt.consf.cname} ${kt.consf.cargs.map((ke) => `arg_${ke.fname}`).join(" ")} = {${kt.consf.cargs.map((ke) => `${ke.fname} = arg_${ke.fname})`).join(" ")}}`,
                    boxf: `${kt.boxf} ${kt.morphirname}`,
                    unboxfdecl: `${kt.ubf} : BTerm -> ${kt.morphirname}`,
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLowerCase()}_default = \n    {${kt.consf.cargs.map((ke) => `${ke.fname} = bsq${ke.ftype.typeID.toLowerCase()}_default`).join(" ")}}`
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
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLowerCase()}_default = \n    {${kt.consf.cargs.map((ke) => `${ke.fname} = bsq${ke.ftype.typeID.toLowerCase()}_default`).join(" ")}}`
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
                unboxfimpl: `${kt.ubf} k = \n    case k of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLowerCase()}_default`,
                defaultdecl: `bsq${kt.typetag.toLowerCase()}_default : ${kt.morphirname}`,
                defaultimpl: `bsq${kt.typetag.toLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLowerCase()}_default`
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
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLowerCase()}_default`
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
                    unboxfimpl: `${tt.ubf} t = \n    case t of\n        ${tt.boxf} v -> \n            v\n        _ -> \n            bsq${tt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${tt.typetag.toLowerCase()}_default : ${tt.morphirname}`,
                    defaultimpl: `bsq${tt.typetag.toLowerCase()}_default = \n    {${tt.consf.cargs.map((te) => `${te.fname} = bsq${te.ftype.typeID.toLowerCase()}_default`).join(" ")}}`
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
                    unboxfimpl: `${kt.ubf} t = \n    case t of\n        ${kt.boxf} v -> \n            v\n        _ -> \n            bsq${kt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${kt.typetag.toLowerCase()}_default : ${kt.morphirname}`,
                    defaultimpl: `bsq${kt.typetag.toLowerCase()}_default = \n    bsq${eokt.ofsmttype.toLowerCase()}_default`
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
                    unboxfimpl: `${tt.ubf} t = \n    case t of\n        ${tt.boxf} v -> \n            v\n        _ -> \n            bsq${tt.typetag.toLowerCase()}_default`,
                    defaultdecl: `bsq${tt.typetag.toLowerCase()}_default : ${tt.morphirname}`,
                    defaultimpl: `bsq${tt.typetag.toLowerCase()}_default = \n    []`
                };
            });

        const etypeinfo = this.ephemeralDecls
            .sort((t1, t2) => t1.morphirname.localeCompare(t2.morphirname))
            .map((et) => {
                return {
                    decl: `type alias ${et.morphirname} = {${et.consf.cargs.map((te) => `${te.fname}: ${te.ftype.morphirtypename})`).join(" ")}}`,
                    consfdecl: `${et.consf.cname} : ${et.consf.cargs.map((te) => `${te.ftype.morphirtypename}`).join(" -> ")} -> ${et.morphirname}`,
                    consfimpl: `${et.consf.cname} ${et.consf.cargs.map((te) => `arg_${te.fname}`).join(" ")} = {${et.consf.cargs.map((te) => `${te.fname} = arg_${te.fname})`).join(" ")}}`
                };
            });

        const maskinfo = [...this.maskSizes]
            .sort()
            .map((msize) => {
                let declentries: string[] = [];
                let implentries: string[] = [];
                for(let i = 0; i < msize; ++i) {
                    declentries.push(`Bool`);
                    implentries.push(`arg_mask_${msize}_${i}`);
                }

                return {
                    decl: `type alias mask_${msize} = List Bool`,
                    consfdecl: `mask_${msize}_cons ${declentries.join(" -> ")} -> mask_${msize}`,
                    consfimpl: `mask_${msize}_cons ${implentries.join(" ")} = [${implentries.join(", ")}]`
                };
            });

        const gdecls = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => `${c.gkey} ${c.ctype.morphirtypename}`);

        const gdefs = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => {
                    return `${c.gkey} = \n    ${c.consfexp.emitMorphir(undefined)}`;
            });

        let foutput: string[] = [];
        let doneset: Set<string> = new Set<string>();
        const cginfo = MorphirAssembly.constructCallGraphInfo(this.entrypoints, this);
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

                    const impl = crf.emitMorphir();

                    if (cscc !== undefined) {
                        cscc.forEach((v) => doneset.add(v));
                    }

                    foutput.push(impl);
                }
                else {
                    let impls: string[] = [];
                    while (worklist.length !== 0) {
                        const cf = worklist.shift() as string;
                        const crf = this.functions.find((f) => f.fname === cf) as MorphirFunction;

                        impls.push(crf.emitMorphir());
                    }

                    if (cscc !== undefined) {
                        cscc.forEach((v) => doneset.add(v));
                    }

                    foutput.push(impls.join("\n"));
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
            OF_TYPE_DECLS: [...keyoftypeinfo.map((kti) => kti.decl).sort(), ...oftypeinfo.map((oti) => oti.decl).sort()],
            KEY_BOX_OPS: keyoftypeinfo.map((kb) =>  `    | ${kb.boxf}`).sort(),
            KEY_UNBOX_OPS: keyoftypeinfo.map((kb) => kb.unboxfdecl + "\n" + kb.unboxfimpl).sort(),
            KEY_DEFAULT_OPS: keyoftypeinfo.map((kb) => kb.defaultdecl + "\n" + kb.defaultimpl).sort(),
            TUPLE_TYPE_DECLS: termtupleinfo.map((ti) => ti.decl).sort(),
            RECORD_TYPE_DECLS: termrecordinfo.map((ri) => ri.decl).sort(),
            TYPE_DECLS: [...ofinternaltypeinfo.map((oti) => oti.decl).sort(), ...collectiontypeinfo.map((cti) => cti.decl).sort(), ...termtypeinfo.map((ti) => ti.decl).sort()],   
            TUPLE_TYPE_BOXING: termtupleinfo.map((ti) => ti.boxf).sort().map((ttb) => `    | ${ttb}`),
            RECORD_TYPE_BOXING: termrecordinfo.map((ri) => ri.boxf).sort().map((trb) => `    | ${trb}`),
            TYPE_BOXING: [
                ...ofinternaltypeinfo.map((oti) => oti.boxf).sort().map((ttb) => `    | ${ttb}`), 
                ...collectiontypeinfo.map((cti) => cti.boxf).sort().map((ttb) => `    | ${ttb}`), 
                ...termtypeinfo.map((ti) => ti.boxf).sort().map((ttb) => `    | ${ttb}`)
            ],
            TERM_DEFAULT: [
                ...termtupleinfo.map((tti) => tti.defaultdecl + "\n" + tti.defaultimpl).sort(),
                ...termrecordinfo.map((tti) => tti.defaultdecl + "\n" + tti.defaultimpl).sort(),
                ...ofinternaltypeinfo.map((tti) => tti.defaultdecl + "\n" + tti.defaultimpl).sort(),
                ...collectiontypeinfo.map((tti) => tti.defaultdecl + "\n" + tti.defaultimpl).sort(),
                ...termtypeinfo.map((tti) => tti.defaultdecl + "\n" + tti.defaultimpl).sort()
            ],
            TERM_UNBOX_OPS: [
                ...termtupleinfo.map((tti) => tti.unboxfdecl + "\n" + tti.unboxfimpl).sort(),
                ...termrecordinfo.map((tti) => tti.unboxfdecl + "\n" + tti.unboxfimpl).sort(),
                ...ofinternaltypeinfo.map((tti) => tti.unboxfdecl + "\n" + tti.unboxfimpl).sort(),
                ...collectiontypeinfo.map((tti) => tti.unboxfdecl + "\n" + tti.unboxfimpl).sort(),
                ...termtypeinfo.map((tti) => tti.unboxfdecl + "\n" + tti.unboxfimpl).sort()
            ],

            EPHEMERAL_DECLS: etypeinfo.map((eti) => eti.decl + eti.consfdecl + eti.consfimpl).sort(),
            MASK_INFO: maskinfo.map((mti) => mti.decl + mti.consfdecl + mti.consfimpl).sort(),

            GLOBAL_DECLS: gdecls,
            FUNCTION_DECLS: foutput.reverse(),
            GLOBAL_DEFINITIONS: gdefs
        };
    }

    buildMorphir2file(morphirruntime: string): string {
        const sfileinfo = this.generateMorphir2AssemblyInfo();
    
        function joinWithIndent(data: string[], indent: string): string {
            if (data.length === 0) {
                return "--NO DATA--"
            }
            else {
                return data.map((d, i) => (i === 0 ? "" : indent) + d).join("\n");
            }
        }

        const contents = morphirruntime
            .replace("--TYPE_TAG_DECLS--", joinWithIndent(sfileinfo.TYPE_TAG_DECLS, ""))
            .replace("--ORDINAL_TYPE_TAG_DECLS--", joinWithIndent(sfileinfo.ORDINAL_TYPE_TAG_DECLS, ""))
            .replace("--ABSTRACT_TYPE_TAG_DECLS--", joinWithIndent(sfileinfo.ABSTRACT_TYPE_TAG_DECLS, ""))
            .replace("--INDEX_TAG_DECLS--", joinWithIndent(sfileinfo.INDEX_TAG_DECLS, ""))
            .replace("--PROPERTY_TAG_DECLS--", joinWithIndent(sfileinfo.PROPERTY_TAG_DECLS, ""))
            .replace("--SUBTYPE_DECLS--", joinWithIndent(sfileinfo.SUBTYPE_DECLS, ""))
            .replace("--TUPLE_HAS_INDEX_DECLS--", joinWithIndent(sfileinfo.TUPLE_HAS_INDEX_DECLS, ""))
            .replace("--RECORD_HAS_PROPERTY_DECLS--", joinWithIndent(sfileinfo.RECORD_HAS_PROPERTY_DECLS, ""))
            .replace("--OF_TYPE_DECLS--", joinWithIndent(sfileinfo.OF_TYPE_DECLS, ""))
            .replace("--KEY_BOX_OPS--", joinWithIndent(sfileinfo.KEY_BOX_OPS, ""))
            .replace("--KEY_UNBOX_OPS--", joinWithIndent(sfileinfo.KEY_UNBOX_OPS, ""))
            .replace("--KEY_DEFAULT_OPS--", joinWithIndent(sfileinfo.KEY_DEFAULT_OPS, ""))
            .replace("--TUPLE_TYPE_DECLS--", joinWithIndent(sfileinfo.TUPLE_TYPE_DECLS, ""))
            .replace("--RECORD_TYPE_DECLS--", joinWithIndent(sfileinfo.RECORD_TYPE_DECLS, ""))
            .replace("--TYPE_DECLS--", joinWithIndent(sfileinfo.TYPE_DECLS, ""))
            .replace("--TUPLE_TYPE_BOXING--", joinWithIndent(sfileinfo.TUPLE_TYPE_BOXING, ""))
            .replace("--RECORD_TYPE_BOXING--", joinWithIndent(sfileinfo.RECORD_TYPE_BOXING, ""))
            .replace("--TYPE_BOXING--", joinWithIndent(sfileinfo.TYPE_BOXING, ""))
            .replace("--TERM_DEFAULT--", joinWithIndent(sfileinfo.TERM_DEFAULT, ""))
            .replace("--TERM_UNBOX_OPS--", joinWithIndent(sfileinfo.TERM_UNBOX_OPS, ""))
            .replace("--EPHEMERAL_DECLS--", joinWithIndent(sfileinfo.EPHEMERAL_DECLS, ""))
            .replace("--MASK_INFO--", joinWithIndent(sfileinfo.MASK_INFO, ""))
            .replace("--GLOBAL_DECLS--", joinWithIndent(sfileinfo.GLOBAL_DECLS, ""))
            .replace("--FUNCTION_DECLS--", joinWithIndent(sfileinfo.FUNCTION_DECLS, ""))
            .replace("--GLOBAL_DEFINITIONS--", joinWithIndent(sfileinfo.GLOBAL_DEFINITIONS, ""));
    
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

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { Argument, ICPPOp } from "./icpp_exp";

import { BSQRegex } from "../../../ast/bsqregex";

type TranspilerOptions = {
};

type SourceInfo = {
    line: number;
    column: number;
};

const ICPP_WORD_SIZE = 8;
const UNIVERSAL_CONTENT_SIZE = 32;
const UNIVERSAL_TOTAL_SIZE = 40;

type RefMask = string;

class ICPPTypeSizeInfoSimple {
    readonly tkey: MIRResolvedTypeKey;

    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask) {
        this.tkey = tkey;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;
        this.inlinedmask = inlinedmask;
    }

    isScalarOnlyInline(): boolean {
        return /1+/.test(this.inlinedmask);
    }

    static createByRegisterSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, inlinedatasize, assigndatasize, inlinedmask);
    }

    static createByValueSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, inlinedatasize, inlinedatasize, inlinedmask);
    }

    static createByRefSizeInfo(tkey: MIRResolvedTypeKey): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2");
    }
}

class ICPPTypeSizeInfo {
    readonly heapsize: number;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly heapmask: RefMask | undefined; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(heapsize: number, inlinedatasize: number, assigndatasize: number, heapmask: RefMask | undefined, inlinedmask: RefMask) {
        this.heapsize = heapsize;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;
        this.heapmask = heapmask;
        this.inlinedmask = inlinedmask;
    }

    isScalarOnlyInline(): boolean {
        return /1+/.test(this.inlinedmask);
    }

    static createByRegisterSizeInfo(inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(inlinedatasize, inlinedatasize, assigndatasize, undefined, inlinedmask);
    }

    static createByValueSizeInfo(inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask);
    }

    static createByRefSizeInfo(heapsize: number, heapmask: RefMask | undefined): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(heapsize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, heapmask, "2");
    }

    jemit(): any {
        return {heapsize: this.heapsize, inlinedatasize: this.inlinedatasize, assigndatasize: this.assigndatasize, heapmask: this.heapmask || null, inlinedmask: this.inlinedmask};
    }
}

enum LayoutCategory {
    Inline = 0x0,
    Ref,
    UnionRef,
    UnionInline,
    UnionUniversal
}

class ICPPLayoutInfo {
    readonly tkey: MIRResolvedTypeKey;
    readonly allocinfo: ICPPTypeSizeInfo;
    readonly layout: LayoutCategory;

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, layout: LayoutCategory) {
        this.tkey = tkey;
        this.allocinfo = allocinfo;
        this.layout = layout;
    }
}

class ICPPLayoutInfoFixed extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, layout: LayoutCategory) {
        super(tkey, allocinfo, layout);
    }
}

class ICPPTupleLayoutInfo extends ICPPLayoutInfo {
    readonly maxIndex: number;
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[], layout: LayoutCategory) {
        super(tkey, allocinfo, layout);

        this.maxIndex = idxtypes.length;
        this.ttypes = idxtypes;
        this.idxoffsets = idxoffsets;
    }

    static createByValueTuple(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTupleLayoutInfo {
        return new ICPPTupleLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(inlinedatasize, inlinedmask), idxtypes, idxoffsets, LayoutCategory.Inline);
    }

    static createByRefTuple(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTupleLayoutInfo {
        return new ICPPTupleLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(heapsize, heapmask), idxtypes, idxoffsets, LayoutCategory.Ref);
    }
}

class ICPPRecordLayoutInfo extends ICPPLayoutInfo {
    readonly propertynames: string[];
    readonly propertytypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[], layout: LayoutCategory) {
        super(tkey, allocinfo, layout);

        this.propertynames = propertynames;
        this.propertytypes = propertytypes;
        this.propertyoffsets = propertyoffsets;
    }

    static createByValueRecord(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPRecordLayoutInfo {
        return new ICPPRecordLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(inlinedatasize, inlinedmask), propertynames, propertytypes, propertyoffsets, LayoutCategory.Inline);
    }

    static createByRefRecord(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPRecordLayoutInfo {
        return new ICPPRecordLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(heapsize, heapmask), propertynames, propertytypes, propertyoffsets, LayoutCategory.Ref);
    }
}

class ICPPEntityLayoutInfo extends ICPPLayoutInfo {
    readonly fieldnames: MIRFieldKey[];
    readonly fieldtypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[], layout: LayoutCategory) {
        super(tkey, allocinfo, layout);

        this.fieldnames = fieldnames;
        this.fieldtypes = fieldtypes;
        this.fieldoffsets = fieldoffsets;
    }

    static createByValueEntity(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPEntityLayoutInfo {
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(inlinedatasize, inlinedmask), fieldnames, fieldtypes, fieldoffsets, LayoutCategory.Inline);
    }

    static createByRefEntity(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPEntityLayoutInfo {
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets, LayoutCategory.Ref);
    }
}

class ICPPEphemeralListLayoutInfo extends ICPPLayoutInfo {
    readonly etypes: MIRResolvedTypeKey[];
    readonly eoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, etypes: MIRResolvedTypeKey[], eoffsets: number[]) {
        super(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(inlinedatasize, inlinedmask), LayoutCategory.Inline);

        this.etypes = etypes;
        this.eoffsets = eoffsets;
    }
}

class ICPPLayoutRefUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey) {
        super(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(0, "2"), LayoutCategory.UnionRef);
    }
}

class ICPPLayoutInlineUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, iskey: boolean) {
        super(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(inlinedatasize, inlinedmask), LayoutCategory.UnionInline);
    }
}

class ICPPLayoutUniversalUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey) {
        super(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(UNIVERSAL_TOTAL_SIZE, "51111"), LayoutCategory.UnionUniversal);
    }
}

class ICPPFunctionParameter {
    readonly name: string;
    readonly ptype: MIRResolvedTypeKey;

    constructor(name: string, ptype: MIRResolvedTypeKey) {
        this.name = name;
        this.ptype = ptype;
    }

    jsonEmit(): object {
        return {name: this.name, ptype: this.ptype};
    }
}

class ICPPInvokeDecl {
    readonly name: string;
    readonly ikey: MIRInvokeKey;

    readonly srcFile: string;
    readonly sinfo: SourceInfo;
    
    readonly recursive: boolean;

    readonly params: ICPPFunctionParameter[];
    readonly resultType: MIRResolvedTypeKey;

    readonly scalarStackBytes: number;
    readonly mixedStackBytes: number;
    readonly mixedStackMask: RefMask;

    readonly maskSlots: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: MIRResolvedTypeKey, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number) {
        this.name = name;
        this.ikey = ikey;
        this.srcFile = srcFile;
        this.sinfo = sinfo;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;

        this.scalarStackBytes = scalarStackBytes;
        this.mixedStackBytes = mixedStackBytes;
        this.mixedStackMask = mixedStackMask;

        this.maskSlots = maskSlots;
    }

    jsonEmit(): object {
        return {name: this.name, ikey: this.ikey, srcFile: this.srcFile, sinfo: this.sinfo, recursive: this.recursive, params: this.params.map((param) => param.jsonEmit()), resultType: this.resultType, scalarStackBytes: this.scalarStackBytes, mixedStackBytes: this.mixedStackBytes, mixedStackMask: this.mixedStackMask, maskSlots: this.maskSlots};
    }
}

class ICPPInvokeBodyDecl extends ICPPInvokeDecl 
{
    readonly body: ICPPOp[];
    readonly resultArg: Argument;
    readonly argmaskSize: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: MIRResolvedTypeKey, resultArg: Argument, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, body: ICPPOp[], argmaskSize: number) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.body = body;
        this.resultArg = resultArg;
        this.argmaskSize = argmaskSize;
    }

    jsonEmit(): object {
        return {...super.jsonEmit(), isbuiltin: false, resultArg: this.resultArg, body: this.body, argmaskSize: this.argmaskSize};
    }
}

class ICPPInvokePrimitiveDecl extends ICPPInvokeDecl 
{
    readonly enclosingtype: string | undefined;
    readonly implkeyname: string;
    readonly scalaroffsetMap: Map<string, [number, MIRResolvedTypeKey]>;
    readonly mixedoffsetMap: Map<string, [number, MIRResolvedTypeKey]>;
    readonly binds: Map<string, MIRResolvedTypeKey>;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: MIRResolvedTypeKey, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, enclosingtype: string | undefined, implkeyname: string, scalaroffsetMap: Map<string, [number, MIRResolvedTypeKey]>, mixedoffsetMap: Map<string, [number, MIRResolvedTypeKey]>, binds: Map<string, MIRResolvedTypeKey>) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.enclosingtype = enclosingtype;
        this.implkeyname = implkeyname;
        this.scalaroffsetMap = scalaroffsetMap;
        this.mixedoffsetMap = mixedoffsetMap;
        this.binds = binds;
    }

    jsonEmit(): object {
        const soffsets = [...this.scalaroffsetMap].map((v) => {
            return {name: v[0], info: v[1]};
        });

        const moffsets = [...this.mixedoffsetMap].map((v) => {
            return {name: v[0], info: v[1]};
        });

        const binds = [...this.binds].map((v) => {
            return {name: v[0], ttype: v[1]};
        });

        return {...super.jsonEmit(), isbuiltin: true, enclosingtype: this.enclosingtype, implkeyname: this.implkeyname, scalaroffsetMap: soffsets, mixedoffsetMap: moffsets, binds: binds};
    }
}

class ICPPConstDecl 
{
    readonly gkey: MIRGlobalKey;
    readonly optenumname: [MIRResolvedTypeKey, string] | undefined;
    readonly storageOffset: number;
    readonly valueInvoke: MIRInvokeKey;
    readonly ctype: MIRResolvedTypeKey;

    constructor(gkey: MIRGlobalKey, optenumname: [MIRResolvedTypeKey, string] | undefined, storageOffset: number, valueInvoke: MIRInvokeKey, ctype: MIRResolvedTypeKey) {
        this.gkey = gkey;
        this.optenumname = optenumname;
        this.storageOffset = storageOffset;
        this.valueInvoke = valueInvoke;
        this.ctype = ctype;
    }

    jsonEmit(): object {
        return { storageOffset: this.storageOffset, valueInvoke: this.valueInvoke, ctype: this.ctype };
    }
}

class ICPPAssembly
{
    readonly typecount: number;
    cbuffsize: number = 0;
    cmask: RefMask = "";

    readonly typenames: MIRResolvedTypeKey[];
    readonly propertynames: string[];
    readonly fieldnames: MIRFieldKey[];

    readonly invokenames: MIRInvokeKey[];
    readonly vinvokenames: MIRVirtualMethodKey[];

    vtable: {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]}[] = [];
    subtypes: Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>> = new Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>>();

    typedecls: ICPPType[] = [];
    invdecls: ICPPInvokeDecl[] = [];

    litdecls: { offset: number, storage: ICPPType, value: string }[] = [];
    constdecls: ICPPConstDecl[] = [];

    readonly entrypoint: MIRInvokeKey;

    constructor(typecount: number, typenames: MIRResolvedTypeKey[], propertynames: string[], fieldnames: MIRFieldKey[], invokenames: MIRInvokeKey[], vinvokenames: MIRVirtualMethodKey[], entrypoint: MIRInvokeKey) {
        this.typecount = typecount;

        this.typenames = typenames;
        this.propertynames = propertynames;
        this.fieldnames = fieldnames;

        this.invokenames = invokenames;
        this.vinvokenames = vinvokenames;

        this.entrypoint = entrypoint;
    }

    jsonEmit(): object {
        return {
            typecount: this.typecount,
            cbuffsize: this.cbuffsize,
            cmask: this.cmask,

            typenames: this.typenames.sort(),
            propertynames: this.propertynames.sort(),
            fieldnames: this.fieldnames.sort(),

            invokenames: this.invokenames.sort(),
            vinvokenames: this.vinvokenames.sort(),

            vtable: this.vtable.sort((a, b) => a.oftype.localeCompare(b.oftype)),

            typedecls: this.typedecls.sort((a, b) => a.tkey.localeCompare(b.tkey)).map((tdecl) => {
                const vtbl = this.vtable.find((vte) => vte.oftype === tdecl.tkey) as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]};

                if(tdecl instanceof ICPPTypeRegister) {
                    return tdecl.jemitRegister(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeTuple) {
                    return tdecl.jemitTupleType(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeRecord) {
                    return tdecl.jemitRecord(vtbl.vtable);
                }
                else if (tdecl instanceof ICPPTypeEphemeralList) {
                    return tdecl.jemitEphemeralList();
                }
                else if(tdecl instanceof ICPPTypeInlineUnion) {
                    return tdecl.jemitInlineUnion([...(this.subtypes.get(tdecl.tkey) as Set<MIRResolvedTypeKey>)].sort());
                }
                else if (tdecl instanceof ICPPTypeRefUnion) {
                    return tdecl.jemitRefUnion([...(this.subtypes.get(tdecl.tkey) as Set<MIRResolvedTypeKey>)].sort());
                }
                else {
                    const edecl = tdecl as ICPPTypeEntity;

                    switch(edecl.ptag) {
                        case ICPPParseTag.ValidatorTag: {
                            return edecl.jemitValidator((edecl.extradata as BSQRegex).jemit());
                        }
                        case ICPPParseTag.StringOfTag: {
                            return edecl.jemitStringOf(edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.DataStringTag: {
                            return edecl.jemitDataString(edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.TypedNumberTag: {
                            //
                            //TODO: we need to switch this to encode the underlying and primitive types in the type decl really -- not as
                            //         the funky v field -- we probably want to add some extra access (and maybe constructor) magic too 
                            //
                            return edecl.jemitTypedNumber(edecl.extradata as MIRResolvedTypeKey, edecl.extradata as MIRResolvedTypeKey);
                        }
                        case ICPPParseTag.EnumTag: {
                            const ddcls = this.constdecls.filter((cdcl) => cdcl.optenumname !== undefined && cdcl.optenumname[0] === tdecl.tkey);
                            const enuminvs = ddcls.map((ddcl) => [`${(ddcl.optenumname as [string, string])[0]}::${(ddcl.optenumname as [string, string])[1]}`, ddcl.storageOffset] as [string, number]);
                            return edecl.jemitEnum(edecl.extradata as MIRResolvedTypeKey, enuminvs);
                        }
                        case ICPPParseTag.VectorTag: {
                            const sdata = edecl.extradata as ICPPTypeSizeInfoSimple;
                            return edecl.jemitVector(sdata.tkey, sdata.inlinedatasize, sdata.inlinedmask);
                        }
                        case ICPPParseTag.ListTag: {
                            const sdata = edecl.extradata as ICPPTypeSizeInfoSimple;
                            return edecl.jemitList(sdata.tkey, sdata.inlinedatasize, sdata.inlinedmask);
                        }
                        case ICPPParseTag.StackTag: {
                            const sdata = edecl.extradata as ICPPTypeSizeInfoSimple;
                            return edecl.jemitStack(sdata.tkey, sdata.inlinedatasize, sdata.inlinedmask);
                        }
                        case ICPPParseTag.QueueTag: {
                            const sdata = edecl.extradata as ICPPTypeSizeInfoSimple;
                            return edecl.jemitQueue(sdata.tkey, sdata.inlinedatasize, sdata.inlinedmask);
                        }
                        case ICPPParseTag.SetTag: {
                            const sdata = edecl.extradata as ICPPTypeSizeInfoSimple;
                            return edecl.jemitSet(sdata.tkey, sdata.inlinedatasize, sdata.inlinedmask);
                        }
                        case ICPPParseTag.MapTag: {
                            const keysdata = edecl.extradata[0] as ICPPTypeSizeInfoSimple;
                            const valsdata = edecl.extradata[1] as ICPPTypeSizeInfoSimple;
                            return edecl.jemitMap(keysdata.tkey, keysdata.inlinedatasize, keysdata.inlinedmask, valsdata.tkey, valsdata.inlinedatasize, valsdata.inlinedmask);
                        }
                        default:
                            return edecl.jemitEntity(vtbl.vtable);
                    }
                }
            }),

            invdecls: this.invdecls.sort((a, b) => a.ikey.localeCompare(b.ikey)).map((inv) => inv.jsonEmit()),

            litdecls: this.litdecls.sort((a, b) => a.value.localeCompare(b.value)).map((lv) => {
                return {offset: lv.offset, storage: lv.storage.tkey, value: lv.value};
            }),

            constdecls: this.constdecls.sort((a, b) => a.gkey.localeCompare(b.gkey)).map((cd) => cd.jsonEmit()),

            entrypoint: this.entrypoint
        };
    }
}

export {
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_CONTENT_SIZE, UNIVERSAL_TOTAL_SIZE,
    ICPPTypeSizeInfoSimple, ICPPTypeSizeInfo, RefMask,
    ICPPLayoutInfo, ICPPLayoutInfoFixed, ICPPTupleLayoutInfo, ICPPRecordLayoutInfo, ICPPEntityLayoutInfo, ICPPEphemeralListLayoutInfo, 
    ICPPLayoutInlineUnion, ICPPLayoutRefUnion, ICPPLayoutUniversalUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl,
    ICPPConstDecl,
    ICPPAssembly
};

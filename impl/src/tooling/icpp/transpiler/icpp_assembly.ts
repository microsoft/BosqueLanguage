//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { Argument, ICPPOp, ParameterInfo, TargetVar } from "./icpp_exp";

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
const UNIVERSAL_MASK = "51111";

type RefMask = string;

class ICPPTypeSizeInfoSimple {
    readonly tkey: MIRResolvedTypeKey;

    readonly isinlinevalue: boolean; //if this value is represented by an inline value (otherwise by a pointer to a heap allocated value)
    readonly issmallinlinevalue: boolean; //if this value is represented by a small inline value (which can be inlined itself) 
    
    readonly realdatasize: number; //number of bytes needed in storage location for this (EXCLUDES type tag for inline union)
    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(tkey: MIRResolvedTypeKey, realdatasize: number, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask, isinlinevalue: boolean, issmallinlinevalue: boolean) {
        this.tkey = tkey;
        this.isinlinevalue = isinlinevalue;
        this.issmallinlinevalue = issmallinlinevalue;

        this.realdatasize = realdatasize;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;

        this.inlinedmask = inlinedmask;
    }

    isScalarOnlyInline(): boolean {
        return /^1+$/.test(this.inlinedmask);
    }

    static createByRegisterSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, inlinedatasize, inlinedatasize, assigndatasize, inlinedmask, true, true);
    }

    static createByValueSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, issmallinlinevalue: boolean): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, inlinedatasize, inlinedatasize, inlinedatasize, inlinedmask, true, issmallinlinevalue);
    }

    static createByRefSizeInfo(tkey: MIRResolvedTypeKey): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, ICPP_WORD_SIZE, ICPP_WORD_SIZE, ICPP_WORD_SIZE, "2", false, false);
    }

    static createInlineUnionSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, inlinedatasize - ICPP_WORD_SIZE, inlinedatasize, inlinedatasize, inlinedmask, true, false);
    }

    createFromSizeInfo(tkey: MIRResolvedTypeKey): ICPPTypeSizeInfoSimple {
        return new ICPPTypeSizeInfoSimple(tkey, this.inlinedatasize, this.inlinedatasize, this.assigndatasize, this.inlinedmask, this.isinlinevalue, this.issmallinlinevalue);
    }
}

class ICPPTypeSizeInfo {
    readonly tkey: MIRResolvedTypeKey;

    readonly isinlinevalue: boolean; //if this value is represented by an inline value (otherwise by a pointer to a heap allocated value)
    readonly issmallinlinevalue: boolean; //if this value is represented by a small inline value (which can be inlined itself) 
    
    readonly realdatasize: number; //number of bytes needed in storage location for this (EXCLUDES type tag for inline union)
    readonly heapsize: number;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly heapmask: RefMask | undefined; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(tkey: MIRResolvedTypeKey, realdatasize: number, heapsize: number, inlinedatasize: number, assigndatasize: number, heapmask: RefMask | undefined, inlinedmask: RefMask, isinlinevalue: boolean, issmallinlinevalue: boolean)
    {
        this.tkey = tkey;
        this.isinlinevalue = isinlinevalue;
        this.issmallinlinevalue = issmallinlinevalue;

        this.realdatasize = realdatasize;
        this.heapsize = heapsize;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;

        this.heapmask = heapmask;
        this.inlinedmask = inlinedmask;
    }

    static isScalarOnlyMask(mask: RefMask): boolean {
        return /1+/.test(mask);
    }

    static createByRegisterSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize, inlinedatasize, inlinedatasize, assigndatasize, undefined, inlinedmask, true, true);
    }

    static createByValueSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, issmallinlinevalue: boolean): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize, inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask, true, issmallinlinevalue);
    }

    static createByRefSizeInfo(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask | undefined): ICPPTypeSizeInfo {
        if(heapmask !== undefined && ICPPTypeSizeInfo.isScalarOnlyMask(heapmask)) {
            heapmask = undefined;
        }
        
        return new ICPPTypeSizeInfo(tkey, ICPP_WORD_SIZE, heapsize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, heapmask, "2", false, false);
    }

    static createInlineUnionSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize - ICPP_WORD_SIZE, inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask, true, false);
    }

    createFromSizeInfo(tkey: MIRResolvedTypeKey): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, this.inlinedatasize, this.heapsize, this.inlinedatasize, this.assigndatasize, this.heapmask, this.inlinedmask, this.isinlinevalue, this.issmallinlinevalue);
    }

    jemit(): any {
        return {realdatasize: this.realdatasize, heapsize: this.heapsize, inlinedatasize: this.inlinedatasize, assigndatasize: this.assigndatasize, heapmask: this.heapmask || null, inlinedmask: this.inlinedmask};
    }
}

enum ICPPLayoutCategory {
    Inline = 0x0,
    Ref,
    UnionRef,
    UnionInline,
    UnionUniversal
}

abstract class ICPPLayoutInfo {
    readonly tkey: MIRResolvedTypeKey;
    readonly allocinfo: ICPPTypeSizeInfo;
    readonly layout: ICPPLayoutCategory;

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, layout: ICPPLayoutCategory) {
        this.tkey = tkey;
        this.allocinfo = allocinfo;
        this.layout = layout;
    }

    abstract createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo;

    canScalarStackAllocate(): boolean {
        if(this.layout === ICPPLayoutCategory.Inline) {
            return /1+/.test(this.allocinfo.inlinedmask);
        }
        else if(this.layout === ICPPLayoutCategory.UnionInline) {
            return /51+/.test(this.allocinfo.inlinedmask);
        }
        else {
            return false;
        }
    }
}

class ICPPLayoutInfoFixed extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, layout: ICPPLayoutCategory) {
        super(tkey, allocinfo, layout);
    }

    static createByRegisterLayout(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPLayoutInfoFixed {
        return new ICPPLayoutInfoFixed(tkey, ICPPTypeSizeInfo.createByRegisterSizeInfo(tkey, inlinedatasize, assigndatasize, inlinedmask), ICPPLayoutCategory.Inline);
    }

    static createByValueLayout(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, issmallinlinevalue: boolean): ICPPLayoutInfoFixed {
        return new ICPPLayoutInfoFixed(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask, issmallinlinevalue), ICPPLayoutCategory.Inline);
    }

    static createByRefLayout(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask | undefined): ICPPLayoutInfoFixed {
        return new ICPPLayoutInfoFixed(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, heapsize, heapmask), ICPPLayoutCategory.Ref);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPTupleLayoutInfo extends ICPPLayoutInfo {
    readonly maxIndex: number;
    readonly ttypes: MIRResolvedTypeKey[];
    readonly idxoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[], layout: ICPPLayoutCategory) {
        super(tkey, allocinfo, layout);

        this.maxIndex = idxtypes.length;
        this.ttypes = idxtypes;
        this.idxoffsets = idxoffsets;
    }

    static createByValueTuple(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTupleLayoutInfo {
        return new ICPPTupleLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask, false), idxtypes, idxoffsets, ICPPLayoutCategory.Inline);
    }

    static createByRefTuple(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, idxtypes: MIRResolvedTypeKey[], idxoffsets: number[]): ICPPTupleLayoutInfo {
        return new ICPPTupleLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, heapsize, heapmask), idxtypes, idxoffsets, ICPPLayoutCategory.Ref);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPRecordLayoutInfo extends ICPPLayoutInfo {
    readonly propertynames: string[];
    readonly propertytypes: MIRResolvedTypeKey[];
    readonly propertyoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[], layout: ICPPLayoutCategory) {
        super(tkey, allocinfo, layout);

        this.propertynames = propertynames;
        this.propertytypes = propertytypes;
        this.propertyoffsets = propertyoffsets;
    }

    static createByValueRecord(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPRecordLayoutInfo {
        return new ICPPRecordLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask, false), propertynames, propertytypes, propertyoffsets, ICPPLayoutCategory.Inline);
    }

    static createByRefRecord(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, propertynames: string[], propertytypes: MIRResolvedTypeKey[], propertyoffsets: number[]): ICPPRecordLayoutInfo {
        return new ICPPRecordLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, heapsize, heapmask), propertynames, propertytypes, propertyoffsets, ICPPLayoutCategory.Ref);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPEntityLayoutInfo extends ICPPLayoutInfo {
    readonly fieldnames: MIRFieldKey[];
    readonly fieldtypes: MIRResolvedTypeKey[];
    readonly fieldoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[], layout: ICPPLayoutCategory) {
        super(tkey, allocinfo, layout);

        this.fieldnames = fieldnames;
        this.fieldtypes = fieldtypes;
        this.fieldoffsets = fieldoffsets;
    }

    static createByValueEntity(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPEntityLayoutInfo {
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask, false), fieldnames, fieldtypes, fieldoffsets, ICPPLayoutCategory.Inline);
    }

    static createByRefEntity(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPEntityLayoutInfo {
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets, ICPPLayoutCategory.Ref);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPEphemeralListLayoutInfo extends ICPPLayoutInfo {
    readonly etypes: MIRResolvedTypeKey[];
    readonly eoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, etypes: MIRResolvedTypeKey[], eoffsets: number[]) {
        super(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask, false), ICPPLayoutCategory.Inline);

        this.etypes = etypes;
        this.eoffsets = eoffsets;
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPLayoutRefUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey) {
        super(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, 0, "2"), ICPPLayoutCategory.UnionRef);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), ICPPLayoutCategory.Ref);
    }
}

class ICPPLayoutInlineUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask) {
        super(tkey, ICPPTypeSizeInfo.createInlineUnionSizeInfo(tkey, inlinedatasize, inlinedmask), ICPPLayoutCategory.UnionInline);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), ICPPLayoutCategory.Inline);
    }
}

class ICPPLayoutUniversalUnion extends ICPPLayoutInfo {
    constructor(tkey: MIRResolvedTypeKey) {
        super(tkey, ICPPTypeSizeInfo.createInlineUnionSizeInfo(tkey, UNIVERSAL_TOTAL_SIZE, UNIVERSAL_MASK), ICPPLayoutCategory.UnionUniversal);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), ICPPLayoutCategory.Inline);
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

class ICPPInvokeBodyDecl extends ICPPInvokeDecl {
    readonly body: ICPPOp[];
    readonly paraminfo: ParameterInfo[];
    readonly resultArg: Argument;
    readonly argmaskSize: number;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], paraminfo: ParameterInfo[], resultType: MIRResolvedTypeKey, resultArg: Argument, scalarStackBytes: number, mixedStackBytes: number, mixedStackMask: RefMask, maskSlots: number, body: ICPPOp[], argmaskSize: number) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, scalarStackBytes, mixedStackBytes, mixedStackMask, maskSlots);
        this.body = body;
        this.paraminfo = paraminfo;
        this.resultArg = resultArg;
        this.argmaskSize = argmaskSize;
    }

    jsonEmit(): object {
        return {...super.jsonEmit(), isbuiltin: false, paraminfo: this.paraminfo, resultArg: this.resultArg, body: this.body, argmaskSize: this.argmaskSize};
    }
}

class ICPPInvokePrimitiveDecl extends ICPPInvokeDecl {
    readonly enclosingtype: string | undefined;
    readonly implkeyname: string;
    readonly binds: Map<string, MIRResolvedTypeKey>;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: MIRResolvedTypeKey, enclosingtype: string | undefined, implkeyname: string, binds: Map<string, MIRResolvedTypeKey>) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, 0, 0, "", 0);
        this.enclosingtype = enclosingtype;
        this.implkeyname = implkeyname;
        this.binds = binds;
    }

    jsonEmit(): object {
        const binds = [...this.binds].map((v) => {
            return {name: v[0], ttype: v[1]};
        });

        return {...super.jsonEmit(), isbuiltin: true, enclosingtype: this.enclosingtype, implkeyname: this.implkeyname, binds: binds};
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
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_CONTENT_SIZE, UNIVERSAL_TOTAL_SIZE, UNIVERSAL_MASK,
    ICPPTypeSizeInfoSimple, ICPPTypeSizeInfo, RefMask,
    ICPPLayoutCategory, ICPPLayoutInfo, ICPPLayoutInfoFixed, ICPPTupleLayoutInfo, ICPPRecordLayoutInfo, ICPPEntityLayoutInfo, ICPPEphemeralListLayoutInfo, 
    ICPPLayoutInlineUnion, ICPPLayoutRefUnion, ICPPLayoutUniversalUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl,
    ICPPConstDecl,
    ICPPAssembly
};

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptTypeDecl, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREnumEntityTypeDecl, MIREphemeralListType, MIRFieldDecl, MIRObjectEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRGlobalKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { ICPPParseTag } from "./icppdecls_emitter";
import { Argument, ICPPOp, ParameterInfo } from "./icpp_exp";

import * as assert from "assert";

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

class ICPPTypeSizeInfo {
    readonly tkey: MIRResolvedTypeKey;

    readonly isinlinevalue: boolean; //if this value is represented by an inline value (otherwise by a pointer to a heap allocated value)
    
    readonly realdatasize: number; //number of bytes needed in storage location for this (EXCLUDES type tag for inline union)
    readonly heapsize: number;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    readonly inlinedatasize: number; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    readonly assigndatasize: number; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    readonly heapmask: RefMask | undefined; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    readonly inlinedmask: RefMask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object

    constructor(tkey: MIRResolvedTypeKey, realdatasize: number, heapsize: number, inlinedatasize: number, assigndatasize: number, heapmask: RefMask | undefined, inlinedmask: RefMask, isinlinevalue: boolean)
    {
        this.tkey = tkey;
        this.isinlinevalue = isinlinevalue;

        this.realdatasize = realdatasize;
        this.heapsize = heapsize;
        this.inlinedatasize = inlinedatasize;
        this.assigndatasize = assigndatasize;

        this.heapmask = heapmask;
        this.inlinedmask = inlinedmask;
    }

    static isScalarOnlyMask(mask: RefMask): boolean {
        return /^1+$/.test(mask);
    }

    static createByRegisterSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, assigndatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize, inlinedatasize, inlinedatasize, assigndatasize, undefined, inlinedmask, true);
    }

    static createByValueSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize, inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask, true);
    }

    static createByRefSizeInfo(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask | undefined): ICPPTypeSizeInfo {
        if(heapmask !== undefined && ICPPTypeSizeInfo.isScalarOnlyMask(heapmask)) {
            heapmask = undefined;
        }
        
        return new ICPPTypeSizeInfo(tkey, ICPP_WORD_SIZE, heapsize, ICPP_WORD_SIZE, ICPP_WORD_SIZE, heapmask, "2", false);
    }

    static createInlineUnionSizeInfo(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, inlinedatasize - ICPP_WORD_SIZE, inlinedatasize, inlinedatasize, inlinedatasize, undefined, inlinedmask, true);
    }

    createFromSizeInfo(tkey: MIRResolvedTypeKey): ICPPTypeSizeInfo {
        return new ICPPTypeSizeInfo(tkey, this.inlinedatasize, this.heapsize, this.inlinedatasize, this.assigndatasize, this.heapmask, this.inlinedmask, this.isinlinevalue);
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
            return /^1+$/.test(this.allocinfo.inlinedmask);
        }
        else if(this.layout === ICPPLayoutCategory.UnionInline) {
            return /^51+$/.test(this.allocinfo.inlinedmask);
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

    static createByValueLayout(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask): ICPPLayoutInfoFixed {
        return new ICPPLayoutInfoFixed(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask), ICPPLayoutCategory.Inline);
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
        return new ICPPTupleLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask), idxtypes, idxoffsets, ICPPLayoutCategory.Inline);
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
        return new ICPPRecordLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask), propertynames, propertytypes, propertyoffsets, ICPPLayoutCategory.Inline);
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
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask), fieldnames, fieldtypes, fieldoffsets, ICPPLayoutCategory.Inline);
    }

    static createByRefEntity(tkey: MIRResolvedTypeKey, heapsize: number, heapmask: RefMask, fieldnames: string[], fieldtypes: MIRResolvedTypeKey[], fieldoffsets: number[]): ICPPEntityLayoutInfo {
        return new ICPPEntityLayoutInfo(tkey, ICPPTypeSizeInfo.createByRefSizeInfo(tkey, heapsize, heapmask), fieldnames, fieldtypes, fieldoffsets, ICPPLayoutCategory.Ref);
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPCollectionInternalsLayoutInfo extends ICPPLayoutInfo {
    readonly xinfo: {name: string, type: MIRResolvedTypeKey, size: number, offset: number}[];

    constructor(tkey: MIRResolvedTypeKey, allocinfo: ICPPTypeSizeInfo, xinfo: {name: string, type: MIRResolvedTypeKey, size: number, offset: number}[]) {
        super(tkey, allocinfo, ICPPLayoutCategory.Ref);

        this.xinfo = xinfo;
    }

    createFromLayoutInfo(tkey: MIRResolvedTypeKey): ICPPLayoutInfo {
        return new ICPPLayoutInfoFixed(tkey, this.allocinfo.createFromSizeInfo(tkey), this.layout);
    }
}

class ICPPEphemeralListLayoutInfo extends ICPPLayoutInfo {
    readonly etypes: MIRResolvedTypeKey[];
    readonly eoffsets: number[];

    constructor(tkey: MIRResolvedTypeKey, inlinedatasize: number, inlinedmask: RefMask, etypes: MIRResolvedTypeKey[], eoffsets: number[]) {
        super(tkey, ICPPTypeSizeInfo.createByValueSizeInfo(tkey, inlinedatasize, inlinedmask), ICPPLayoutCategory.Inline);

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

class ICPPPCode
{
    readonly code: MIRInvokeKey;
    readonly ctypes: MIRResolvedTypeKey[];
    readonly cargpos: number[];

    constructor(code: MIRInvokeKey, ctypes: MIRResolvedTypeKey[], cargpos: number[]) {
        this.code = code;
        this.ctypes = ctypes;
        this.cargpos = cargpos;
    }

    jsonEmit(): object {
        return {code: this.code, ctypes: this.ctypes, cargs: this.cargpos};
    }
}

class ICPPInvokePrimitiveDecl extends ICPPInvokeDecl {
    readonly enclosingtype: string | undefined;
    readonly implkeyname: string;
    readonly binds: Map<string, MIRResolvedTypeKey>;
    readonly pcodes: Map<string, ICPPPCode>;

    constructor(name: string, ikey: MIRInvokeKey, srcFile: string, sinfo: SourceInfo, recursive: boolean, params: ICPPFunctionParameter[], resultType: MIRResolvedTypeKey, enclosingtype: string | undefined, implkeyname: string, binds: Map<string, MIRResolvedTypeKey>, pcodes: Map<string, ICPPPCode>) {
        super(name, ikey, srcFile, sinfo, recursive, params, resultType, 0, 0, "", 0);
        this.enclosingtype = enclosingtype;
        this.implkeyname = implkeyname;
        this.binds = binds;
        this.pcodes = pcodes;
    }

    jsonEmit(): object {
        const binds = [...this.binds].map((v) => {
            return {name: v[0], ttype: v[1]};
        });

        const pcodes = [...this.pcodes].map((v) => {
            return {name: v[0], pc: v[1].jsonEmit()};
        });

        return {...super.jsonEmit(), isbuiltin: true, enclosingtype: this.enclosingtype, implkeyname: this.implkeyname, binds: binds, pcodes: pcodes};
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
    cbuffsize: number = 0;
    cmask: RefMask = "";

    readonly typenames: MIRResolvedTypeKey[];
    readonly propertynames: string[];
    readonly fields: MIRFieldDecl[];

    invokenames: Set<MIRInvokeKey>;
    vinvokenames: Set<MIRVirtualMethodKey>;

    vtable: {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]}[] = [];
    subtypes: Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>> = new Map<MIRResolvedTypeKey, Set<MIRResolvedTypeKey>>();

    typedecls: ICPPLayoutInfo[] = [];
    invdecls: ICPPInvokeDecl[] = [];

    litdecls: { offset: number, storage: ICPPTypeSizeInfo, value: string }[] = [];
    constdecls: ICPPConstDecl[] = [];

    constructor(typenames: MIRResolvedTypeKey[], propertynames: string[], fields: MIRFieldDecl[], invokenames: MIRInvokeKey[], vinvokenames: MIRVirtualMethodKey[]) {
        this.typenames = typenames;
        this.propertynames = propertynames;
        this.fields = fields;

        this.invokenames = new Set<MIRInvokeKey>(invokenames);
        this.vinvokenames = new Set<MIRVirtualMethodKey>(vinvokenames);
    }

    private generateBoxedTypeName(tkey: MIRResolvedTypeKey): string {
        return tkey + "@boxed";
    }
    
    private processStringOfEntityDecl(edecl: MIRStringOfInternalEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.StringOfTag,
            tkey: icpptype.tkey,
            name: edecl.tkey
        };
    }
            
    private processDataStringStringOfEntityDecl(edecl: MIRDataStringInternalEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.DataStringTag,
            tkey: icpptype.tkey,
            name: edecl.tkey
        };
    }
            
    private processDataBufferStringOfEntityDecl(edecl: MIRDataBufferInternalEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.DataBufferTag,
            tkey: icpptype.tkey,
            name: edecl.tkey
        };
    }

    private processConstructableEntityDecl(edecl: MIRConstructableEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.EntityDeclOfTag,
            tkey: icpptype.tkey,
            name: edecl.tkey,
            oftype: edecl.fromtype
        };
    }
    
    private processEnumEntityDecl(edecl: MIREnumEntityTypeDecl, icpptype: ICPPLayoutInfo): object  {
        const enumnames = edecl.enums.map((en) => edecl.tkey + "::" + en);

        return {
            ptag: ICPPParseTag.EnumTag,
            tkey: icpptype.tkey,
            name: edecl.tkey,
            enumnames: enumnames
        };
    }

    private processConstructableInternalEntityDecl(edecl: MIRConstructableInternalEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        if(icpptype.layout === ICPPLayoutCategory.Ref) {
            return {
                ptag: ICPPParseTag.EntityConstructableRefTag,
                tkey: icpptype.tkey,
                name: edecl.tkey,
                allocinfo: icpptype.allocinfo.jemit(),
                oftype: edecl.fromtype
            };
        }
        else {
            return {
                ptag: ICPPParseTag.EntityConstructableStructTag,
                tkey: icpptype.tkey,
                name: edecl.tkey,
                allocinfo: icpptype.allocinfo.jemit(),
                oftype: edecl.fromtype,
                norefs: icpptype.canScalarStackAllocate(),
                boxedtype: this.generateBoxedTypeName(icpptype.tkey)
            };
        }
    }

    private processPrimitiveListEntityDecl(edecl: MIRPrimitiveListEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.ListTag,
            tkey: icpptype.tkey,
            name: edecl.tkey,
            etype: edecl.getTypeT().typeID
        };
    }

    private processPrimitiveStackEntityDecl(edecl: MIRPrimitiveStackEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        assert(false, "MIRPrimitiveStackEntityTypeDecl");
        return {};
    }

    private processPrimitiveQueueEntityDecl(edecl: MIRPrimitiveQueueEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        assert(false, "MIRPrimitiveQueueEntityTypeDecl");
        return {};
    }

    private processPrimitiveSetEntityDecl(edecl: MIRPrimitiveSetEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        assert(false, "MIRPrimitiveSetEntityTypeDecl");
        return {};
    }

    private processPrimitiveMapEntityDecl(edecl: MIRPrimitiveMapEntityTypeDecl, icpptype: ICPPLayoutInfo): object {
        return {
            ptag: ICPPParseTag.ListTag,
            tkey: icpptype.tkey,
            name: edecl.tkey,
            ktype: edecl.getTypeK(),
            vtype: edecl.getTypeV(),
            etype: edecl.tupentrytype
        };
    }

    private processPartialVector4EntityDecl(edecl: MIRPrimitiveInternalEntityTypeDecl, icpptype: ICPPCollectionInternalsLayoutInfo): object {
        const etype = edecl.terms.get("T") as MIRType;

        return {
            ptag: ICPPParseTag.PartialVector4Tag,
            tkey: edecl.tkey,
            name: edecl.tkey,
            heapsize: icpptype.allocinfo.heapsize,
            heapmask: icpptype.allocinfo.heapmask,
            etype: etype.typeID,
            esize: icpptype.xinfo[0].size
        };
    }

    private processPartialVector8EntityDecl(edecl: MIRPrimitiveInternalEntityTypeDecl, icpptype: ICPPCollectionInternalsLayoutInfo): object {
        return {
            ptag: ICPPParseTag.PartialVector4Tag,
            tkey: edecl.tkey,
            name: edecl.tkey,
            heapsize: icpptype.allocinfo.heapsize,
            heapmask: icpptype.allocinfo.heapmask,
            etype: icpptype.xinfo[0].type,
            esize: icpptype.xinfo[0].size
        };
    }

    private processListTreeEntityDecl(edecl: MIRPrimitiveInternalEntityTypeDecl, icpptype: ICPPCollectionInternalsLayoutInfo): object {
        return {
            ptag: ICPPParseTag.PartialVector4Tag,
            tkey: edecl.tkey,
            name: edecl.tkey,
            etype: icpptype.xinfo[0].type,
        };
    }

    private processMapTreeEntityDecl(edecl: MIRPrimitiveInternalEntityTypeDecl, icpptype: ICPPCollectionInternalsLayoutInfo): object {
        return {
            ptag: ICPPParseTag.PartialVector4Tag,
            tkey: edecl.tkey,
            name: edecl.tkey,
            heapsize: icpptype.allocinfo.heapsize,
            heapmask: icpptype.allocinfo.heapmask,
            ktype: icpptype.xinfo[0].type,
            vtype: icpptype.xinfo[1].type,
            koffset: icpptype.xinfo[0].offset,
            voffset: icpptype.xinfo[1].offset
        };
    }

    private processEntityDecl(edcl: MIRObjectEntityTypeDecl, icpplayout: ICPPEntityLayoutInfo): object {
        const vtbl = this.vtable.find((vte) => vte.oftype === edcl.tkey) as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]};

        if(icpplayout.layout === ICPPLayoutCategory.Ref) {
            return {
                ptag: ICPPParseTag.EntityObjectRefTag,
                tkey: edcl.tkey,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: edcl.tkey,
                vtable: vtbl || null,
                fieldnames: icpplayout.fieldnames,
                fieldtypes: icpplayout.fieldtypes,
                fieldoffsets: icpplayout.fieldoffsets
            };
        }
        else {
            return {
                ptag: ICPPParseTag.EntityObjectStructTag,
                tkey: edcl.tkey,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: edcl.tkey,
                vtable: vtbl || null,
                norefs: icpplayout.canScalarStackAllocate(),
                boxedtype: this.generateBoxedTypeName(edcl.tkey),
                fieldnames: icpplayout.fieldnames,
                fieldtypes: icpplayout.fieldtypes,
                fieldoffsets: icpplayout.fieldoffsets
            };
        }
    }

    private processConceptDecl(cdcl: MIRConceptTypeDecl, icpplayout: ICPPLayoutInfo, subtypes: MIRResolvedTypeKey[]): object {
        if(icpplayout.layout === ICPPLayoutCategory.UnionRef) {
            return {
                ptag: ICPPParseTag.RefUnionTag,
                tkey: cdcl.tkey,
                name: cdcl.tkey,
                subtypes: subtypes
            };
        }
        else if (icpplayout.layout === ICPPLayoutCategory.UnionInline) {
            return {
                ptag: ICPPParseTag.InlineUnionTag,
                tkey: cdcl.tkey,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.tkey,
                subtypes: subtypes
            };
        }
        else {
            return {
                ptag: ICPPParseTag.UniversalUnionTag,
                tkey: cdcl.tkey,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.tkey,
                subtypes: subtypes
            };
        }
    }

    private processTupleDecl(cdcl: MIRTupleType, icpplayout: ICPPTupleLayoutInfo): object {
        const vtbl = this.vtable.find((vte) => vte.oftype === cdcl.typeID) as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]};

        if(icpplayout.layout === ICPPLayoutCategory.Ref) {
            return {
                ptag: ICPPParseTag.TupleRefTag,
                tkey: cdcl.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.typeID,
                vtable: vtbl || null,
                maxIndex: icpplayout.maxIndex,
                ttypes: icpplayout.ttypes,
                idxoffsets: icpplayout.idxoffsets
            };
        }
        else {
            return {
                ptag: ICPPParseTag.TupleStructTag,
                tkey: cdcl.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.typeID,
                vtable: vtbl || null,
                norefs: icpplayout.canScalarStackAllocate(),
                boxedtype: this.generateBoxedTypeName(cdcl.typeID),
                maxIndex: icpplayout.maxIndex,
                ttypes: icpplayout.ttypes,
                idxoffsets: icpplayout.idxoffsets
            };
        }
    }

    private processRecordDecl(cdcl: MIRRecordType, icpplayout: ICPPRecordLayoutInfo): object {
        const vtbl = this.vtable.find((vte) => vte.oftype === cdcl.typeID) as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]};

        if(icpplayout.layout === ICPPLayoutCategory.Ref) {
            return {
                ptag: ICPPParseTag.RecordRefTag,
                tkey: cdcl.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.typeID,
                vtable: vtbl || null,
                propertynames: icpplayout.propertynames,
                propertytypes: icpplayout.propertytypes,
                propertyoffsets: icpplayout.propertyoffsets
            };
        }
        else {
            return {
                ptag: ICPPParseTag.RecordStructTag,
                tkey: cdcl.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: cdcl.typeID,
                vtable: vtbl || null,
                norefs: icpplayout.canScalarStackAllocate(),
                boxedtype: this.generateBoxedTypeName(cdcl.typeID),
                propertynames: icpplayout.propertynames,
                propertytypes: icpplayout.propertytypes,
                propertyoffsets: icpplayout.propertyoffsets
            };
        }
    }

    private processEphemeralListDecl(cdcl: MIREphemeralListType, icpplayout: ICPPEphemeralListLayoutInfo): object {
        return {
            ptag: ICPPParseTag.EphemeralListTag,
            tkey: cdcl.typeID,
            allocinfo: icpplayout.allocinfo.jemit(),
            name: cdcl.typeID,
            norefs: icpplayout.canScalarStackAllocate(),
            boxedtype: this.generateBoxedTypeName(cdcl.typeID),
            etypes: icpplayout.etypes,
            idxoffsets: icpplayout.eoffsets
        };
    }

    private processUnionDecl(ud: MIRType, icpplayout: ICPPLayoutInfo, subtypes: MIRResolvedTypeKey[]): object {
        if(icpplayout.layout === ICPPLayoutCategory.UnionRef) {
            return {
                ptag: ICPPParseTag.RefUnionTag,
                tkey: ud.typeID,
                name: ud.typeID,
                subtypes: subtypes
            };
        }
        else if (icpplayout.layout === ICPPLayoutCategory.UnionInline) {
            return {
                ptag: ICPPParseTag.InlineUnionTag,
                tkey: ud.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: ud.typeID,
                subtypes: subtypes
            };
        }
        else {
            return {
                ptag: ICPPParseTag.UniversalUnionTag,
                tkey: ud.typeID,
                allocinfo: icpplayout.allocinfo.jemit(),
                name: ud.typeID,
                subtypes: subtypes
            };
        }
    }

    jsonEmit(assembly: MIRAssembly, entrypoints: MIRInvokeKey[]): object {
        const entitydecls = [...assembly.entityDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((edcl) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === edcl.tkey) as ICPPLayoutInfo;

            if (edcl.attributes.includes("__stringof_type")) {
                return this.processStringOfEntityDecl(edcl as MIRStringOfInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__datastring_type")) {
                return this.processDataStringStringOfEntityDecl(edcl as MIRDataStringInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__databuffer_type")) {
                return this.processDataBufferStringOfEntityDecl(edcl as MIRDataBufferInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__typedprimitive")) {
                return this.processConstructableEntityDecl(edcl as MIRConstructableEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__enum_type")) {
                return this.processEnumEntityDecl(edcl as MIREnumEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__ok_type")) {
                return this.processConstructableInternalEntityDecl(edcl as MIRConstructableInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__err_type")) {
                return this.processConstructableInternalEntityDecl(edcl as MIRConstructableInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__something_type")) {
                return this.processConstructableInternalEntityDecl(edcl as MIRConstructableInternalEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__list_type")) {
                return this.processPrimitiveListEntityDecl(edcl as MIRPrimitiveListEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__stack_type")) {
                return this.processPrimitiveStackEntityDecl(edcl as MIRPrimitiveStackEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__queue_type")) {
                return this.processPrimitiveQueueEntityDecl(edcl as MIRPrimitiveQueueEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__set_type")) {
                return this.processPrimitiveSetEntityDecl(edcl as MIRPrimitiveSetEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__map_type")) {
                return this.processPrimitiveMapEntityDecl(edcl as MIRPrimitiveMapEntityTypeDecl, icpplayout);
            }
            else if (edcl.attributes.includes("__partial_vector4_type")) {
                return this.processPartialVector4EntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl, icpplayout as ICPPCollectionInternalsLayoutInfo);
            }
            else if (edcl.attributes.includes("__partial_vector8_type")) {
                return this.processPartialVector8EntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl, icpplayout as ICPPCollectionInternalsLayoutInfo);
            }
            else if (edcl.attributes.includes("__map_type")) {
                return this.processListTreeEntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl, icpplayout as ICPPCollectionInternalsLayoutInfo);
            }
            else if (edcl.attributes.includes("__map_type")) {
                return this.processMapTreeEntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl, icpplayout as ICPPCollectionInternalsLayoutInfo);
            }
            else if (edcl instanceof MIRObjectEntityTypeDecl) {
                return this.processEntityDecl(edcl, icpplayout as ICPPEntityLayoutInfo);
            }
            else {
                return undefined;
            }
        }).filter((icppt) => icppt !== undefined);

        const conceptdecls = [...assembly.conceptDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((tdcl) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === tdcl.tkey) as ICPPLayoutInfo;
            const ctype = assembly.typeMap.get(tdcl.tkey) as MIRType;
            const subtypes = [...assembly.typeMap].filter((tt) => assembly.subtypeOf(tt[1], ctype)).map((subt) => subt[0]);

            return this.processConceptDecl(tdcl, icpplayout, subtypes);
        });

        const tupledecls = [...assembly.tupleDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((tdcl) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === tdcl.typeID) as ICPPLayoutInfo;

            return this.processTupleDecl(tdcl, icpplayout as ICPPTupleLayoutInfo);
        });

        const recorddecls = [...assembly.recordDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((rdcl) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === rdcl.typeID) as ICPPLayoutInfo;

            return this.processRecordDecl(rdcl, icpplayout as ICPPRecordLayoutInfo);
        });

        const elistdecls = [...assembly.ephemeralListDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((eldcl) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === eldcl.typeID) as ICPPLayoutInfo;

            return this.processEphemeralListDecl(eldcl, icpplayout as ICPPEphemeralListLayoutInfo);
        });

        const uniondecls = [...assembly.typeMap].filter((td) => td[1].options.length > 1).sort((a, b) => a[0].localeCompare(b[0])).map((td) => td[1]).map((ud) => {
            const icpplayout = this.typedecls.find((dd) => dd.tkey === ud.typeID) as ICPPLayoutInfo;
            const subtypes = [...assembly.typeMap].filter((tt) => assembly.subtypeOf(tt[1], ud)).map((subt) => subt[0]);

            return this.processUnionDecl(ud, icpplayout, subtypes);
        });

        const boxedtypes = [...assembly.typeMap]
            .filter((td) => {
                const icppinfo = (this.typedecls.find((dd) => dd.tkey === td[0]) as ICPPLayoutInfo);
                return icppinfo.layout === ICPPLayoutCategory.Inline && icppinfo.allocinfo.inlinedatasize > UNIVERSAL_CONTENT_SIZE
            })
            .sort((a, b) => a[0].localeCompare(b[0])).map((td) => td[1])
            .map((ud) => {
                return {
                    ptag: ICPPParseTag.BoxedStructTag,
                    tkey: this.generateBoxedTypeName(ud.typeID),
                    name: this.generateBoxedTypeName(ud.typeID),
                    oftype: ud.typeID
                }
        });

        const lflavors = [...assembly.entityDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((edcl) => {
            if (edcl.attributes.includes("__list_type")) {
                const ldcl = edcl as MIRPrimitiveListEntityTypeDecl;
                return {
                    ltype: ldcl.tkey,
                    reprtype: ldcl.oftype,
                    entrytype: ldcl.getTypeT().typeID,
                    pv4type: `PartialVector4<${ldcl.getTypeT().typeID}>`,
                    pv8type: `PartialVector8<${ldcl.getTypeT().typeID}>`,
                    treetype: `ListTree<${ldcl.getTypeT().typeID}>`
                };
            }
            else {
                return undefined;
            }
        }).filter((icppt) => icppt !== undefined);

        const mflavors = [...assembly.entityDecls].sort((a, b) => a[0].localeCompare(b[0])).map((dclp) => dclp[1]).map((edcl) => {
            if (edcl.attributes.includes("__map_type")) {
                const mdcl = edcl as MIRPrimitiveMapEntityTypeDecl;
                return {
                    ltype: mdcl.tkey,
                    reprtype: mdcl.oftype,
                    keytype: mdcl.getTypeK().typeID,
                    valuetype: mdcl.getTypeV().typeID,
                    tupletype: mdcl.tupentrytype,
                    treetype: `MapTree<${mdcl.getTypeK().typeID}, ${mdcl.getTypeV().typeID}>`
                };
            }
            else {
                return undefined;
            }
        }).filter((icppt) => icppt !== undefined);

        const validators = [...assembly.validatorRegexs].sort((a, b) => a[0].localeCompare(b[0])).map((vdcl) => {
            return {
                vtype: vdcl[0],
                regex: vdcl[1].jemit()
            };
        });

        const regexes = assembly.literalRegexs.sort((a, b) => a.restr.localeCompare(b.restr)).map((redcl) => {
            return redcl.jemit();
        });

        return {
            cmask: this.cmask,
            cbuffsize: this.cbuffsize,
            
            typenames: this.typenames.sort(),
            propertynames: this.propertynames.sort(),
            fieldnames: this.fields.map((ff) => ff.fkey).sort(),

            fielddecls: this.fields.sort((a, b) => a.fkey.localeCompare(b.fkey)).map((ff) => {
                return {
                    fkey: ff.fkey,
                    fname: ff.fname,
                    declaredType: ff.declaredType,
                    isOptional: ff.isOptional
                }
            }),

            invokenames: [...this.invokenames].sort(),
            vinvokenames: [...this.vinvokenames].sort(),

            vtable: this.vtable.sort((a, b) => a.oftype.localeCompare(b.oftype)),

            typedecls: [...entitydecls, ...conceptdecls, ...tupledecls, ...recorddecls, ...elistdecls, ...uniondecls],

            boxeddecls: boxedtypes,

            listflavors: lflavors,

            mapflavors: mflavors,

            invdecls: this.invdecls.sort((a, b) => a.ikey.localeCompare(b.ikey)).map((inv) => inv.jsonEmit()),

            litdecls: this.litdecls.sort((a, b) => a.value.localeCompare(b.value)).map((lv) => {
                return {offset: lv.offset, storage: lv.storage.tkey, value: lv.value};
            }),

            validators: validators,

            regexes: regexes,

            constdecls: this.constdecls.sort((a, b) => a.gkey.localeCompare(b.gkey)).map((cd) => cd.jsonEmit())
        };
    }
}

export {
    TranspilerOptions, SourceInfo, ICPP_WORD_SIZE, UNIVERSAL_CONTENT_SIZE, UNIVERSAL_TOTAL_SIZE, UNIVERSAL_MASK,
    ICPPTypeSizeInfo, RefMask,
    ICPPLayoutCategory, ICPPLayoutInfo, ICPPLayoutInfoFixed, ICPPTupleLayoutInfo, ICPPRecordLayoutInfo, ICPPEntityLayoutInfo, ICPPCollectionInternalsLayoutInfo, ICPPEphemeralListLayoutInfo, 
    ICPPLayoutInlineUnion, ICPPLayoutRefUnion, ICPPLayoutUniversalUnion,
    ICPPInvokeDecl, ICPPFunctionParameter, ICPPPCode, ICPPInvokeBodyDecl, ICPPInvokePrimitiveDecl,
    ICPPConstDecl,
    ICPPAssembly
};

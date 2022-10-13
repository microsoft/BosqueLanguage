//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType, MIRTypeOption } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";

class ISCConstraint {
    readonly path: number[];
    readonly condition: string;

    constructor(path: number[], condition: string) {
        this.path = path;
        this.condition = condition;
    }

    static create(condition: string): ISCConstraint {
        return new ISCConstraint([], condition);
    }

    extend(step: number): ISCConstraint {
        return new ISCConstraint([step, ...this.path], this.condition);
    }

    emitSMT(): string {
        const pathstr = "(seq.++ " + this.path.map((pv) => `(seq.unit ${pv})`).join(" ") + ")";
        const assertstr = `(assert ${this.condition.replace(";;PATH;;", pathstr)})`;

        return assertstr;
    }
}

class ISCTestOption {
    readonly constraints: ISCConstraint[];

    constructor(constraints: ISCConstraint[]) {
        this.constraints = constraints;
    }

    extend(step: number): ISCTestOption {
        return new ISCTestOption(this.constraints.map((c) => c.extend(step)));
    }

    augment(condition: string) {
        return new ISCTestOption([ISCConstraint.create(condition), ...this.constraints]);
    }

    static join(...optsets: ISCTestOption[][]): ISCTestOption[] {
        return ([] as ISCTestOption[]).concat(...optsets);
    }
}

class ISCGenerator {
    readonly assembly: MIRAssembly;
    readonly temitter: SMTTypeEmitter;

    constructor(assembly: MIRAssembly, temitter: SMTTypeEmitter) {
        this.assembly = assembly;
        this.temitter = temitter;
    }

    private generateISCOptions_Bool(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BBool@UFCons_API ;;PATH;;) true)")]), 
            new ISCTestOption([ISCConstraint.create("(= (BBool@UFCons_API ;;PATH;;) false)")])
        ];
    }

    private generateISCOptions_Nat(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BNat@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_Int(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BInt@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BInt@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_BigNat(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BBigNat@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BBigNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_BigInt(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BBigInt@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BBigInt@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BBigInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_Float(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BFloat@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BFloat@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BFloat@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_Decimal(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BDecimal@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BDecimal@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BDecimal@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_Rational(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BRational@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BRational@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BRational@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_String(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \"\")")]),
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \"a\")")]),
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \" \")")]),
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \"3\")")]),
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \"#\")")]),
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \".\")")]),
            new ISCTestOption([ISCConstraint.create("(> (len (BString@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateISCOptions_ByteBuffer(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateISCOptions_DateTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 11)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 31)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 23)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2019)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 10)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 3)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 1)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) \"PST\")")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2019)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 10)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 3)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 1)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 0)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) \"PDT\")")
            ])
        ];
    }
  
    private generateISCOptions_UTCDateTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 11)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 31)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 23)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)")
            ])
        ];
    }
  
  private generateISCOptions_CalendarDate(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ])
        ];
    }

    private generateISCOptions_TickTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BTickTime@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (BTickTime@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_LogicalTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BLogicalTime@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (BLogicalTime@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_ISOTimeStamp(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_UUID4(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_UUID7(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_SHAContentHash(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_LatLongCoordinate(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BLatitude@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BLatitude@UFCons_API ;;PATH;;) -90.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BLongitude@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BLongitude@UFCons_API ;;PATH;;) 180.0)")]),
        ];
    }

    private generateISCOptions_StringOf(tt: MIRType): ISCTestOption[] {
        const bcreate = this.generateISCOptions_String();

        //TODO: maybe add options around what the regex allows instead?

        return bcreate;
    }

    private  generateISCOptions_DataString(tt: MIRType): ISCTestOption[] {
        return this.generateISCOptions_String();
    }

    private  generateISCOptions_DataBuffer(tt: MIRType): ISCTestOption[] {
        return this.generateISCOptions_ByteBuffer();
    }

    private generateISCOptions_TypedPrimitive(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRConstructableEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.valuetype);

        return this.generateISCOptions(oftype);
    }

    private generateISCOptions_Something(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        return this.generateISCOptions(oftype);
    }

    private generateISCOptions_Ok(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        return this.generateISCOptions(oftype);
    }

    private generateISCOptions_Err(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        return this.generateISCOptions(oftype);
    }

    private generateISCOptions_Enum(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIREnumEntityTypeDecl;
        const emax = tdecl.enums.length;

        let topts: ISCTestOption[] = [];
        for(let i = 0; i < emax; ++i) {
            topts.push(new ISCTestOption([ISCConstraint.create(`(= (BEnum@UFCons_API ;;PATH;;) ${i}")`)]));
        }
        
        return topts;
    }

    private generateISCOptions_Tuple(tt: MIRType): ISCTestOption[] {
        const ttuple = tt.options[0] as MIRTupleType;

        const ctors = ttuple.entries.map((ee, i) => {
            const cc = this.generateISCOptions(ee);
            return cc.map((c) => c.extend(i));
        });

        return ISCTestOption.join(...ctors);
    }

    private generateISCOptions_Record(tt: MIRType): ISCTestOption[] {
        const trecord = tt.options[0] as MIRRecordType;

        const ctors = trecord.entries.map((ee, i) => {
            const cc = this.generateISCOptions(ee.ptype);
            return cc.map((c) => c.extend(i));
        });

        return ISCTestOption.join(...ctors);
    }

    private generateISCOptions_Object(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRObjectEntityTypeDecl;

        const ctors = tdecl.consfuncfields.map((ee, i) => {
            const ff = this.temitter.assembly.fieldDecls.get(ee.cfkey) as MIRFieldDecl;
            const fftype = this.temitter.getMIRType(ff.declaredType);

            const cc = this.generateISCOptions(fftype);
            return cc.map((c) => c.extend(i));
        });

        //see args path thing
        const allopts = ISCTestOption.join(...ctors).map((oo) => oo.extend(0));

        return allopts;
    }

    private generateISCOptions_List(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveListEntityTypeDecl;
        const lentrytype = this.temitter.getMIRType(tdecl.getTypeT().typeID);

        const topts = this.generateISCOptions(lentrytype);

        const empty_opt = new ISCTestOption([ISCConstraint.create("(= (ContainerSize@UFCons_API ;;PATH;;) 0)")]);
        
        const one_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 1)"));
        const two_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 2)"));
        const four_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 4)"));
        
        const three_zero_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        const three_one_opts = topts.map((oo) => oo.extend(1).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        const three_two_opts = topts.map((oo) => oo.extend(2).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        
        return [empty_opt, ...one_opts, ...two_opts, ...four_opts, ...three_zero_opts, ...three_one_opts, ...three_two_opts];
    }

    private generateISCOptions_Stack(tt: MIRType): ISCTestOption[] {
        assert(false, "generateISCOptions_Stack");
        return [];
    }

    private generateISCOptions_Queue(tt: MIRType): ISCTestOption[] {
        assert(false, "generateISCOptions_Queue");
        return [];
    }

    private generateISCOptions_Set(tt: MIRType): ISCTestOption[] {
        assert(false, "generateISCOptions_Set");
        return [];
    }

    private generateISCOptions_Map(tt: MIRType): ISCTestOption[] {
        const tdecl = this.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveMapEntityTypeDecl;
        const lentrytype = this.temitter.getMIRType(`[${tdecl.getTypeK().typeID}, ${tdecl.getTypeV().typeID}]`);

        const topts = this.generateISCOptions(lentrytype);

        const empty_opt = new ISCTestOption([ISCConstraint.create("(= (ContainerSize@UFCons_API ;;PATH;;) 0)")]);
        
        const one_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 1)"));
        const two_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 2)"));
        const four_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 4)"));
        
        const three_zero_opts = topts.map((oo) => oo.extend(0).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        const three_one_opts = topts.map((oo) => oo.extend(1).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        const three_two_opts = topts.map((oo) => oo.extend(2).augment("(= (ContainerSize@UFCons_API ;;PATH;;) 3)"));
        
        return [empty_opt, ...one_opts, ...two_opts, ...four_opts, ...three_zero_opts, ...three_one_opts, ...three_two_opts];
    }

    private generateISCOptions_Union(tt: MIRType, opts: MIRTypeOption[]): ISCTestOption[] {
        let allopts: ISCTestOption[][] = [];

        for(let i = 0; i < opts.length; ++i) {
            let ofidx = opts.length - (i + 1);
            let oftt = this.temitter.getMIRType(opts[ofidx].typeID);

            const cc = this.generateISCOptions(oftt);
            const iopts = cc.map((c) => c.extend(ofidx).augment(`(= (UnionChoice@UFCons_API ;;PATH;;) ${ofidx})`));

            allopts.push(iopts);
        }

        return ISCTestOption.join(...allopts);
    }

    private generateISCOptions(tt: MIRType): ISCTestOption[] {
        //
        //TODO: this isn't recursive type friendly!!!!
        //

        if (tt.options.length !== 1) {
            const etypes = [...this.assembly.typeMap].filter((edi) => this.assembly.subtypeOf(edi[1], this.temitter.getMIRType(tt.typeID)));
            const opts: MIRTypeOption[] = etypes.map((opt) => opt[1].options[0]).sort((a, b) => a.typeID.localeCompare(b.typeID));

            let ropts: MIRTypeOption[] = [];
            for(let i = 0; i < opts.length; ++i) {
                const has = ropts.find((ropt) => ropt.typeID === opts[i].typeID) !== undefined;
                if(!has) {
                    ropts.push(opts[i]);
                }
            }

            return this.generateISCOptions_Union(tt, ropts);
        }
        else {
            if (this.temitter.isUniqueTupleType(tt)) {
                return this.generateISCOptions_Tuple(tt);
            }
            else if (this.temitter.isUniqueRecordType(tt)) {
                return this.generateISCOptions_Record(tt);
            }
            else if (this.temitter.isUniqueEntityType(tt)) {
                const etype = tt.options[0] as MIREntityType;
                const edecl = this.temitter.assembly.entityDecls.get(etype.typeID) as MIREntityTypeDecl;
 
                if (etype.typeID === "None") {
                    return [];
                }
                else if(etype.typeID === "Bool") {
                    return this.generateISCOptions_Bool();
                }
                else if(etype.typeID === "Nat") {
                    return this.generateISCOptions_Nat();
                }
                else if(etype.typeID === "Int") {
                    return this.generateISCOptions_Int();
                }
                else if(etype.typeID === "BigNat") {
                    return this.generateISCOptions_BigNat();
                }
                else if(etype.typeID === "BigInt") {
                    return this.generateISCOptions_BigInt();
                }
                else if(etype.typeID === "Float") {
                    return this.generateISCOptions_Float();
                }
                else if(etype.typeID === "Decimal") {
                    return this.generateISCOptions_Decimal();
                }
                else if(etype.typeID === "Rational") {
                    return this.generateISCOptions_Rational();
                }
                else if(etype.typeID === "String") {
                    return this.generateISCOptions_String();
                }
                else if(etype.typeID === "ByteBuffer") {
                    return this.generateISCOptions_ByteBuffer();
                }
                else if(etype.typeID === "DateTime") {
                    return this.generateISCOptions_DateTime();
                }
                else if(etype.typeID === "UTCDateTime") {
                    return this.generateISCOptions_UTCDateTime();
                }
                else if(etype.typeID === "CalendarDate") {
                    return this.generateISCOptions_CalendarDate();
                }
                else if(etype.typeID === "TickTime") {
                    return this.generateISCOptions_TickTime();
                }
                else if(etype.typeID === "LogicalTime") {
                    return this.generateISCOptions_LogicalTime();
                }
                else if(etype.typeID === "ISOTimeStamp") {
                    return this.generateISCOptions_ISOTimeStamp();
                }
                else if(etype.typeID === "UUID4") {
                    return this.generateISCOptions_UUID4();
                }
                else if(etype.typeID === "UUID7") {
                    return this.generateISCOptions_UUID7();
                }
                else if(etype.typeID === "SHAContentHash") {
                    return this.generateISCOptions_SHAContentHash();
                }
                else if(etype.typeID === "LatLongCoordinate") {
                    return this.generateISCOptions_LatLongCoordinate();
                }
                else if (edecl.attributes.includes("__stringof_type")) {
                    return this.generateISCOptions_StringOf(tt);
                }
                else if (edecl.attributes.includes("__datastring_type")) {
                    return this.generateISCOptions_DataString(tt);
                }
                else if (edecl.attributes.includes("__databuffer_type")) {
                    return this.generateISCOptions_DataBuffer(tt);
                }
                else if (edecl.attributes.includes("__typedprimitive")) {
                    return this.generateISCOptions_TypedPrimitive(tt);
                }
                else if (edecl.attributes.includes("__enum_type")) {
                    return this.generateISCOptions_Enum(tt);
                }
                else if (edecl.attributes.includes("__ok_type")) {
                    return this.generateISCOptions_Ok(tt);
                }
                else if (edecl.attributes.includes("__err_type")) {
                    return this.generateISCOptions_Err(tt);
                }
                else if (edecl.attributes.includes("__something_type")) {
                    return this.generateISCOptions_Something(tt);
                }
                else if (edecl.attributes.includes("__list_type")) {
                    return this.generateISCOptions_List(tt);
                }
                else if (edecl.attributes.includes("__stack_type")) {
                    return this.generateISCOptions_Stack(tt);
                }
                else if (edecl.attributes.includes("__queue_type")) {
                    return this.generateISCOptions_Queue(tt);
                }
                else if (edecl.attributes.includes("__set_type")) {
                    return this.generateISCOptions_Set(tt);
                }
                else if (edecl.attributes.includes("__map_type")) {
                    return this.generateISCOptions_Map(tt);
                }
                else if (edecl instanceof MIRObjectEntityTypeDecl) {
                    return this.generateISCOptions_Object(tt);
                }
                else {
                    //Don't need to do anything -- is this even possible?
                    return [];
                }
            }
            else if (tt.options[0] instanceof MIRConceptType) {
                const etypes = [...this.assembly.entityDecls].filter((edi) => this.assembly.subtypeOf(this.temitter.getMIRType(edi[1].tkey), this.temitter.getMIRType(tt.typeID)));
                const opts: MIRTypeOption[] = etypes.map((opt) => this.temitter.getMIRType(opt[1].tkey).options[0]).sort((a, b) => a.typeID.localeCompare(b.typeID));

                let ropts: MIRTypeOption[] = [];
                for(let i = 0; i < opts.length; ++i) {
                    const has = ropts.find((ropt) => ropt.typeID === opts[i].typeID) !== undefined;
                    if(!has) {
                        ropts.push(opts[i]);
                    }
                }

                return this.generateISCOptions_Union(tt, ropts);
            }
            else {
                //Don't need to do anything -- is this even possible?
                return [];
            }
        }
    }

    static generateInputConstraintOptions(inv: MIRInvokeDecl, assembly: MIRAssembly, temitter: SMTTypeEmitter): string[] {
        const gen = new ISCGenerator(assembly, temitter);

        const popts = inv.params.map((p) => gen.generateISCOptions(temitter.getMIRType(p.type)).map((opt) => opt.extend(0)));
        const allopts = ISCTestOption.join(...popts);

        return allopts.map((opt) => {
            const ccs = opt.constraints.map((cc) => cc.emitSMT());
            return ccs.join(" "); 
        });
    }
}

export {
    ISCGenerator
}

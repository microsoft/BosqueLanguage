//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

type VerifierOptions = {
    ISize: number, //bits used for Int/Nat
    StringOpt: "ASCII" | "UNICODE",

    EnableCollection_SmallMode: boolean,
    EnableCollection_LargeMode: boolean
};

class BVEmitter {
    readonly bvsize: bigint;
    readonly natmax: bigint;
    readonly intmin: bigint;
    readonly intmax: bigint;

    readonly bvnatmax: string;
    readonly bvintmin: string;
    readonly bvintmax: string;

    readonly bvnatmax1: string;
    readonly bvintmin1: string;
    readonly bvintmax1: string;

    computeBVMinSigned(bits: bigint): bigint {
        return -((2n ** bits) / 2n);
    }

    computeBVMaxSigned(bits: bigint): bigint {
        return ((2n ** bits) / 2n) - 1n;
    }

    computeBVMaxUnSigned(bits: bigint): bigint {
        return (2n ** bits) - 1n;
    }

    constructor(bvsize: bigint, natmax: bigint, intmin: bigint, intmax: bigint, natmax1: bigint, intmin1: bigint, intmax1: bigint) {
        this.bvsize = bvsize;
        this.natmax = natmax;
        this.intmin = intmin;
        this.intmax = intmax;

        this.bvnatmax = natmax.toString();
        this.bvintmin = intmin.toString();
        this.bvintmax = intmax.toString();

        this.bvnatmax1 = natmax1.toString();
        this.bvintmin1 = intmin1.toString();
        this.bvintmax1 = intmax1.toString();
    }

    create(bvsize: bigint): BVEmitter {
        return new BVEmitter(bvsize, 
            this.computeBVMaxUnSigned(bvsize), this.computeBVMinSigned(bvsize), this.computeBVMaxSigned(bvsize),
            this.computeBVMaxUnSigned(bvsize + 1n), this.computeBVMinSigned(bvsize + 1n), this.computeBVMaxSigned(bvsize + 1n))
    }

    emitIntGeneral(val: bigint): SMTExp {
        if(val === 0n) {
            return new SMTConst("BInt@zero");
        }
        else {
            if (val > 0) {
                assert(BigInt(val) <= this.intmax);
                let bits = BigInt(val).toString(2);

                while(bits.length < this.bvsize) {
                    bits = "0" + bits;
                }
                return new SMTConst(`#b${bits}`);
            }
            else {
                assert(this.intmin <= BigInt(val));

                let bits = (~BigInt(val) + 1n).toString(2).slice(0, Number(this.bvsize));
                while(bits.length < this.bvsize) {
                    bits = "1" + bits;
                }
                return new SMTConst(`#b${bits}`);
            }
        }
    }

    emitNatGeneral(val: bigint): SMTExp {
        if(val === 0n) {
            return new SMTConst("BNat@zero");
        }
        else {
            assert(0 < val && BigInt(val) <= this.natmax);
            return new SMTConst(`(_ bv${val} ${this.bvsize})`);
        }
    }

    emitSimpleInt(val: number): SMTExp {
        return this.emitIntGeneral(BigInt(val));
    }

    emitSimpleNat(val: number): SMTExp {
       return this.emitNatGeneral(BigInt(val));
    }

    emitInt(intv: string): SMTExp {
        return this.emitIntGeneral(BigInt(intv.slice(0, intv.length - 1)));
    }

    emitNat(natv: string): SMTExp {
        return this.emitNatGeneral(BigInt(natv.slice(0, natv.length - 1)));
    }
}

class SMTMaskConstruct {
    readonly maskname: string;
    readonly entries: SMTExp[] = [];

    constructor(maskname: string) {
        this.maskname = maskname;
    }

    emitSMT2(): string {
        return `($Mask_${this.entries.length}@cons ${this.entries.map((mv) => mv.emitSMT2(undefined)).join(" ")})`;
    }
}

class SMTType {
    readonly name: string;
    readonly smttypetag: string;
    readonly typeID: MIRResolvedTypeKey;
    
    constructor(name: string, smttypetag: string, typeid: MIRResolvedTypeKey) {
        this.name = name;
        this.smttypetag = smttypetag;
        this.typeID = typeid;
    }

    isGeneralKeyType(): boolean {
        return this.name === "BKey";
    }

    isGeneralTermType(): boolean {
        return this.name === "BTerm";
    }
}

abstract class SMTExp {
    abstract emitSMT2(indent: string | undefined): string;

    abstract computeCallees(callees: Set<string>): void;
}

class SMTVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();

        this.vname = vname;
    }

    emitSMT2(indent: string | undefined): string {
        return this.vname;
    }

    computeCallees(callees: Set<string>): void {
        //Nothing to do in many cases
    }
}

class SMTConst extends SMTExp {
    readonly cname: string;

    constructor(cname: string) {
        super();

        this.cname = cname;
    }

    emitSMT2(indent: string | undefined): string {
        return this.cname;
    }

    computeCallees(callees: Set<string>): void {
        //Nothing to do in many cases
    }
}

class SMTCallSimple extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? this.fname : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }

    static makeEq(lhs: SMTExp, rhs: SMTExp): SMTExp {
        return new SMTCallSimple("=", [lhs, rhs]);
    }

    static makeNotEq(lhs: SMTExp, rhs: SMTExp): SMTExp {
        return new SMTCallSimple("not", [new SMTCallSimple("=", [lhs, rhs])]);
    }

    static makeBinOp(op: string, lhs: SMTExp, rhs: SMTExp): SMTExp {
        return new SMTCallSimple(op, [lhs, rhs]);
    }

    static makeIsTypeOp(smtname: string, exp: SMTExp): SMTExp {
        return new SMTCallSimple(`(_ is ${smtname})`, [exp]);
    }

    static makeNot(exp: SMTExp): SMTExp {
        return new SMTCallSimple("not", [exp]);
    }

    static makeAndOf(...exps: SMTExp[]): SMTExp {
        return new SMTCallSimple("and", exps);
    }

    static makeOrOf(...exps: SMTExp[]): SMTExp {
        return new SMTCallSimple("or", exps);
    }
}

class SMTCallGeneral extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? this.fname : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }
}

class SMTCallGeneralWOptMask extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];
    readonly mask: SMTMaskConstruct;

    constructor(fname: string, args: SMTExp[], mask: SMTMaskConstruct) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? `(${this.fname} ${this.mask.emitSMT2()})` : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")} ${this.mask.emitSMT2()})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));

        this.mask.entries.forEach((mentry) => mentry.computeCallees(callees));
    }
}

class SMTCallGeneralWPassThroughMask extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];
    readonly mask: string;

    constructor(fname: string, args: SMTExp[], mask: string) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? `(${this.fname} ${this.mask})` : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")} ${this.mask})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }
}

class SMTLet extends SMTExp {
    readonly vname: string;
    readonly value: SMTExp;
    readonly inexp: SMTExp;

    constructor(vname: string, value: SMTExp, inexp: SMTExp) {
        super();

        this.vname = vname;
        this.value = value;
        this.inexp = inexp;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            return `(let ((${this.vname} ${this.value.emitSMT2(undefined)})) ${this.inexp.emitSMT2(undefined)})`;
        }
        else {
            return `(let ((${this.vname} ${this.value.emitSMT2(undefined)}))\n${indent + "  "}${this.inexp.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.value.computeCallees(callees);
        this.inexp.computeCallees(callees);
    }
}

class SMTLetMulti extends SMTExp {
    readonly assigns: { vname: string, value: SMTExp }[];
    readonly inexp: SMTExp

    constructor(assigns: { vname: string, value: SMTExp }[], inexp: SMTExp) {
        super();

        this.assigns = assigns;
        this.inexp = inexp;
    }

    emitSMT2(indent: string | undefined): string {
        const binds = this.assigns.map((asgn) => `(${asgn.vname} ${asgn.value.emitSMT2(undefined)})`);

        if (indent === undefined) {
            return `(let (${binds.join(" ")}) ${this.inexp.emitSMT2(undefined)})`;
        }
        else {
            return `(let (${binds.join(" ")})\n${indent + "  "}${this.inexp.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.assigns.forEach((asgn) => {
            asgn.value.computeCallees(callees);
        });
        this.inexp.computeCallees(callees);
    }
}

class SMTIf extends SMTExp {
    readonly cond: SMTExp;
    readonly tval: SMTExp;
    readonly fval: SMTExp;

    constructor(cond: SMTExp, tval: SMTExp, fval: SMTExp) {
        super();

        this.cond = cond;
        this.tval = tval;
        this.fval = fval;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            return `(ite ${this.cond.emitSMT2(undefined)} ${this.tval.emitSMT2(undefined)} ${this.fval.emitSMT2(undefined)})`;
        }
        else {
            return `(ite ${this.cond.emitSMT2(undefined)}\n${indent + "  "}${this.tval.emitSMT2(indent + "  ")}\n${indent + "  "}${this.fval.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.cond.computeCallees(callees);
        this.tval.computeCallees(callees);
        this.fval.computeCallees(callees);
    }
}

class SMTCond extends SMTExp {
    readonly opts: {test: SMTExp, result: SMTExp}[];
    readonly orelse: SMTExp;

    constructor(opts: {test: SMTExp, result: SMTExp}[], orelse: SMTExp) {
        super();

        this.opts = opts;
        this.orelse = orelse;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            let iopts: string = this.orelse.emitSMT2(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `(ite ${this.opts[i].test.emitSMT2(undefined)} ${this.opts[i].result.emitSMT2(undefined)} ${iopts})`
            }
            return iopts;
        }
        else {
            let iopts: string = this.orelse.emitSMT2(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `(ite ${this.opts[i].test.emitSMT2(undefined)}\n${indent + "  "}${this.opts[i].result.emitSMT2(indent + "  ")}\n${indent + "  "}${iopts}\n${indent})`
            }
            return iopts;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.opts.forEach((opt) => {
            opt.test.computeCallees(callees);
            opt.result.computeCallees(callees);
        });
        this.orelse.computeCallees(callees);
    }
}

class SMTADTKindSwitch extends SMTExp {
    readonly value: SMTExp;
    readonly opts: { cons: string, cargs: string[], result: SMTExp }[];

    constructor(value: SMTExp, opts: { cons: string, cargs: string[], result: SMTExp }[]) {
        super();

        this.value = value;
        this.opts = opts;
    }

    emitSMT2(indent: string | undefined): string {
        const matches = this.opts.map((op) => {
            const test = op.cargs.length !== 0 ? `(${op.cons} ${op.cargs.join(" ")})` : op.cons;
            return `(${test} ${op.result.emitSMT2(undefined)})`;
        });

        if (indent === undefined) {
            return `(match ${this.value.emitSMT2(undefined)} (${matches.join(" ")}))`;
        }
        else {
            return `(match ${this.value.emitSMT2(undefined)} (\n${indent + "  "}${matches.join("\n" + indent + "  ")})\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.value.computeCallees(callees);
        this.opts.forEach((opt) => {
            opt.result.computeCallees(callees);
        });
    }
}

class SMTForAll extends SMTExp {
    readonly terms: { vname: string, vtype: SMTType }[];
    readonly clause: SMTExp;

    constructor(terms: { vname: string, vtype: SMTType }[], clause: SMTExp) {
        super();

        this.terms = terms;
        this.clause = clause;
    }

    emitSMT2(indent: string | undefined): string {
        const terms = this.terms.map((t) => `(${t.vname} ${t.vtype.name})`);

        if(indent === undefined) {
            return `(forall (${terms.join(" ")}) ${this.clause.emitSMT2(undefined)})`;
        }
        else {
            return `(forall (${terms.join(" ")})\n${indent + "  "}${this.clause.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.clause.computeCallees(callees);
    }
}

class SMTExists extends SMTExp {
    readonly terms: { vname: string, vtype: SMTType }[];
    readonly clause: SMTExp;

    constructor(terms: { vname: string, vtype: SMTType }[], clause: SMTExp) {
        super();

        this.terms = terms;
        this.clause = clause;
    }

    emitSMT2(indent: string | undefined): string {
        const terms = this.terms.map((t) => `(${t.vname} ${t.vtype.name})`);
        
        if(indent === undefined) {
            return `(exists (${terms.join(" ")}) ${this.clause.emitSMT2(undefined)})`;
        }
        else {
            return `(exists (${terms.join(" ")})\n${indent + "  "}${this.clause.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.clause.computeCallees(callees);
    }
}

export {
    VerifierOptions,
    SMTMaskConstruct,
    BVEmitter,
    SMTType, SMTExp, SMTVar, SMTConst, 
    SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallGeneralWPassThroughMask,
    SMTLet, SMTLetMulti, SMTIf, SMTCond, SMTADTKindSwitch,
    SMTForAll, SMTExists
};

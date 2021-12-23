//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

type VerifierOptions = {
    ISize: number, //bits used for Int/Nat
    StringOpt: "ASCII" | "UNICODE"
};

class BVEmitter {
    readonly bvsize: bigint;
    readonly natmax: bigint;
    readonly intmin: bigint;
    readonly intmax: bigint;

    readonly bvnatmax: SMTExp;
    readonly bvintmin: SMTExp;
    readonly bvintmax: SMTExp;

    readonly bvnatmax1: SMTExp;
    readonly bvintmin1: SMTExp;
    readonly bvintmax1: SMTExp;

    static computeBVMinSigned(bits: bigint): bigint {
        return -((2n ** bits) / 2n);
    }

    static computeBVMaxSigned(bits: bigint): bigint {
        return ((2n ** bits) / 2n) - 1n;
    }

    static computeBVMaxUnSigned(bits: bigint): bigint {
        return (2n ** bits) - 1n;
    }

    private static emitIntCore(val: bigint, imin: bigint, imax: bigint, bvsize: bigint): SMTExp {
        if(val === 0n) {
            return new SMTConst("BInt@zero");
        }
        else {
            if (val > 0n) {
                assert(BigInt(val) <= imax);

                return new SMTConst(`(_ bv${val} ${bvsize})`);
            }
            else {
                assert(imin <= val);

                let bitstr = (-val).toString(2);
                let bits = "";
                let carry = true;
                for(let i = bitstr.length - 1; i >= 0; --i) {
                    const bs = (bitstr[i] === "0" ? "1" : "0");

                    if(bs === "0") {
                        bits = (carry ? "1": "0") + bits;
                        carry = false;
                    }
                    else {
                        if(!carry) {
                            bits = "1" + bits;
                            //carry stays false
                        }
                        else {
                            bits = "0" + bits;
                            carry = true;
                        }
                    }
                }

                while(bits.length < bvsize) {
                    bits = "1" + bits;
                }

                return new SMTConst(`#b${bits}`);
            }
        }
    }

    private static emitNatCore(val: bigint, nmax: bigint, bvsize: bigint): SMTExp {
        if(val === 0n) {
            return new SMTConst("BNat@zero");
        }
        else {
            assert(0n < val && val <= nmax);
            return new SMTConst(`(_ bv${val} ${bvsize})`);
        }
    }

    constructor(bvsize: bigint, natmax: bigint, intmin: bigint, intmax: bigint, natmax1: bigint, intmin1: bigint, intmax1: bigint) {
        this.bvsize = bvsize;
        this.natmax = natmax;
        this.intmin = intmin;
        this.intmax = intmax;

        this.bvnatmax = BVEmitter.emitNatCore(natmax, natmax, bvsize);
        this.bvintmin = BVEmitter.emitIntCore(intmin, intmin, intmax, bvsize);
        this.bvintmax = BVEmitter.emitIntCore(intmax, intmin, intmax, bvsize);

        this.bvnatmax1 = BVEmitter.emitNatCore(natmax, natmax1, bvsize + 1n);
        this.bvintmin1 = BVEmitter.emitIntCore(intmin, intmin1, intmax1, bvsize + 1n);
        this.bvintmax1 = BVEmitter.emitIntCore(intmax, intmin1, intmax1, bvsize + 1n);
    }

    static create(bvsize: bigint): BVEmitter {
        return new BVEmitter(bvsize, 
            BVEmitter.computeBVMaxUnSigned(bvsize), BVEmitter.computeBVMinSigned(bvsize), BVEmitter.computeBVMaxSigned(bvsize),
            BVEmitter.computeBVMaxUnSigned(bvsize + 1n), BVEmitter.computeBVMinSigned(bvsize + 1n), BVEmitter.computeBVMaxSigned(bvsize + 1n));
    }

    emitIntGeneral(val: bigint): SMTExp {
        return BVEmitter.emitIntCore(val, this.intmin, this.intmax, this.bvsize);
    }

    emitNatGeneral(val: bigint): SMTExp {
        return BVEmitter.emitNatCore(val, this.natmax, this.bvsize);
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

class SMTTypeInfo {
    readonly smttypename: string;
    readonly smttypetag: string;
    readonly typeID: MIRResolvedTypeKey;
    
    constructor(smttypename: string, smttypetag: string, typeid: MIRResolvedTypeKey) {
        this.smttypename = smttypename;
        this.smttypetag = smttypetag;
        this.typeID = typeid;
    }

    isGeneralKeyType(): boolean {
        return this.smttypename === "BKey";
    }

    isGeneralTermType(): boolean {
        return this.smttypename === "BTerm";
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

export {
    VerifierOptions,
    SMTMaskConstruct,
    BVEmitter,
    SMTTypeInfo, SMTExp, SMTVar, SMTConst, 
    SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallGeneralWPassThroughMask,
    SMTLet, SMTLetMulti, SMTIf, SMTCond
};

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------


import { MIRResolvedTypeKey } from "../../../compiler/mir_ops";

function cleanVarName(vn: string): string {
    let cleanname = vn.replace(/[$]/g, "_").replace(/@/g, "_");
    if(cleanname.startsWith("_")) {
        cleanname = "q" + cleanname;
    }

    if(/[A-Z]/.test(cleanname[0])) {
        cleanname = (cleanname[0].toLowerCase()) + cleanname.slice(1);
    }

    return cleanname;
}

class MorphirMaskConstruct {
    readonly maskname: string;
    readonly entries: MorphirExp[] = [];

    constructor(maskname: string) {
        this.maskname = maskname;
    }

    emitMorphir(): string {
        return `[${this.entries.map((mv) => mv.emitMorphir(undefined)).join(" ")}]`;
    }
}

class MorphirTypeInfo {
    readonly morphirtypename: string;
    readonly morphirtypetag: string;
    readonly typeID: MIRResolvedTypeKey;
    
    constructor(morphirtypename: string, morphirtypetag: string, typeid: MIRResolvedTypeKey) {
        this.morphirtypename = morphirtypename;
        this.morphirtypetag = morphirtypetag;
        this.typeID = typeid;
    }

    isGeneralKeyType(): boolean {
        return this.morphirtypename === "BKey";
    }

    isGeneralTermType(): boolean {
        return this.morphirtypename === "BTerm";
    }
}

abstract class MorphirExp {
    abstract emitMorphir(indent: string | undefined): string;

    abstract computeCallees(callees: Set<string>): void;
}

class MorphirVar extends MorphirExp {
    readonly vname: string;

    constructor(vname: string) {
        super();

        this.vname = vname;
    }

    emitMorphir(indent: string | undefined): string {
        return cleanVarName(this.vname);
    }

    computeCallees(callees: Set<string>): void {
        //Nothing to do in many cases
    }
}

class MorphirConst extends MorphirExp {
    readonly cname: string;

    constructor(cname: string) {
        super();

        this.cname = cname;
    }

    emitMorphir(indent: string | undefined): string {
        return cleanVarName(this.cname);
    }

    computeCallees(callees: Set<string>): void {
        //Nothing to do in many cases
    }
}

class MorphirCallSimple extends MorphirExp {
    readonly fname: string;
    readonly args: MorphirExp[];
    readonly infix: boolean;

    constructor(fname: string, args: MorphirExp[], infix?: boolean) {
        super();

        this.fname = fname;
        this.args = args;
        this.infix = infix || false;
    }

    emitMorphir(indent: string | undefined): string {
        if(this.infix) {
            return `(${this.args[0].emitMorphir(undefined)} ${this.fname} ${this.args[1].emitMorphir(undefined)})`;
        }
        else {
            return `(${this.fname} ${this.args.map((arg) => arg.emitMorphir(undefined)).join(" ")})`;
        }
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }

    static makeEq(lhs: MorphirExp, rhs: MorphirExp): MorphirExp {
        return new MorphirCallSimple("=", [lhs, rhs], true);
    }

    static makeNotEq(lhs: MorphirExp, rhs: MorphirExp): MorphirExp {
        return new MorphirCallSimple("/=", [lhs, rhs], true);
    }

    static makeBinOp(op: string, lhs: MorphirExp, rhs: MorphirExp): MorphirExp {
        return new MorphirCallSimple(op, [lhs, rhs], true);
    }

    static makeNot(exp: MorphirExp): MorphirExp {
        return new MorphirCallSimple("not", [exp]);
    }

    static makeAndOf(...exps: MorphirExp[]): MorphirExp {
        if(exps.length === 1) {
            return exps[0];
        }
        else if(exps.length === 2) {
            return new MorphirCallSimple("&&", exps, true);
        }
        else {
            const tand = MorphirCallSimple.makeAndOf(...exps.slice(1));
            return new MorphirCallSimple("&&", [exps[0], tand], true);
        }
    }

    static makeOrOf(...exps: MorphirExp[]): MorphirExp {
        if(exps.length === 1) {
            return exps[0];
        }
        else if(exps.length === 2) {
            return new MorphirCallSimple("||", exps, true);
        }
        else {
            const tor = MorphirCallSimple.makeOrOf(...exps.slice(1));
            return new MorphirCallSimple("||", [exps[0], tor], true);
        }
    }
}

class MorphirCallGeneral extends MorphirExp {
    readonly fname: string;
    readonly args: MorphirExp[];

    constructor(fname: string, args: MorphirExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }

    emitMorphir(indent: string | undefined): string {
        return `(${this.fname} ${this.args.map((arg) => arg.emitMorphir(undefined)).join(" ")})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }
}

class MorphirCallGeneralWOptMask extends MorphirExp {
    readonly fname: string;
    readonly args: MorphirExp[];
    readonly mask: MorphirMaskConstruct;

    constructor(fname: string, args: MorphirExp[], mask: MorphirMaskConstruct) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitMorphir(indent: string | undefined): string {
        return `(${this.fname} ${this.args.map((arg) => arg.emitMorphir(undefined)).join(" ")} ${this.mask.emitMorphir()})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));

        this.mask.entries.forEach((mentry) => mentry.computeCallees(callees));
    }
}

class MorphirCallGeneralWPassThroughMask extends MorphirExp {
    readonly fname: string;
    readonly args: MorphirExp[];
    readonly mask: string;

    constructor(fname: string, args: MorphirExp[], mask: string) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitMorphir(indent: string | undefined): string {
        return `(${this.fname} ${this.args.map((arg) => arg.emitMorphir(undefined)).join(" ")} ${this.mask})`;
    }

    computeCallees(callees: Set<string>): void {
        callees.add(this.fname);
        this.args.forEach((arg) => arg.computeCallees(callees));
    }
}

class MorphirLet extends MorphirExp {
    readonly vname: string;
    readonly value: MorphirExp;
    readonly inexp: MorphirExp;

    constructor(vname: string, value: MorphirExp, inexp: MorphirExp) {
        super();

        this.vname = vname;
        this.value = value;
        this.inexp = inexp;
    }

    emitMorphir(indent: string | undefined): string {
        if (indent === undefined) {
            return `(let ${cleanVarName(this.vname)} = ${this.value.emitMorphir(undefined)} in ${this.inexp.emitMorphir(undefined)})`;
        }
        else {
            return `let ${cleanVarName(this.vname)} = ${this.value.emitMorphir(undefined)} in\n${indent + "  "}${this.inexp.emitMorphir(indent + "  ")}`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.value.computeCallees(callees);
        this.inexp.computeCallees(callees);
    }
}

class MorphirLetMulti extends MorphirExp {
    readonly assigns: { vname: string, value: MorphirExp }[];
    readonly inexp: MorphirExp

    constructor(assigns: { vname: string, value: MorphirExp }[], inexp: MorphirExp) {
        super();

        this.assigns = assigns;
        this.inexp = inexp;
    }

    emitMorphir(indent: string | undefined): string {
        const binds = this.assigns.map((asgn) => `${cleanVarName(asgn.vname)} = ${asgn.value.emitMorphir(undefined)})`);

        if (indent === undefined) {
            return `(let ${binds.join(" ")} in ${this.inexp.emitMorphir(undefined)})`;
        }
        else {
            return `let ${binds.join(" ")} in\n${indent + "  "}${this.inexp.emitMorphir(indent + "  ")}`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.assigns.forEach((asgn) => {
            asgn.value.computeCallees(callees);
        });
        this.inexp.computeCallees(callees);
    }
}

class MorphirIf extends MorphirExp {
    readonly cond: MorphirExp;
    readonly tval: MorphirExp;
    readonly fval: MorphirExp;

    constructor(cond: MorphirExp, tval: MorphirExp, fval: MorphirExp) {
        super();

        this.cond = cond;
        this.tval = tval;
        this.fval = fval;
    }

    emitMorphir(indent: string | undefined): string {
        if (indent === undefined) {
            return `(if ${this.cond.emitMorphir(undefined)} then ${this.tval.emitMorphir(undefined)} else ${this.fval.emitMorphir(undefined)})`;
        }
        else {
            return `if ${this.cond.emitMorphir(undefined)} then\n${indent + "  "}${this.tval.emitMorphir(indent + "  ")} else\n${indent + "  "}${this.fval.emitMorphir(indent + "  ")}\n${indent}`;
        }
    }

    computeCallees(callees: Set<string>): void {
        this.cond.computeCallees(callees);
        this.tval.computeCallees(callees);
        this.fval.computeCallees(callees);
    }
}

class MorphirCond extends MorphirExp {
    readonly opts: {test: MorphirExp, result: MorphirExp}[];
    readonly orelse: MorphirExp;

    constructor(opts: {test: MorphirExp, result: MorphirExp}[], orelse: MorphirExp) {
        super();

        this.opts = opts;
        this.orelse = orelse;
    }

    emitMorphir(indent: string | undefined): string {
        if (indent === undefined) {
            let iopts: string = this.orelse.emitMorphir(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `(if ${this.opts[i].test.emitMorphir(undefined)} then ${this.opts[i].result.emitMorphir(undefined)} else ${iopts})`
            }
            return iopts;
        }
        else {
            let iopts: string = this.orelse.emitMorphir(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `if ${this.opts[i].test.emitMorphir(undefined)} then\n${indent + "  "}${this.opts[i].result.emitMorphir(indent + "  ")} else\n${indent + "  "}${iopts}\n${indent})`
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
    MorphirMaskConstruct,
    MorphirTypeInfo, MorphirExp, MorphirVar, MorphirConst, 
    MorphirCallSimple, MorphirCallGeneral, MorphirCallGeneralWOptMask, MorphirCallGeneralWPassThroughMask,
    MorphirLet, MorphirLetMulti, MorphirIf, MorphirCond
};

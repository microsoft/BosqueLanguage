//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

abstract class SMTExp {
    abstract bind(sval: SMTExp, svar?: string): SMTExp;
    abstract emit(indent?: string): string;
}

class SMTFreeVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();
        this.vname = vname;
    }

    static generate(name?: string): SMTFreeVar {
        return new SMTFreeVar(`${name || "#body#"}`);
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return svar === undefined || this.vname === svar ? sval : this;
    }

    emit(indent?: string): string {
        return this.vname;
    }
}

class SMTValue extends SMTExp {
    readonly value: string;

    constructor(value: string) {
        super();
        this.value = value;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return this;
    }

    emit(indent?: string): string {
        return this.value;
    }
}

class SMTLet extends SMTExp {
    readonly lname: string;
    readonly exp: SMTExp;
    readonly body: SMTExp;

    constructor(lname: string, exp: SMTExp, body?: SMTExp) {
        super();
        this.lname = lname;
        this.exp = exp;
        this.body = body || SMTFreeVar.generate();
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return new SMTLet(this.lname, this.exp.bind(sval, svar), this.body.bind(sval, svar));
    }

    emit(indent?: string): string {
        if (indent === undefined) {
            return `(let ((${this.lname} ${this.exp.emit()})) ${this.body.emit()})`;
        }
        else {
            return `(let ((${this.lname} ${this.exp.emit()}))\n${indent + "  "}${this.body.emit(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTCond extends SMTExp {
    readonly test: SMTExp;
    readonly iftrue: SMTExp;
    readonly iffalse: SMTExp;

    constructor(test: SMTExp, iftrue: SMTExp, iffalse: SMTExp) {
        super();
        this.test = test;
        this.iftrue = iftrue;
        this.iffalse = iffalse;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return new SMTCond(this.test.bind(sval, svar), this.iftrue.bind(sval, svar), this.iffalse.bind(sval, svar));
    }

    emit(indent?: string): string {
        if (indent === undefined) {
            return `(ite ${this.test.emit()} ${this.iftrue.emit()} ${this.iffalse.emit()})`;
        }
        else {
            return `(ite ${this.test.emit()}\n${indent + "  "}${this.iftrue.emit(indent + "  ")}\n${indent + "  "}${this.iffalse.emit(indent + "  ")}\n${indent})`;
        }
    }
}

export {
    SMTFreeVar, SMTValue, SMTLet, SMTCond, SMTExp
};

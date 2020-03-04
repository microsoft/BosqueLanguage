"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
class SMTExp {
}
exports.SMTExp = SMTExp;
class SMTFreeVar extends SMTExp {
    constructor(vname) {
        super();
        this.vname = vname;
    }
    static generate(name) {
        return new SMTFreeVar(`${name || "#body#"}`);
    }
    bind(sval, svar) {
        return svar === undefined || this.vname === svar ? sval : this;
    }
    emit(indent) {
        return this.vname;
    }
}
exports.SMTFreeVar = SMTFreeVar;
class SMTValue extends SMTExp {
    constructor(value) {
        super();
        this.value = value;
    }
    bind(sval, svar) {
        return this;
    }
    emit(indent) {
        return this.value;
    }
}
exports.SMTValue = SMTValue;
class SMTLet extends SMTExp {
    constructor(lname, exp, body) {
        super();
        this.lname = lname;
        this.exp = exp;
        this.body = body || SMTFreeVar.generate();
    }
    bind(sval, svar) {
        return new SMTLet(this.lname, this.exp.bind(sval, svar), this.body.bind(sval, svar));
    }
    emit(indent) {
        if (indent === undefined) {
            return `(let ((${this.lname} ${this.exp.emit()})) ${this.body.emit()})`;
        }
        else {
            return `(let ((${this.lname} ${this.exp.emit()}))\n${indent + "  "}${this.body.emit(indent + "  ")}\n${indent})`;
        }
    }
}
exports.SMTLet = SMTLet;
class SMTCond extends SMTExp {
    constructor(test, iftrue, iffalse) {
        super();
        this.test = test;
        this.iftrue = iftrue;
        this.iffalse = iffalse;
    }
    bind(sval, svar) {
        return new SMTCond(this.test.bind(sval, svar), this.iftrue.bind(sval, svar), this.iffalse.bind(sval, svar));
    }
    emit(indent) {
        if (indent === undefined) {
            return `(ite ${this.test.emit()} ${this.iftrue.emit()} ${this.iffalse.emit()})`;
        }
        else {
            return `(ite ${this.test.emit()}\n${indent + "  "}${this.iftrue.emit(indent + "  ")}\n${indent + "  "}${this.iffalse.emit(indent + "  ")}\n${indent})`;
        }
    }
}
exports.SMTCond = SMTCond;
//# sourceMappingURL=smt_exp.js.map
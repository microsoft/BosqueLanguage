//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

function notImplemented(of: string): string {
    console.log("Not Implemented -- " + of);
    assert(false);

    return "[NOT IMPLEMENTED]";
}

enum EvalMode {
    Exp,
    ExpStmt,
    Stmt
}

type LetStackEntry = string[];

type CurryStackEntry = {
    op: string;
    isinfix: boolean;
    isdot: boolean;
    iscons: boolean,
    ispredfunctor: boolean,
    revargs: boolean;
    postaction: string | undefined;
    args: string[];
};

const FUNCTION_TAG = "[FUNCTION]";

class Transpiler {
    private scopeStack: LetStackEntry[] = [];
    private opCurryStack: CurryStackEntry[] = [];

    enums: Set<string> = new Set<string>();

    processNameAsFunction(name: string | string[]): string {
        if(typeof(name) === "string") {
            return name[0].toLowerCase() + name.slice(1);
        } 
        else {
            const lname = name[0][0].toLowerCase() + name[0].slice(1);
            return lname + name.slice(1).map((nn) => nn[0].toUpperCase() + nn.slice(1)).join("");
        }
    }

    processNameAsVarOrField(name: string | string[]): string {
        if(typeof(name) === "string") {
            return name[0].toLowerCase() + name.slice(1);
        } 
        else {
            const lname = name[0][0].toLowerCase() + name[0].slice(1);
            return lname + name.slice(1).map((nn) => nn[0].toUpperCase() + nn.slice(1)).join("");
        }
    }

    processNameAsType(name: string | string[]): string {
        if(typeof(name) === "string") {
            return name[0].toUpperCase() + name.slice(1);
        } 
        else {
            return name.map((nn) => nn[0].toUpperCase() + nn.slice(1)).join("");
        }
    }

    processTypeReference(jv: any[]): string {
        const tparams = jv[3];

        const tname = this.processNameAsType(jv[2][2]);
        if (tname === "List") {
            const oftype = this.processType(tparams[0]);
            return `List<${oftype}>`;
        }
        else if(tname === "Map") {
            const ktype = this.processType(tparams[0]);
            const vtype = this.processType(tparams[1]);
            return `Map<${ktype}, ${vtype}>`;
        }
        else if(tname === "Option") {
            const ttype = this.processType(tparams[0]);
            return `Option<${ttype}>`;
        }
        else if(tname === "Result") {
            const errtype = this.processType(tparams[0]);
            const oktype = this.processType(tparams[1]);
            return `Result<${oktype}, ${errtype}>`;
        }
        else {
            return tname;
        }
    }

    processTypeTuple(jv: any[]): string {
        const entries = jv[2].map((ee: any) => {
            return `${this.processType(ee[1])}`;
        });

        return "[" + entries.join(", ") + "]";
    }

    processTypeRecord(jv: any[]): string {
        const entries = jv[2].map((ee: any) => {
            return `${this.processNameAsVarOrField(ee.name)}: ${this.processType(ee.tpe)}`;
        });

        return "{" + entries.join(", ") + "}";
    }

    processType(jv: any[]): string {
        switch(jv[0]) {
            case "Reference":
                return this.processTypeReference(jv);
            case "Tuple":
                return this.processTypeTuple(jv);
            case "Record":
                return this.processTypeRecord(jv);
            default:
                return notImplemented(`processType -- ${jv[0]}`);
        }
    }

    processLiteral(jv: any[]): string {
        const lv = jv[2];
        switch(lv[0]) {
            case "BoolLiteral":
                return lv[1] ? "true" : "false";
            case "CharLiteral":
                return `"${lv[1]}"`;
            case "StringLiteral":
                return `"${lv[1]}"`;
            case "WholeNumberLiteral":
                return `${lv[1]}i`;
            case "FloatLiteral": {
                let fstr = `${lv[1]}`;
                return fstr + (fstr.includes(".") ? "f" : ".0f");
            }
            case "DecimalLiteral": {
                let fstr = `${lv[1]}`;
                return fstr + (fstr.includes(".") ? "d" : ".0d");
            }
            default:
                return notImplemented(`processLiteral -- ${lv[0]}`);
        }
    }

    processConstructor(jv: any[]): string {
        if(jv[1][0] !== "Function") {
            //it is an enum?
            const consname = this.processNameAsType(jv[1][2][2]);
            assert(this.enums.has(consname));

            const ename = this.processNameAsVarOrField(jv[2][2]);
            return `${consname}::${ename}`;
        }
        else {
            const ctype = this.processNameAsType(jv[2][2]);
            
            if(ctype === "Ok") {
                this.opCurryStack.push({ op: "ok", isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
            }
            else if(ctype === "Err") {
                this.opCurryStack.push({ op: "err", isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
            }
            else if(ctype === "Some") {
                this.opCurryStack.push({ op: "some", isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
            }
            else {
                this.opCurryStack.push({ op: ctype, isinfix: false, isdot: false, iscons: true, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
            }

            return FUNCTION_TAG;
        }
    }

    processTuple(jv: any[]): string {
        return notImplemented("processTuple");
    }

    processRecord(jv: any[]): string {
        return notImplemented("processRecord");
    }

    processVariable(jv: any[]): string {
        return this.processNameAsVarOrField(jv[2]);
    }

    processReference(jv: any[]): string {
        if (jv[1][0] !== "Function") {
            return this.processNameAsVarOrField(jv[2][2]);
        }
        else {
            const rr = this.processNameAsFunction(jv[2][2]);

            switch (rr) {
                case "not":
                    this.opCurryStack.push({ op: "!", isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "and":
                    this.opCurryStack.push({ op: "&&", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "or":
                    this.opCurryStack.push({ op: "||", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "negate":
                    this.opCurryStack.push({ op: "-", isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "add":
                    this.opCurryStack.push({ op: "+", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "subtract":
                    this.opCurryStack.push({ op: "-", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "multiply":
                    this.opCurryStack.push({ op: "*", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "divide":
                    this.opCurryStack.push({ op: "/", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "integerDivide":
                    this.opCurryStack.push({ op: "/", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "equal":
                    this.opCurryStack.push({ op: "==", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "notEqual":
                    this.opCurryStack.push({ op: "!=", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "lessThan":
                    this.opCurryStack.push({ op: "<", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "lessThanOrEqual":
                    this.opCurryStack.push({ op: "<=", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "greaterThan":
                    this.opCurryStack.push({ op: ">", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "greaterThanOrEqual":
                    this.opCurryStack.push({ op: ">=", isinfix: true, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "toFloat":
                    this.opCurryStack.push({ op: "toFloat", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "toInt":
                    this.opCurryStack.push({ op: "toInt", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "floor":
                    this.opCurryStack.push({ op: "floor", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: ".toInt()", "args": [] });
                    break;
                case "ceiling":
                    this.opCurryStack.push({ op: "ceiling", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: ".toInt()", "args": [] });
                    break;
                case "truncate":
                    this.opCurryStack.push({ op: "truncate", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: ".toInt()", "args": [] });
                    break;
                case "isEmpty":
                    this.opCurryStack.push({ op: "empty", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                case "length":
                    this.opCurryStack.push({ op: "size", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: ".toInt()", "args": [] });
                    break;
                case "map":
                    this.opCurryStack.push({ op: "map", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: true, postaction: undefined, "args": [] });
                    break;
                case "filter":
                    this.opCurryStack.push({ op: "map", isinfix: false, isdot: true, iscons: false, ispredfunctor: true, revargs: true, postaction: undefined, "args": [] });
                    break;
                case "sum":
                    this.opCurryStack.push({ op: "sum", isinfix: false, isdot: true, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
                default:
                    this.opCurryStack.push({ op: rr, isinfix: false, isdot: false, iscons: false, ispredfunctor: false, revargs: false, postaction: undefined, "args": [] });
                    break;
            }

            return FUNCTION_TAG;
        }
    }

    processField(jv: any[]): string {
        const ee = this.processValue(jv[2], EvalMode.Exp, true);
        const ff = this.processNameAsVarOrField(jv[3]);
        
        return `${ee}.${ff}`;
    }

    processFieldFunction(jv: any[]): string {
        return notImplemented("processFieldFunction");
    }

    processApply(jv: any[], force: boolean): string {
        this.processValue(jv[2], EvalMode.Exp, false);
        const ffunc = this.opCurryStack[this.opCurryStack.length - 1] as CurryStackEntry;

        const vv = this.processValue(jv[3], EvalMode.Exp, true);
        ffunc.args.push(vv);

        if(!force) {
            return FUNCTION_TAG;
        }
        else {
            this.opCurryStack.pop();

            if(ffunc.revargs) {
                ffunc.args = ffunc.args.reverse();
            }

            let op = "";
            if(ffunc.isinfix) {
                //special case for == and != on keytypes
                if(ffunc.op === "==" || ffunc.op === "!=") {
                    const vvtype = this.processTypeReference(jv[3][1]);
                    if(vvtype === "String" || this.enums.has(vvtype)){
                        const newop = ffunc.op === "==" ? "===" : "!==";
                        op = `(${ffunc.args[0]} ${newop} ${ffunc.args[1]})`;
                    }
                    else {
                        op = `(${ffunc.args[0]} ${ffunc.op} ${ffunc.args[1]})`;
                    }
                }
                else {
                    op = `(${ffunc.args[0]} ${ffunc.op} ${ffunc.args[1]})`;
                }
            }
            else if(ffunc.isdot) {
                op = `(${ffunc.args[0]}).${ffunc.op}(${ffunc.args.slice(1).join(", ")})`;
            }
            else if(ffunc.iscons) {
                op = `${ffunc.op}{${ffunc.args.join(", ")}}`;
            }
            else {
                op = `${ffunc.op}(${ffunc.args.join(", ")})`;
            }

            if(ffunc.postaction !== undefined) {
                op = op + ffunc.postaction;
            }

            return op;
        }
    }
    
    processLambda(jv: any[], ispred: boolean): string {
        //const rtype = this.processType(jv[1][3]);
        const vvar = jv[2][3];
        const body = this.processValue(jv[3], EvalMode.Exp, true);
        
        return `${ispred ? "pred" : "fn"}(${vvar}) => ${body}`;
    }

    processLet(jv: any[], mode: EvalMode, indent?: string): string {
        //get count of current scope (we want to know if this is the first let)
        const cscope = this.scopeStack[this.scopeStack.length - 1];
        const toplevel = cscope.length === 0;

        //get var + value assign
        const vname = this.processNameAsVarOrField(jv[2]);
        const vvalue = this.processValue(jv[3].body, EvalMode.Exp, true);

        //push onto current scope list
        cscope.push(`let ${vname} = ${vvalue};`);

        //compute in value
        //if this was the first let entry (then we need to make a block structure statment -- either yield or return)
        //otherwise just return the value -- with no indent
        const escope = mode === EvalMode.Stmt ? EvalMode.Stmt : EvalMode.ExpStmt;
        const exp = this.processValue(jv[4], escope, true, indent);

        if (toplevel) {
            const rindent = (indent || "");
            if (escope === EvalMode.Stmt) {
                const lets = cscope.join(`\n${indent}`);
                return `${rindent}${lets}\n${exp}`;
            }
            else {
                const lets = cscope.join(`\n${indent}`);
                return `{|\n${rindent}${lets}\n${exp}\n${rindent}|}`;
            }
        }
        else {
            return exp;
        }
    }

    processLetRec(jv: any[], mode: EvalMode, indent?: string): string {
        return notImplemented("processLetRec");
    }
    
    processDestructure(jv: any[], mode: EvalMode, indent?: string): string {
        return notImplemented("processDestructure");
    }
    
    processIfThenElse(jv: any[], mode: EvalMode, indent?: string): string {
        const nindent = indent !== undefined ? (indent + "    ") : undefined;

        const test = this.processValue(jv[2], EvalMode.Exp, true);

        this.scopeStack.push([]);
        const tval = this.processValue(jv[3], mode !== EvalMode.Stmt ? EvalMode.Exp : EvalMode.Stmt, true, nindent);
        this.scopeStack.pop();

        this.scopeStack.push([]);
        const fval = this.processValue(jv[4], mode !== EvalMode.Stmt ? EvalMode.Exp : EvalMode.Stmt, true, nindent);
        this.scopeStack.pop();

        const rindent = (indent || "");
        if(mode === EvalMode.Stmt) {
            return `${rindent}if (${test}) {\n${tval}\n${rindent}}\n${rindent}else {\n${fval}\n${rindent}}`;
        }
        else {
            const sep = indent !== undefined ? "\n" : " ";
            const ee = `${sep}if (${test})${sep}${tval}${sep}else${sep}${fval}`;
            if(mode === EvalMode.Exp) {
                return rindent + ee;
            }
            else {
                return rindent + `yield ${ee};`;
            }
        }
    }

    processPatternMatch(jv: any[], mode: EvalMode, indent?: string): string {
        return notImplemented("processPatternMatch");
    }

    processUpdateRecord(jv: any[]): string {
        return notImplemented("processUpdateRecord");
    }

    processResultActionForValue(mode: EvalMode, value: string, indent?: string): string {
        const idtstr = indent || "";

        if(mode === EvalMode.Stmt) {
            return `${idtstr}return ${value};`;
        }
        else if(mode === EvalMode.ExpStmt) {
            return `${idtstr}yield ${value};`;
        }
        else {
            return `${idtstr}${value}`;
        }
    }

    processValue(v: any[], mode: EvalMode, force: boolean, indent?: string): string {
        switch(v[0]) {
            case "literal":
                return this.processResultActionForValue(mode, this.processLiteral(v), indent);
            case "constructor":
                return this.processResultActionForValue(mode, this.processConstructor(v), indent);
            case "tuple":
                return this.processResultActionForValue(mode, this.processTuple(v), indent);
            case "record":
                return this.processResultActionForValue(mode, this.processRecord(v), indent);
            case "variable":
                return this.processResultActionForValue(mode, this.processVariable(v), indent);
            case "reference":
                return this.processResultActionForValue(mode, this.processReference(v), indent);
            case "field":
                return this.processResultActionForValue(mode, this.processField(v), indent);
            case "field_function":
                return this.processResultActionForValue(mode, this.processFieldFunction(v), indent);
            case "apply":
                return this.processResultActionForValue(mode, this.processApply(v, force), indent);
            case "lambda":
                assert(mode === EvalMode.Exp);
                return this.processLambda(v, this.opCurryStack[this.opCurryStack.length].ispredfunctor);
            case "let_definition":
                return this.processLet(v, mode, indent);
            case "let_recursion":
                return this.processLetRec(v, mode, indent);
            case "destructure":
                return this.processDestructure(v, mode, indent);
            case "if_then_else":
                return this.processIfThenElse(v, mode, indent);
            case "pattern_match":
                return this.processPatternMatch(v, mode, indent);
            case "update_record":
                return this.processResultActionForValue(mode, this.processUpdateRecord(v), indent);
            default:
                notImplemented("processValue");
                return "[NOT IMPLEMENTED]"
        }
    }

    processFunctionDef(name: string, jv: any): string {
        const args = jv.inputTypes.map((arg: any) => {
            const vv = this.processNameAsVarOrField(arg[0]);
            const tt = this.processType(arg[1])

            return `${vv}: ${tt}`;
        });

        const result = this.processType(jv.outputType);

        this.scopeStack.push([]);
        const body = this.processValue(jv.body, EvalMode.Stmt, true, "    ");
        this.scopeStack.pop();

        return `${name === "main" ? "entrypoint " : ""}function ${name}(${args.join(", ")}): ${result} {\n` 
        + body + "\n"
        + "}";
    }
}

function loadMainModule(jv: any): string {
    const jconv: Transpiler = new Transpiler();

    const ddecls = jv.distribution[3].modules.map((mm: any) => {
        const mdef = mm[1].value;
        const mdecls: string[] = mdef.types.map((vv: any) => {
            const name = jconv.processNameAsType(vv[0]);
            //console.log(`Processing Type ${name}...`);

            const declkind: string = vv[1].value.value[0];
            const vvdata = vv[1].value.value[2];
            switch(declkind) {
                case "TypeAliasDefinition": {
                    const oftype = jconv.processType(vvdata);
                    return `typedef ${name} = ${oftype};`; 
                }
                case "CustomTypeDefinition": {
                    if (vvdata.value.every((dd: any[]) => dd[1].length === 0)) {
                        //it is an enum
                        jconv.enums.add(name);

                        const enames = vvdata.value.map((ev: any[]) => jconv.processNameAsVarOrField(ev[0])).join(",\n    ");
                        return `enum ${name} {\n    ${enames}\n}`;
                    }
                    else {
                        //it is a real ADT
                        assert(false, "adt decl");
                    }
                }
                default: {
                    assert(false, "type decl");
                }
            }
        });

        return mdecls;
    });

    const cdecls = jv.distribution[3].modules.map((mm: any) => {
        const mdef = mm[1].value;
        const mdecls: string[] = mdef.values.map((vv: any) => {
            const name = jconv.processNameAsFunction(vv[0]);
            //console.log(`Processing Function ${name}...`);

            return jconv.processFunctionDef(name, vv[1].value.value);
        });

        return mdecls;
    });

    const tdecls = ([] as string[]).concat(...ddecls);
    const fdecls = ([] as string[]).concat(...cdecls);
    return "namespace Main;\n\n" + tdecls.join("\n\n") + "\n\n" + fdecls.join("\n\n")
}

function transpile(jv: object): string {
    return loadMainModule(jv);
}

export {
    transpile
};

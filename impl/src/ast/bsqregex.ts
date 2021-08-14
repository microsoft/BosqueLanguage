//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

class RegexParser {
    readonly restr: string;
    pos: number;

    constructor(restr: string) {
        this.restr = restr;
        this.pos = 0;
    }

    private done(): boolean {
        return this.restr.length <= this.pos;
    }

    private isToken(tk: string): boolean {
        return this.restr[this.pos] === tk;
    }

    private token(): string {
        return this.restr[this.pos];
    }

    private advance(dist?: number) {
        this.pos = this.pos + (dist !== undefined ? dist : 1);
    }

    private parseBaseComponent(): RegexComponent | string {
        let res: RegexComponent | string;
        if(this.isToken("(")) {
            this.advance();

            res = this.parseComponent();
            if(!this.isToken(")")) {
                return "Un-matched paren";
            }

            this.advance();
        }
        else if(this.isToken("[")) {
            this.advance();

            const lb = this.token();
            this.advance();

            if(!this.isToken("-")) {
                return "Invalid range given";
            }
            else {
                this.advance();
            }

            const ub = this.token();
            this.advance();

            if(!this.isToken("]")) {
                return "Invalid range given";
            }
            this.advance();

            return new CharRange(lb.codePointAt(0) as number, ub.codePointAt(0) as number);
        }
        else {
            res = new Literal(this.token(), this.token(), this.token());
            this.advance();
        }

        return res;
    }

    private parseCharClassOrEscapeComponent(): RegexComponent | string {
        if(this.isToken(".")) {
            return new CharClass(SpecialCharKind.Wildcard);
        }
        else if(this.isToken("\\")) {
            this.advance();
            if(this.isToken("\\") || this.isToken("/") 
                || this.isToken(".") || this.isToken("*") || this.isToken("+") || this.isToken("?") || this.isToken("|")
                || this.isToken("(") || this.isToken(")") || this.isToken("[") || this.isToken("]") || this.isToken("{") || this.isToken("}")
                || this.isToken("$") || this.isToken("^")) {
                const cc = this.token();
                this.advance();

                return new Literal(`\\${cc}`, cc, cc);
            }
            else if(this.isToken("n") || this.isToken("r") || this.isToken("t")) {
                const cc = this.token();
                this.advance();

                let rc = "";
                if(cc == "n") {
                    rc = "\n";
                }
                else if(cc == "r") {
                    rc = "\r";
                }
                else {
                    rc = "\t";
                }

                return new Literal(`\\${cc}`, `\\${cc}`, rc);
            }
            else {
                if(!this.isToken("p")) {
                    return "Ill formed character class";
                }
                this.advance();
                if(!this.isToken("{")) {
                    return "Ill formed character class";
                }
                this.advance();

                let res: RegexComponent | string = "Ill formed character class";
                if(this.isToken("Z")) {
                    res = new CharClass(SpecialCharKind.WhiteSpace);
                    this.advance();
                }
                else {
                    res = "Ill formed character class";
                }

                if(!this.isToken("}")) {
                    return "Ill formed character class";
                }
                this.advance();

                return res;
            }
        }
        else {
            return this.parseBaseComponent();
        }
    }

    private parseRepeatComponent(): RegexComponent | string {
        let rcc = this.parseCharClassOrEscapeComponent();
        if(typeof(rcc) === "string") {
            return rcc;
        }

        while(this.isToken("*") || this.isToken("+") || this.isToken("?") || this.isToken("{")) {
            if(this.isToken("*")) {
                rcc = new StarRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("+")) {
                rcc = new PlusRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("?")) {
                rcc = new Optional(rcc);
                this.advance();
            }
            else {
                this.advance();
                let nre = new RegExp(/[0-9]+/, "y");
                nre.lastIndex = this.pos;

                const nmin = nre.exec(this.restr);
                if(nmin === null) {
                    return "Invalid number";
                }
                this.advance(nmin[0].length);

                const min = Number.parseInt(nmin[0]);
                let max = min;
                if (this.isToken(",")) {
                    this.advance();
                    nre.lastIndex = this.pos;

                    const nmax = nre.exec(this.restr);
                    if (nmax === null) {
                        return "Invalid number";
                    }
                    this.advance(nmax[0].length);

                    max = Number.parseInt(nmax[0]);
                }

                if(!this.isToken("}")) {
                    return "Un-matched paren";
                }
                this.advance();

                rcc = new RangeRepeat(rcc, min, max);
            }
        }   

        return rcc;
    }

    private parseSequenceComponent(): RegexComponent | string {
        let sre: RegexComponent[] = [];

        while(!this.done() && !this.isToken("|") && !this.isToken(")")) {
            const rpe = this.parseRepeatComponent();
            if(typeof(rpe) === "string") {
                return rpe;
            }

            if(sre.length === 0) {
                sre.push(rpe);
            }
            else {
                const lcc = sre[sre.length - 1];
                if(lcc instanceof Literal && rpe instanceof Literal) {
                    sre[sre.length - 1] = Literal.mergeLiterals(lcc, rpe);
                }
                else {
                    sre.push(rpe);
                }
            }
        }

        if(sre.length === 0) {
            return "Malformed regex";
        }

        if (sre.length === 1) {
            return sre[0];
        }
        else {
            return new Sequence(sre);
        }
    }

    private parseAlternationComponent(): RegexComponent | string {
        const rpei = this.parseSequenceComponent();
        if (typeof (rpei) === "string") {
            return rpei;
        }

        let are: RegexComponent[] = [rpei];

        while (!this.done() && this.isToken("|")) {
            this.advance();
            const rpe = this.parseSequenceComponent();
            if (typeof (rpe) === "string") {
                return rpe;
            }

            are.push(rpe);
        }

        if(are.length === 1) {
            return are[0];
        }
        else {
            return new Alternation(are);
        }
    }

    parseComponent(): RegexComponent | string {
        return this.parseAlternationComponent();
    }
}

class BSQRegex {
    readonly restr: string;
    readonly re: RegexComponent;

    constructor(restr: string, re: RegexComponent) {
        this.restr = restr;
        this.re = re;
    }

    compileToJS(): string {
        return "$" + this.re.compileToJS() + "^";
    }

    compileToPatternToSMT(ascii: boolean): string {
        return this.re.compilePatternToSMT(ascii);
    }

    static parse(rstr: string): BSQRegex | string {
        const reparser = new RegexParser(rstr.substr(1, rstr.length - 2));
        const rep = reparser.parseComponent();
       
        if(typeof(rep) === "string") {
            return rep;
        }
        else {
            return new BSQRegex(rstr, rep);
        }
    }

    jemit(): any {
        return { restr: this.restr, re: this.re.jemit() };
    }

    static jparse(obj: any): BSQRegex {
        return new BSQRegex(obj.restr, RegexComponent.jparse(obj.re));
    }
}

abstract class RegexComponent {
    useParens(): boolean {
        return false;
    }

    abstract jemit(): any;

    abstract compileToJS(): string;
    abstract compilePatternToSMT(ascii: boolean): string;

    static jparse(obj: any): RegexComponent {
        const tag = obj.tag;
        switch (tag) {
            case "Literal":
                return Literal.jparse(obj);
            case "CharClass":
                return CharClass.jparse(obj);
            case "CharRange":
                return CharRange.jparse(obj);
            case "StarRepeat":
                return StarRepeat.jparse(obj);
            case "PlusRepeat":
                return PlusRepeat.jparse(obj);
            case "RangeRepeat":
                return RangeRepeat.jparse(obj);
            case "Optional":
                return Optional.jparse(obj);
            case "Alternation":
                return Alternation.jparse(obj);
            default:
                return Sequence.jparse(obj);
        }
    }
}

class Literal extends RegexComponent {
    readonly restr: string;
    readonly escstr: string;
    readonly litstr: string;

    constructor(restr: string, escstr: string, litstr: string) {
        super();

        this.restr = restr;
        this.escstr = escstr;
        this.litstr = litstr;
    }

    jemit(): any {
        return {tag: "Literal", restr: this.restr, escstr: this.escstr, litstr: this.litstr};
    }

    static jparse(obj: any): RegexComponent {
        return new Literal(obj.restr, obj.escstr, obj.litstr);
    }

    static mergeLiterals(l1: Literal, l2: Literal): Literal {
        return new Literal(l1.restr + l2.restr, l1.escstr + l2.escstr, l1.litstr + l2.litstr);
    }

    compileToJS(): string {
        return this.restr;
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(ascii);

        return `(str.to.re "${this.escstr}")`;
    }
}

class CharRange extends RegexComponent {
    readonly lb: number;
    readonly ub: number;

    constructor(lb: number, ub: number) {
        super();

        this.lb = lb;
        this.ub = ub;
    }

    jemit(): any {
        return { tag: "CharRange", lb: this.lb, ub: this.ub };
    }

    static jparse(obj: any): RegexComponent {
        return new CharRange(obj.lb, obj.ub);
    }

    compileToJS(): string {
        return `[${this.lb}-${this.ub}]`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(ascii);

        return `(re.range \"${this.lb}\" \"${this.ub}\")`;
    }
}

class CharClass extends RegexComponent {
    readonly kind: SpecialCharKind;

    constructor(kind: SpecialCharKind) {
        super();

        this.kind = kind;
    }

    jemit(): any {
        return { tag: "CharClass", kind: this.kind };
    }

    static jparse(obj: any): RegexComponent {
        return new CharClass(obj.kind);
    }

    compileToJS(): string {
        switch (this.kind) {
            case SpecialCharKind.WhiteSpace:
                return "\\p{Z}";
            default:
                return ".";
        }
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(ascii);
        
        switch (this.kind) {
            case SpecialCharKind.WhiteSpace:
                return "(re.union (str.to.re \" \") (str.to.re \"\\t\") (str.to.re \"\\n\") (str.to.re \"\\r\"))";
            default:
                return "re.allchar";
        }
    }
}

class StarRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return { tag: "StarRepeat", repeat: this.repeat.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new StarRepeat(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})*` : `${this.repeat.compileToJS()}*`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.* ${this.repeat.compilePatternToSMT(ascii)})`;
    }
}

class PlusRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return { tag: "PlusRepeat", repeat: this.repeat.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new PlusRepeat(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})+` : `${this.repeat.compileToJS()}+`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.+ ${this.repeat.compilePatternToSMT(ascii)})`;
    }
}

class RangeRepeat extends RegexComponent {
    readonly repeat: RegexComponent;
    readonly min: number;
    readonly max: number;

    constructor(repeat: RegexComponent, min: number, max: number) {
        super();

        this.repeat = repeat;
        this.min = min;
        this.max = max;
    }

    jemit(): any {
        return { tag: "RangeRepeat", repeat: this.repeat.jemit(), min: this.min, max: this.max };
    }

    static jparse(obj: any): RegexComponent {
        return new RangeRepeat(RegexComponent.jparse(obj.repeat), obj.min, obj.max);
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()}){${this.min},${this.max}}` : `${this.repeat.compileToJS()}{${this.min},${this.max}}`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.loop ${this.repeat.compilePatternToSMT(ascii)} ${this.min} ${this.max})`;
    }
}

class Optional extends RegexComponent {
    readonly opt: RegexComponent;

    constructor(opt: RegexComponent) {
        super();

        this.opt = opt;
    }

    jemit(): any {
        return { tag: "Optional", opt: this.opt.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new Optional(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.opt.useParens() ? `(${this.opt.compileToJS()})?` : `${this.opt.compileToJS()}?`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.opt ${this.opt.compilePatternToSMT(ascii)})`;
    }
}

class Alternation extends RegexComponent {
    readonly opts: RegexComponent[];

    constructor(opts: RegexComponent[]) {
        super();

        this.opts = opts;
    }

    useParens(): boolean {
        return true;
    }

    jemit(): any {
        return { tag: "Alternation", opts: this.opts.map((opt) => opt.jemit()) };
    }

    static jparse(obj: any): RegexComponent {
        return new Alternation(obj.opts.map((opt: any) => RegexComponent.jparse(opt)));
    }

    compileToJS(): string {
        return this.opts.map((opt) => opt.compileToJS()).join("|");
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.union ${this.opts.map((opt) => opt.compilePatternToSMT(ascii)).join(" ")})`;
    }
}

class Sequence extends RegexComponent {
    readonly elems: RegexComponent[];

    constructor(elems: RegexComponent[]) {
        super();

        this.elems = elems;
    }

    useParens(): boolean {
        return true;
    }

    jemit(): any {
        return { tag: "Sequence", elems: this.elems.map((elem) => elem.jemit()) };
    }

    static jparse(obj: any): RegexComponent {
        return new Sequence(obj.elems.map((elem: any) => RegexComponent.jparse(elem)));
    }

    compileToJS(): string {
        return this.elems.map((elem) => elem.compileToJS()).join("");
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.++ ${this.elems.map((elem) => elem.compilePatternToSMT(ascii)).join(" ")})`;
    }
}

export {
    BSQRegex
};

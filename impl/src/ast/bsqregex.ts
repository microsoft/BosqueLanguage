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

            const compliment = this.isToken("^")
            if(compliment) {
                this.advance();
            }

            let range: {lb: number, ub: number}[] = [];
            while(!this.isToken("]")) {
                const lb = this.token();
                this.advance();

                if (!this.isToken("-")) {
                    range.push({ lb: lb.codePointAt(0) as number, ub: lb.codePointAt(0) as number });
                }
                else {
                    this.advance();

                    const ub = this.token();
                    this.advance();

                    range.push({ lb: lb.codePointAt(0) as number, ub: ub.codePointAt(0) as number });
                }
            }

            if(!this.isToken("]")) {
                return "Invalid range given";
            }
            this.advance();

            return new RegexCharRange(compliment, range);
        }
        else if(this.isToken("{")) {
            this.advance();

            let fname = "";
            while(!this.isToken("}")) {
                fname += this.token();
                this.advance();
            }

            if(!this.isToken("}")) {
                return "Invalid range given";
            }
            this.advance();

            let ccpos = fname.indexOf("::");

            let ns = ccpos === -1 ? "NSCore" : fname.slice(0, ccpos);
            let ccname = ccpos === -1 ? fname : fname.slice(ccpos + 3);

            return new RegexConstClass(ns, ccname);            
        }
        else {
            res = new RegexLiteral(this.token(), this.token(), this.token());
            this.advance();
        }

        return res;
    }

    private parseCharClassOrEscapeComponent(): RegexComponent | string {
        if(this.isToken(".")) {
            return new RegexDotCharClass();
        }
        else if(this.isToken("\\")) {
            this.advance();
            if(this.isToken("\\") || this.isToken("/") 
                || this.isToken(".") || this.isToken("*") || this.isToken("+") || this.isToken("?") || this.isToken("|")
                || this.isToken("(") || this.isToken(")") || this.isToken("[") || this.isToken("]") || this.isToken("{") || this.isToken("}")
                || this.isToken("$") || this.isToken("^")) {
                const cc = this.token();
                this.advance();

                return new RegexLiteral(`\\${cc}`, cc, cc);
            }
            else {
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

                return new RegexLiteral(`\\${cc}`, `\\${cc}`, rc);
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
                rcc = new RegexStarRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("+")) {
                rcc = new RegexPlusRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("?")) {
                rcc = new RegexOptional(rcc);
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

                rcc = new RegexRangeRepeat(rcc, min, max);
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
                if(lcc instanceof RegexLiteral && rpe instanceof RegexLiteral) {
                    sre[sre.length - 1] = RegexLiteral.mergeLiterals(lcc, rpe);
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
            return new RegexSequence(sre);
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
            return new RegexAlternation(are);
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
        //
        //TODO: we actually have NFA semantics for our regex -- JS matching is a subset so we need to replace this!!!
        //
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
                return RegexLiteral.jparse(obj);
            case "CharRange":
                return RegexCharRange.jparse(obj);
            case "DotCharClass":
                return RegexDotCharClass.jparse(obj);
            case "ConstRegexClass":
                return RegexConstClass.jparse(obj);
            case "StarRepeat":
                return RegexStarRepeat.jparse(obj);
            case "PlusRepeat":
                return RegexPlusRepeat.jparse(obj);
            case "RangeRepeat":
                return RegexRangeRepeat.jparse(obj);
            case "Optional":
                return RegexOptional.jparse(obj);
            case "Alternation":
                return RegexAlternation.jparse(obj);
            default:
                return RegexSequence.jparse(obj);
        }
    }
}

class RegexLiteral extends RegexComponent {
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
        return new RegexLiteral(obj.restr, obj.escstr, obj.litstr);
    }

    static mergeLiterals(l1: RegexLiteral, l2: RegexLiteral): RegexLiteral {
        return new RegexLiteral(l1.restr + l2.restr, l1.escstr + l2.escstr, l1.litstr + l2.litstr);
    }

    compileToJS(): string {
        return this.restr;
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(ascii);

        return `(str.to.re "${this.escstr}")`;
    }
}

class RegexCharRange extends RegexComponent {
    readonly compliment: boolean;
    readonly range: {lb: number, ub: number}[];

    constructor(compliment: boolean, range: {lb: number, ub: number}[]) {
        super();

        assert(range.length !== 0);

        this.compliment = compliment;
        this.range = range;
    }

    jemit(): any {
        return { tag: "CharRange", compliment: this.compliment, range: this.range };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexCharRange(obj.compliment, obj.range);
    }

    private static valToSStr(cc: number): string {
        assert(cc >= 9);

        if(cc === 9) {
            return "\\t";
        }
        else if (cc === 10) {
            return "\\n";
        }
        else if (cc === 13) {
            return "\\r";
        }
        else {
            return String.fromCodePoint(cc);
        }
    }

    compileToJS(): string {
        //
        //TODO: probably need to do some escaping here as well
        //
        const rng = this.range.map((rr) => (rr.lb == rr.ub) ? RegexCharRange.valToSStr(rr.lb) : `${RegexCharRange.valToSStr(rr.lb)}-${RegexCharRange.valToSStr(rr.ub)}`);
        return `[${this.compliment ? "^" : ""}${rng.join("")}]`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(ascii);
        assert(!this.compliment);
        //
        //TODO: probably need to do some escaping here as well
        //
        const rng = this.range.map((rr) => (rr.lb == rr.ub) ? `(str.to.re "${RegexCharRange.valToSStr(rr.lb)}")` : `(re.range "${RegexCharRange.valToSStr(rr.lb)}" "${RegexCharRange.valToSStr(rr.ub)}")`);
        if(rng.length === 1) {
            return rng[0];
        }
        else {
            return `(re.union ${rng.join(" ")})`; 
        }
    }
}

class RegexDotCharClass extends RegexComponent {
    constructor() {
        super();
    }

    jemit(): any {
        return { tag: "DotCharClass" };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexDotCharClass();
    }

    compileToJS(): string {
        return ".";
    }

    compilePatternToSMT(ascii: boolean): string  {
        return "re.allchar";
    }
}

class RegexConstClass extends RegexComponent {
    readonly ns: string;
    readonly ccname: string;

    constructor(ns: string, ccname: string) {
        super();

        this.ns = ns;
        this.ccname = ccname;
    }

    jemit(): any {
        return { tag: "ConstRegexClass", ns: this.ns, ccname: this.ccname };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexConstClass(obj.ns, obj.ccname);
    }

    compileToJS(): string {
        assert(false, `Should be replaced by const ${this.ns}::${this.ccname}`);
        return `${this.ns}::${this.ccname}`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        assert(false, `Should be replaced by const ${this.ns}::${this.ccname}`);
        return `${this.ns}::${this.ccname}`;
    }
}

class RegexStarRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return { tag: "StarRepeat", repeat: this.repeat.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexStarRepeat(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})*` : `${this.repeat.compileToJS()}*`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.* ${this.repeat.compilePatternToSMT(ascii)})`;
    }
}

class RegexPlusRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return { tag: "PlusRepeat", repeat: this.repeat.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexPlusRepeat(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})+` : `${this.repeat.compileToJS()}+`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.+ ${this.repeat.compilePatternToSMT(ascii)})`;
    }
}

class RegexRangeRepeat extends RegexComponent {
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
        return new RegexRangeRepeat(RegexComponent.jparse(obj.repeat), obj.min, obj.max);
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()}){${this.min},${this.max}}` : `${this.repeat.compileToJS()}{${this.min},${this.max}}`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.loop ${this.repeat.compilePatternToSMT(ascii)} ${this.min} ${this.max})`;
    }
}

class RegexOptional extends RegexComponent {
    readonly opt: RegexComponent;

    constructor(opt: RegexComponent) {
        super();

        this.opt = opt;
    }

    jemit(): any {
        return { tag: "Optional", opt: this.opt.jemit() };
    }

    static jparse(obj: any): RegexComponent {
        return new RegexOptional(RegexComponent.jparse(obj.repeat));
    }

    compileToJS(): string {
        return this.opt.useParens() ? `(${this.opt.compileToJS()})?` : `${this.opt.compileToJS()}?`;
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.opt ${this.opt.compilePatternToSMT(ascii)})`;
    }
}

class RegexAlternation extends RegexComponent {
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
        return new RegexAlternation(obj.opts.map((opt: any) => RegexComponent.jparse(opt)));
    }

    compileToJS(): string {
        return this.opts.map((opt) => opt.compileToJS()).join("|");
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.union ${this.opts.map((opt) => opt.compilePatternToSMT(ascii)).join(" ")})`;
    }
}

class RegexSequence extends RegexComponent {
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
        return new RegexSequence(obj.elems.map((elem: any) => RegexComponent.jparse(elem)));
    }

    compileToJS(): string {
        return this.elems.map((elem) => elem.compileToJS()).join("");
    }

    compilePatternToSMT(ascii: boolean): string  {
        return `(re.++ ${this.elems.map((elem) => elem.compilePatternToSMT(ascii)).join(" ")})`;
    }
}

export {
    BSQRegex,
    RegexComponent,
    RegexLiteral, RegexCharRange, RegexDotCharClass, RegexConstClass, RegexStarRepeat, RegexPlusRepeat, RegexRangeRepeat, RegexOptional, RegexAlternation, RegexSequence
};

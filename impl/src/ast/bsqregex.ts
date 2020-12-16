//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

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
        else {
            res = new LiteralChar(this.token());
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

                return new LiteralChar(cc);
            }
            else if(this.isToken("n") || this.isToken("t")) {
                const cc = this.token();
                this.advance();

                return new LiteralChar("\\" + cc);
            }
            else {
                if(!this.isToken("p{")) {
                    return "Ill formed character class";
                }

                this.advance(2);
                let isneg = this.isToken("!");
                if(isneg) {
                    this.advance();
                }

                let res: RegexComponent | string = "Ill formed character class";
                if(this.isToken("L")) {
                    res = new CharClass(isneg ? SpecialCharKind.NotLetter : SpecialCharKind.Letter);
                }
                else if(this.isToken("N")) {
                    res = new CharClass(isneg ? SpecialCharKind.NotNumber : SpecialCharKind.Number);
                }
                else if(this.isToken("Z")) {
                    res = new CharClass(isneg ? SpecialCharKind.NotWhiteSpace : SpecialCharKind.WhiteSpace);
                }
                else {
                    res = "Ill formed character class";
                }

                if(!this.isToken("}")) {
                    return "Ill formed character class";
                }

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
            }
            else if(this.isToken("+")) {
                rcc = new PlusRepeat(rcc);
            }
            else if(this.isToken("?")) {
                rcc = new Optional(rcc);
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

        while(!this.done() && !this.isToken("|")) {
            const rpe = this.parseRepeatComponent();
            if(typeof(rpe) === "string") {
                return rpe;
            }

            sre.push(rpe);
        }

        if(sre.length === 0) {
            return "Malformed regex";
        }

        return new Sequence(sre);
    }

    private parseAlternationComponent(): RegexComponent | string {
        const rpei = this.parseSequenceComponent();
        if (typeof (rpei) === "string") {
            return rpei;
        }

        let are: RegexComponent[] = [rpei];

        while (!this.done() && this.isToken("|")) {
            const rpe = this.parseSequenceComponent();
            if (typeof (rpe) === "string") {
                return rpe;
            }

            are.push(rpe);
        }

        return new Alternation(are);
    }

    parseComponent(): RegexComponent | string {
        return this.parseAlternationComponent();
    }
}

class BSQRegex {
    readonly restr: string;
    readonly isAnchorStart: boolean;
    readonly isAnchorEnd: boolean;
    readonly re: RegexComponent;

    constructor(restr: string, isAnchorStart: boolean, isAnchorEnd: boolean, re: RegexComponent) {
        this.restr = restr;
        this.isAnchorStart = isAnchorStart;
        this.isAnchorEnd = isAnchorEnd;
        this.re = re;
    }

    compileToJS(): string {
        return (this.isAnchorStart ? "$" : "") + this.re.compileToJS() + (this.isAnchorEnd ? "^" : "");
    }

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string {
        return "[TODO]";
    }

    static parse(rstr: string): BSQRegex | string {
        const isAnchorFront = rstr.startsWith("/$");
        let tfront = 1;
        if(isAnchorFront) {
            tfront++;
        }

        const isAnchorEnd = rstr.endsWith("^/");
        let tend = 1;
        if(isAnchorEnd) {
            tend++;
        }

        const reparser = new RegexParser(rstr.substr(tfront, rstr.length - (tfront + tend)));
        const rep = reparser.parseComponent();

        if(typeof(rep) === "string") {
            return rep;
        }
        else {
            return new BSQRegex(rstr, isAnchorFront, isAnchorEnd, rep);
        }
    }

    jemit(): any {
        return { restr: this.restr, isAnchorStart: this.isAnchorStart, isAnchorEnd: this.isAnchorEnd, re: this.re.jemit() };
    }

    static jparse(obj: any): BSQRegex {
        return new BSQRegex(obj.restr, obj.isAnchorStart, obj.isAnchorEnd, RegexComponent.jparse(obj.re));
    }
}

enum SpecialCharKind {
    Wildcard = "Wildcard",
    WhiteSpace = "WhiteSpace",
    Number = "Number",
    Letter = "Letter",
    NotWhiteSpace = "NotWhiteSpace",
    NotNumber = "NotNumber",
    NotLetter = "NotLetter",
}

abstract class RegexComponent {
    useParens(): boolean {
        return false;
    }

    abstract jemit(): any;

    abstract compileToJS(): string;
    abstract compileToCPP(): string;
    abstract compileToSMT(): string;

    static jparse(obj: any): RegexComponent {
        if(typeof(obj) === "string") {
            return LiteralChar.jparse(obj);
        }
        else {
            const tag = obj.tag;
            switch (tag) {
                case "CharClass":
                    return CharClass.jparse(obj);
                case "StarRepeat":
                    return StarRepeat.jparse(obj);
                case "PlusRepeat":
                    return PlusRepeat.jparse(obj);
                case "RangeRepeat":
                    return RangeRepeat.jparse(obj);
                case "Optional":
                    return Optional.jparse(obj);
                case "Alternation":
                    return Optional.jparse(obj);
                default:
                    return Sequence.jparse(obj);
            }
        }
    }
}

class LiteralChar extends RegexComponent {
    readonly charval: string;

    static escapechars = ["\\", "/", ".", "*", "+", "?", "|", "(", ")", "[", "]", "{", "}", "$", "^"];

    constructor(charval: string) {
        super();

        this.charval = charval;
    }

    jemit(): any {
        return this.charval;
    }

    static jparse(obj: any): RegexComponent {
        return new LiteralChar(obj);
    }

    compileToJS(): string {
        if (LiteralChar.escapechars.includes(this.charval)) {
            return "\\" + this.charval;
        }
        else {
            return this.charval;
        }
    }

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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
                return "\p{Z}";
            case SpecialCharKind.NotWhiteSpace:
                return "[^\p{Z}]";
            case SpecialCharKind.Number:
                return "\p{N}";
            case SpecialCharKind.NotNumber:
                return "[^\p{N}]";
            case SpecialCharKind.Letter:
                return "\p{L}";
            case SpecialCharKind.NotLetter:
                return "[^\p{L}]";
            default:
                return ".";
        }
    }

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
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

    compileToCPP(): string {
        return "[TODO]";
    }

    compileToSMT(): string  {
        return "[TODO]";
    }
}

export {
    BSQRegex
};

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

class BSQRegex {
    readonly restr: string;

    constructor(restr: string) {
        this.restr = restr;
    }

    compileToJS(): string {
        return this.restr.substring(1, this.restr.length - 1);
    }

    compileToCPP(): string {
        return "[INVALID]";
    }

    compileToSMT(): string {
        return "[INVALID]";
    }

    static parse(rstr: string): BSQRegex | string {
        //TODO: parse the regex string here as a (mostly) posix ERE with unicode support
        //https://www.boost.org/doc/libs/1_73_0/libs/regex/doc/html/boost_regex/syntax/basic_extended.html
        //https://stackoverflow.com/questions/32572555/regex-match-unicode-punctuation-category-c
        //https://unicodebook.readthedocs.io/unicode.html

        return new BSQRegex(rstr);
    }

    jemit(): any {
        return {restr: this.restr};
    }

    static jparse(obj: any): BSQRegex {
        return BSQRegex.parse(obj.restr) as BSQRegex;
    }
}

export {
    BSQRegex
};

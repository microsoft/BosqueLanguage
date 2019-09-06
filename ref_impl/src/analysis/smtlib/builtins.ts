//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRInvokePrimitiveDecl, MIRType, MIREntityType, MIREntityTypeDecl, MIRPCode, MIRFunctionParameter } from "../../compiler/mir_assembly";
import { SMTLIBGenerator } from "./generator";

function smtsanizite(str: string): string {
    return str
    .replace(/::/g, "$cc$")
    .replace(/=/g, "$eq$")
    .replace(/\[/g, "$lb$")
    .replace(/\]/g, "$rb$")
    .replace(/{/g, "$lc$")
    .replace(/}/g, "$rc$")
    .replace(/</g, "$la$")
    .replace(/>/g, "$ra$")
    .replace(/\|/g, "$v$")
    .replace(/--/g, "$dd$")
    .replace(/, /g, "$csp$")
    .replace(/[.]/g, "$dot$")
    .replace(/:/g, "$c$")
    .replace(/[\\]/g, "$bs$")
    .replace(/[/]/g, "$fs$")
    .replace(/%/g, "$pct$");
}

type BuiltinTypeEmit = (tcstring: string, cstring: string) => [string, string?];
type BuiltinCallEmit = (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => string;

const BuiltinCalls = new Map<string, BuiltinCallEmit>()
    .set("list_empty", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            return `${decl} (Result_Bool@result_success (= (${smtgen.typegen.typeToSMT2Constructor(rcvrtype)}@size this) 0)))`;
        }
        else {
            return `${decl} (Result_Bool@result_success (= (bsq_term_list_size this) 0)))`;
        }
    })
    .set("list_size", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            return `${decl} (Result_Int@result_success (${smtgen.typegen.typeToSMT2Constructor(rcvrtype)}@size this)))`;
        }
        else {
            return `${decl} (Result_Int@result_success (bsq_term_list_size this)))`;
        }
    })

    .set("list_any", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const contentstype = (smtgen.assembly.entityDecls.get((rcvrtype.options[0] as MIREntityType).ekey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        const carray = `(Array Int ${smtgen.typegen.typeToSMT2Type(contentstype)})`;

        const pred = inv.pcodes.get("p") as MIRPCode;
        const cargs = pred.cargs.map((carg) => {
            const ptname = (inv.params.find((p) => p.name === carg) as MIRFunctionParameter).type;
            const ptype = smtgen.typegen.typeToSMT2Type(smtgen.assembly.typeMap.get(ptname) as MIRType);
            return [carg, ptype];
        });
        const rargs = `((size Int) (ina ${carray}) (i Int)${cargs.length !== 0 ? (" " + cargs.map((ca) => `(${ca[0]} ${ca[1]})`).join(" ")) : ""})`;
        const passargs = cargs.length !== 0 ? (" " + cargs.map((ca) => ca[0]).join(" ")) : "";
        const pname = smtgen.invokenameToSMT2(pred.code);

        const tbase = `
        (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} Result_Bool
            (Result_Bool@result_with_code (result_bmc ${inv.sourceLocation.line}))
        )
        `.trim();

        const tfun = `
        (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} Result_Bool
            (ite (= size i)
                 (Result_Bool@result_success false)
                 (let ((pv (${pname} (select ina i)${passargs})))
                 (ite (is-Result_Bool@result_with_code pv)
                    pv
                    (ite (Result_Bool@result_value pv)
                        pv
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1)${passargs})
                    )
                ))
            )
        )
        `.trim();

        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typegen.typeToSMT2Constructor(rcvrtype);
            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (${rtcons}@size this) (${rtcons}@contents this) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
        else {
            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (bsq_term_list_size this) (bsq_term_list_entries this) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
    })
    .set("list_all", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const contentstype = (smtgen.assembly.entityDecls.get((rcvrtype.options[0] as MIREntityType).ekey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        const carray = `(Array Int ${smtgen.typegen.typeToSMT2Type(contentstype)})`;

        const pred = inv.pcodes.get("p") as MIRPCode;
        const cargs = pred.cargs.map((carg) => {
            const ptname = (inv.params.find((p) => p.name === carg) as MIRFunctionParameter).type;
            const ptype = smtgen.typegen.typeToSMT2Type(smtgen.assembly.typeMap.get(ptname) as MIRType);
            return [carg, ptype];
        });
        const rargs = `((size Int) (ina ${carray}) (i Int)${cargs.length !== 0 ? (" " + cargs.map((ca) => `(${ca[0]} ${ca[1]})`).join(" ")) : ""})`;
        const passargs = cargs.length !== 0 ? (" " + cargs.map((ca) => ca[0]).join(" ")) : "";
        const pname = smtgen.invokenameToSMT2(pred.code);

        const tbase = `
        (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} Result_Bool
            (Result_Bool@result_with_code (result_bmc ${inv.sourceLocation.line}))
        )
        `.trim();

        const tfun = `
        (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} Result_Bool
            (ite (= size i)
                 (Result_Bool@result_success true)
                 (let ((pv (${pname} (select ina i)${passargs})))
                 (ite (is-Result_Bool@result_with_code pv)
                    pv
                    (ite (Result_Bool@result_value pv)
                        (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1)${passargs})
                        pv
                    )
                ))
            )
        )
        `.trim();

        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typegen.typeToSMT2Constructor(rcvrtype);
            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (${rtcons}@size this) (${rtcons}@contents this) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
        else {
            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (bsq_term_list_size this) (bsq_term_list_entries this) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
    })

    .set("list_filter", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const contentstype = (smtgen.assembly.entityDecls.get((rcvrtype.options[0] as MIREntityType).ekey) as MIREntityTypeDecl).terms.get("T") as MIRType;
        const restype = smtgen.assembly.typeMap.get(inv.resultType) as MIRType;
        const resulttype = "Result_" + smtgen.typegen.typeToSMT2Type(restype);

        const carray = `(Array Int ${smtgen.typegen.typeToSMT2Type(contentstype)})`;

        const pred = inv.pcodes.get("p") as MIRPCode;
        const cargs = pred.cargs.map((carg) => {
            const ptname = (inv.params.find((p) => p.name === carg) as MIRFunctionParameter).type;
            const ptype = smtgen.typegen.typeToSMT2Type(smtgen.assembly.typeMap.get(ptname) as MIRType);
            return [carg, ptype];
        });
        const rargs = `((size Int) (ina ${carray}) (i Int)${cargs.length !== 0 ? (" " + cargs.map((ca) => `(${ca[0]} ${ca[1]})`).join(" ")) : ""})`;
        const passargs = cargs.length !== 0 ? (" " + cargs.map((ca) => ca[0]).join(" ")) : "";
        const pname = smtgen.invokenameToSMT2(pred.code);

        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typegen.typeToSMT2Constructor(rcvrtype);

            const tbase = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} ${resulttype}
                (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line}))
            )
            `.trim();

            const tfun = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} ${resulttype}
                (ite (= size i)
                     (${resulttype}@result_success (${rtcons} j outa))
                     (let ((pv (${pname} (select ina i)${passargs})))
                     (ite (is-Result_Bool@result_with_code pv)
                        (${resulttype}@result_with_code (Result_Bool@result_code_value pv))
                        (ite (Result_Bool@result_value pv)
                            (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) (store outa j (select ina i)) (+ j 1)${passargs})
                            (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) outa j${passargs})
                        )
                    ))
                )
            )
            `.trim();

            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (${rtcons}@size this) (${rtcons}@contents this) 0 ${rtcons}@emptysingleton 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
        else {
            const tbase = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}0 ${rargs} ${resulttype}
                (${resulttype}@result_with_code (result_bmc ${inv.sourceLocation.line}))
            )
            `.trim();

            const tfun = `
            (define-fun ${smtgen.invokenameToSMT2(inv.key)}%k% ${rargs} ${resulttype}
                (ite (= size i)
                    (${resulttype}@result_success (bsq_term_list "${smtsanizite(rcvrtype.trkey)}" j outa))
                    (let ((pv (${pname} (select ina i)${passargs})))
                    (ite (is-Result_Bool@result_with_code pv)
                        (${resulttype}@result_with_code (Result_Bool@result_code_value pv))
                        (ite (Result_Bool@result_value pv)
                            (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) (store outa j (select ina i)) (+ j 1)${passargs})
                            (${smtgen.invokenameToSMT2(inv.key)}%kdec% size ina (+ i 1) outa j${passargs})
                        )
                    )
                    )
                )
            )
            `.trim();

            const tentry = `
            ${decl}
            (${smtgen.invokenameToSMT2(inv.key)}10 (bsq_term_list_size this) (bsq_term_list_entries this) 0 ((as const (Array Int BTerm)) bsq_term_none) 0${passargs}))
            `.trim();

            return [tbase, ...[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((i) => tfun.replace(/%k%/g, i.toString()).replace(/%kdec%/g, (i - 1).toString())), tentry].join("\n");
        }
    })

    .set("list_at", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const resulttype = "Result_" + smtgen.typegen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typegen.typeToSMT2Constructor(rcvrtype);

            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (${rtcons}@size this)))
                (${resulttype}@result_success (select (${rtcons}@contents this) ${iv}))
                (${resulttype}@result_with_code (result_error ${smtgen.registerError(inv.sourceLocation)})))
            )
            `;
        }
        else {
            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (bsq_term_list_size this)))
                (${resulttype}@result_success (select (bsq_term_list_entries this) ${iv}))
                (${resulttype}@result_with_code (result_error ${smtgen.registerError(inv.sourceLocation)})))
            )
            `;
        }
    })
    .set("list_set", (smtgen: SMTLIBGenerator, inv: MIRInvokePrimitiveDecl, decl: string) => {
        const rcvrtype = smtgen.assembly.typeMap.get(inv.params[0].type) as MIRType;
        const iv = smtgen.varNameToSMT2Name(inv.params[1].name);
        const vv = smtgen.varNameToSMT2Name(inv.params[2].name);
        const resulttype = "Result_" + smtgen.typegen.typeToSMT2Type(smtgen.assembly.typeMap.get(inv.resultType) as MIRType);

        if (smtgen.typegen.isTypeExact(rcvrtype)) {
            const rtcons = smtgen.typegen.typeToSMT2Constructor(rcvrtype);

            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (${rtcons}@size this)))
                (${resulttype}@result_success (${rtcons} (${rtcons}@size this) (store (${rtcons}@contents this) ${iv} ${vv})))
                (${resulttype}@result_with_code (result_error ${smtgen.registerError(inv.sourceLocation)})))
            )
            `;
        }
        else {

            return `
            ${decl}
            (ite (and (<= 0 ${iv}) (< ${iv} (bsq_term_list_size this)))
                (${resulttype}@result_success (bsq_term_list (bsq_term_list_type this) (bsq_term_list_size this) (store (bsq_term_list_entries this) ${iv} ${vv})))
                (${resulttype}@result_with_code (result_error ${smtgen.registerError(inv.sourceLocation)})))
            )
            `;
        }
    });

const BuiltinTypes = new Map<string, BuiltinTypeEmit>()
    .set("List", (tcstring: string, cstring: string) => {
        return [`    ((${tcstring} (${tcstring}@size Int) (${tcstring}@contents (Array Int ${cstring}))))`, `(declare-const ${tcstring}@emptysingleton (Array Int ${cstring}))`];
});

export {
    smtsanizite,
    BuiltinTypeEmit, BuiltinTypes,
    BuiltinCallEmit, BuiltinCalls
};

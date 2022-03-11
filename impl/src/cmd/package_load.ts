//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type URIPath = {
    scheme: string,
    authority: string | undefined,
    port: number | undefined,
    path: string,
    extension: string | undefined;
};

type URIPathGlob = {
    scheme: string,
    authority: string | undefined,
    port: number | undefined,
    path: string,
    selection: "*" | "**",
    filter: string | undefined
}

type Version = {
    major: number, 
    minor: number,
    fix: number,
    patch: number,
    branch: string | undefined
};

type PackageFormat = "Inline" | "Component" | "Service";

type Contact = {
    name: string,
    role: string,
    email: string | undefined,
    url: URIPath | undefined
};

type SourceInfo = {
    bsqsource: URIPathGlob[],
    entrypoints: URIPathGlob[],
    testfiles: URIPathGlob[]
};

type CompilerOptions = {
};

type CheckerOptions = {
    INT_MIN: number,
    INT_MAX: number,
    SLEN_MAX: number,
    BLEN_MAX: number,

    CONTAINER_MAX: number
};

type Config = {
    macros: string[],
    globalmacros: string[],
    buildlevel: "debug" | "test" | "release",
    testbuild: boolean,
    options: CompilerOptions | CheckerOptions
};

type Dependency = {
    name: string,
    version: Version,
    internalOnly: boolean
};

//exports must include scope component of the form `${name}${version.major}`
type Package = {
    name: string;
    version: Version,
    format: PackageFormat,
    description: string
    keywords: string[],
    homepage: URIPath,
    repository: URIPath,
    license: string,
    people: Contact[],
    src: SourceInfo,
    packagemacros: string[],
    documentation: {
        files: URIPath[],
        root: URIPath
    },
    configs: Config[],
    dependencies: Dependency[],
    devDependencies: Dependency[]
};

function parseURIScheme(str: string): [string | undefined, string] {
    if (process.platform === "win32") {
        if (/^[a-zA-Z]:\\/.test(str) || str.startsWith(".\\") || str.startsWith("..\\")) {
            return ["file", str];
        }
    }
    
    if ((process.platform === "linux" || process.platform === "darwin")) {
        if (str.startsWith("/") || str.startsWith("~/") || str.startsWith("./") || str.startsWith("../")) {
            return ["file", str];
        }
    }

    const schemematch = /:/.exec(str);
    if (schemematch !== null) {
        return [schemematch[0].slice(0, schemematch.index), str.slice(schemematch.index + 1)];
    }
    else {
        return [undefined, str];
    }
}

function parseURIAuthority(str: string): [string | undefined, number | undefined, string] {
    if(!str.startsWith("//")) {
        return [undefined, undefined, str];
    }

    const authoritymatch = /^\/\/[a-zA-Z0-9.]+/.exec(str);
    if (authoritymatch !== null) {
        const tail = str.slice(authoritymatch[0].length + 1);
        const port = /^:[0-9]{1, 5}/.exec(tail);
        if(port === null) {
            return [authoritymatch[0].slice(2, authoritymatch[0].length), undefined, tail];
        }
        else {
            const tail2 = tail.slice(port[0].length + 1);
            const portval = Number.parseInt(port[0].slice(1));

            return [authoritymatch[0].slice(2, authoritymatch[0].length), portval, tail2]
        }
    }
    else {
        return [undefined, undefined, str];
    }
}

function parseURIPathBase(str: string): {scheme: string, authority: string | undefined, port: number | undefined, path: string, extension: string | undefined} | undefined {
    const [scheme, rstr1] = parseURIScheme(str);
    if(scheme === undefined) {
        return undefined;
    }

    const [authority, port, rstr2] = parseURIAuthority(rstr1);
    const extidx = rstr2.lastIndexOf(".");
    if(extidx === -1) {
        return undefined;
    }
    const extension = rstr2.slice(extidx + 1);

    return {
        scheme: scheme,
        authority: authority,
        port: port,
        path: rstr2,
        extension: extension
    };
}

function parsePackage(jp: any): Package {

}


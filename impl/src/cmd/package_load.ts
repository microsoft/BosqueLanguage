//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type URIPathString = string; //path parts not things like sep or prefix

type URIPath = {
    scheme: string,
    authority: [URIPathString],
    path: [URIPathString],
    extension: string;
};

type URIPathGlob = {
    scheme: string,
    authority: [URIPathString],
    path: [URIPathString],
    selection: "*" | "**",
    filter: string
}

type Version = {
    major: number, 
    minor: number,
    fix: number,
    patch: number,
    branch: URIPathString
};

type Contact = {
    name: string,
    role: string,
    email: string,
    url: URIPath
};

type SourceInfo = {
    bsqsource: URIPathGlob[],
    entrypoints: URIPathGlob[],
    testfiles: URIPathGlob[]
}

//exports must include scope component of the form `${name}${version.major}`
type Package = {
    name: URIPathString;
    version: Version,
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
    configs: xxxx,
    dependencies: xxxx,
};



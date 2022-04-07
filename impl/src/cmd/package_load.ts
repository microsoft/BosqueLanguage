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
    selection: "*" | "**" | undefined,
    filter: string | undefined
}

type Version = {
    major: number,
    minor: number,
    fix: number,
    patch: number,
    branch: string | undefined
};

type VersionConstraint = {
    major: number,
    minor: number, //min minor
    fix: number,
    branch: string | undefined
};

type PackageFormat = "inline" | "component" | "service";

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

type ConfigRun = {
    main: string,
    args: any[] | undefined
};

type ConfigBuild = {
    out: URIPath | undefined
};

type ConfigTest = {
    flavors: ("sym" | "icpp" | "err" | "chk")[],
    dirs: URIPathGlob[] | "*"
};

type ConfigAppTest = {
    flavors: ("sym" | "icpp" | "err" | "chk")[],
    dirs: URIPathGlob[] | "*"
};

type ConfigFuzz = {
    dirs: URIPathGlob[] | "*"
};

type Config<T> = {
    name: string,
    macros: string[],
    globalmacros: string[],
    buildlevel: "debug" | "test" | "release"
    params: T
};

type Dependency = {
    name: string,
    version: VersionConstraint,
    format: PackageFormat, //string encoded
    internal: boolean,
    src: URIPath | undefined //optional fixed lookup -- repo, manager ref, file system -- otherwise we do standard resolution
};

//exports must include scope component of the form `${name}${version.major}`
type Package = {
    name: string;
    version: Version, //string encoded
    description: string,
    keywords: string[],
    homepage: URIPath | undefined, //string encoded
    repository: URIPath | undefined, //string encoded
    license: string,
    people: Contact[],
    src: SourceInfo,
    documentation: {
        files: URIPath[], //string encoded
        root: URIPath //string encoded
    } | undefined,
    configs: {
        run: Config<ConfigRun>[],
        build: Config<ConfigBuild>[],
        test: Config<ConfigTest>[],
        apptest: Config<ConfigAppTest>[],
        fuzz: Config<ConfigFuzz>[]
    },
    dependencies: Dependency[],
    devDependencies: Dependency[]
};

function parseURIScheme(str: string): [string | undefined, string] {
    if (process.platform === "win32") {
        if (/^[a-zA-Z]:\\/.test(str) || str.startsWith(".\\") || str.startsWith("..\\")) {
            return ["file", str];
        }

        if (str.startsWith("./") || str.startsWith("../")) {
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
    if (!str.startsWith("//")) {
        return [undefined, undefined, str];
    }

    const authoritymatch = /^\/\/[a-zA-Z0-9.]+/.exec(str);
    if (authoritymatch !== null) {
        const tail = str.slice(authoritymatch[0].length + 1);
        const port = /^:[0-9]{1, 5}/.exec(tail);
        if (port === null) {
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

function parseURIPathBase(str: string): { scheme: string, authority: string | undefined, port: number | undefined, path: string, extension: string | undefined } | undefined {
    const [scheme, rstr1] = parseURIScheme(str);
    if (scheme === undefined) {
        return undefined;
    }

    const [authority, port, rstr2] = parseURIAuthority(rstr1);
    const extidx = rstr2.lastIndexOf(".");
    if (extidx === -1) {
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

function parseURIPath(pp: any): URIPath | undefined {
    if (typeof (pp) !== "string") {
        return undefined;
    }

    return parseURIPathBase(pp);
}

function parseURIPathGlob(pg: any): URIPathGlob | undefined {
    if (typeof (pg) !== "string") {
        return undefined;
    }

    const mm = /([*]{1,2}([.][a-zA-Z0-9]+)?)$/.exec(pg);
    const ubase = parseURIPathBase(mm !== null ? pg.slice(0, pg.length - mm[0].length) : pg);
    if (ubase === undefined) {
        return undefined;
    }

    if (mm === null) {
        return {
            scheme: ubase.scheme,
            authority: ubase.authority,
            port: ubase.port,
            path: ubase.path,
            selection: undefined,
            filter: undefined
        };
    }
    else {
        return {
            scheme: ubase.scheme,
            authority: ubase.authority,
            port: ubase.port,
            path: ubase.path,
            selection: mm[0].startsWith("**") ? "**" : "*",
            filter: mm[0].includes(".") ? mm[0].slice(mm[0].indexOf(".") + 1) : undefined
        };
    }
}

function parseVersion(vv: any): Version | undefined {
    if (typeof (vv) !== "string") {
        return undefined;
    }

    if (!/^[0-9]{1,5}\.[0-9]{1,5}\.[0-9]{1,5}\.[0-9]{1,5}(-[a-zA-Z-0-9_]+)?$/.test(vv)) {
        return undefined;
    }

    let branch: string | undefined = undefined;
    if (vv.includes("-")) {
        const bidx = vv.indexOf("-");
        branch = vv.slice(bidx + 1);
        vv = vv.slice(0, bidx);
    }

    const pvals = (vv as string).split(".");

    return {
        major: Number.parseInt(pvals[0]),
        minor: Number.parseInt(pvals[1]),
        fix: Number.parseInt(pvals[2]),
        patch: Number.parseInt(pvals[3]),
        branch: branch
    };
}


function parseVersionConstraint(vv: any): VersionConstraint | undefined {
    if (typeof (vv) !== "string") {
        return undefined;
    }

    if (!/^[0-9]{1-5}\.[0-9]{1-5}\.[0-9]{1-5}\.[*](-[a-zA-Z-0-9_]+)?$/.test(vv)) {
        return undefined;
    }

    let branch: string | undefined = undefined;
    if (vv.includes("-")) {
        const bidx = vv.indexOf("-");
        branch = vv.slice(bidx + 1);
        vv = vv.slice(0, bidx);
    }

    const pvals = (vv as string).split(".");

    return {
        major: Number.parseInt(pvals[0]),
        minor: Number.parseInt(pvals[1]),
        fix: Number.parseInt(pvals[2]),
        branch: branch
    };
}

function parsePackageFormat(pf: any): PackageFormat | undefined {
    if (pf !== "inline" && pf !== "component" && pf !== "service") {
        return undefined;
    }

    return pf;
}

function parseContact(ct: any): Contact | undefined {
    if (ct === null || typeof (ct) !== "object") {
        return undefined;
    }

    if (typeof (ct["name"]) !== "string" || typeof (ct["role"]) !== "string") {
        return undefined;
    }

    if (ct["email"] !== undefined && typeof (ct["email"]) !== "string") {
        return undefined;
    }

    if (ct["url"] !== undefined && typeof (ct["url"]) !== "string") {
        return undefined;
    }

    return {
        name: ct["name"],
        role: ct["role"],
        email: ct["email"],
        url: ct["url"]
    }
}

function parseSourceInfo(si: any): SourceInfo | undefined {
    if (si === null || typeof (si) !== "object") {
        return undefined;
    }

    if (!Array.isArray(si["bsqsource"])) {
        return undefined;
    }
    const bsqsrc = si["bsqsource"].map((src) => {
        const pp = parseURIPathGlob(src);
        if (pp === undefined) {
            return undefined;
        }

        if (pp.selection !== undefined && pp.filter === undefined) {
            pp.filter = ".bsq";
        }

        return pp.filter === ".bsq" ? pp : undefined;
    });

    if (!Array.isArray(si["entrypoints"])) {
        return undefined;
    }
    const entrypoints = si["entrypoints"].map((src) => {
        const pp = parseURIPathGlob(src);
        if (pp === undefined) {
            return undefined;
        }

        if (pp.selection !== undefined && pp.filter === undefined) {
            pp.filter = ".bsqapi";
        }

        return (pp.filter === undefined || pp.filter === ".bsqapi") ? pp : undefined;
    });

    if (!Array.isArray(si["testfiles"])) {
        return undefined;
    }
    const testfiles = si["testfiles"].map((src) => {
        const pp = parseURIPathGlob(src);
        if (pp === undefined) {
            return undefined;
        }

        if (pp.selection !== undefined && pp.filter === undefined) {
            pp.filter = ".bsqtest";
        }

        return (pp.filter === undefined || pp.filter === ".bsqtest") ? pp : undefined;
    });

    if (bsqsrc.includes(undefined) || entrypoints.includes(undefined) || testfiles.includes(undefined)) {
        return undefined;
    }

    return {
        bsqsource: bsqsrc as URIPathGlob[],
        entrypoints: entrypoints as URIPathGlob[],
        testfiles: testfiles as URIPathGlob[]
    };
}

function parseConfigRun(cfg: any): ConfigRun | undefined {
    if (typeof (cfg["main"]) !== "string") {
        return undefined;
    }

    if (cfg["args"] === undefined) {
        return {
            main: cfg["main"],
            args: undefined
        }
    }
    else {
        if (!Array.isArray(cfg["args"])) {
            return undefined;
        }

        return {
            main: cfg["main"],
            args: cfg["args"]
        }
    }
}

function parseConfigBuild(cfg: any): ConfigBuild | undefined {
    const out = parseURIPath(cfg["out"]);
    if (out === undefined) {
        return undefined;
    }

    return {
        out: out
    };
}

function parseConfigTest(cfg: any): ConfigTest | undefined {
    let flavors: ("sym" | "icpp" | "err" | "chk")[] = ["sym", "icpp", "chk"];
    if (cfg["flavors"] !== undefined) {
        if (!Array.isArray(cfg["flavors"]) || cfg["flavors"].some((ff) => (ff !== "sym" && ff !== "icpp" && ff !== "err" && ff !== "chk"))) {
            return undefined;
        }
        flavors = cfg["flavors"] as ("sym" | "icpp" | "err" | "chk")[];
    }

    let dirs: URIPathGlob[] | "*" = "*";
    if (cfg["dirs"] !== undefined) {
        if (!Array.isArray(cfg["dirs"])) {
            return undefined;
        }

        const dirsmap = cfg["dirs"].map((dd) => parseURIPathGlob(dd));
        if (dirsmap.includes(undefined)) {
            return undefined;
        }

        dirs = dirsmap as URIPathGlob[];
    }

    return {
        flavors: flavors,
        dirs: dirs
    };
}

function parseConfigAppTest(cfg: any): ConfigAppTest | undefined {
    let flavors: ("sym" | "icpp" | "err" | "chk")[] = ["sym", "icpp", "err"];
    if (cfg["flavors"] !== undefined) {
        if (!Array.isArray(cfg["flavors"]) || cfg["flavors"].some((ff) => (ff !== "sym" && ff !== "icpp" && ff !== "err" && ff !== "chk"))) {
            return undefined;
        }
        flavors = cfg["flavors"] as ("sym" | "icpp" | "err" | "chk")[];
    }

    let dirs: URIPathGlob[] | "*" = "*";
    if (cfg["dirs"] !== undefined) {
        if (!Array.isArray(cfg["dirs"])) {
            return undefined;
        }

        const dirsmap = cfg["dirs"].map((dd) => parseURIPathGlob(dd));
        if (dirsmap.includes(undefined)) {
            return undefined;
        }

        dirs = dirsmap as URIPathGlob[];
    }

    return {
        flavors: flavors,
        dirs: dirs
    };
}

function parseConfigFuzz(cfg: any): ConfigFuzz | undefined {
    let dirs: URIPathGlob[] | "*" = "*";
    if (cfg["dirs"] !== undefined) {
        if (!Array.isArray(cfg["dirs"])) {
            return undefined;
        }

        const dirsmap = cfg["dirs"].map((dd) => parseURIPathGlob(dd));
        if (dirsmap.includes(undefined)) {
            return undefined;
        }

        dirs = dirsmap as URIPathGlob[];
    }

    return {
        dirs: dirs
    };
}

function parseConfig<T>(cf: any, tag: "run" | "build" | "test" | "apptest" | "fuzz"): Config<T> | undefined {
    if (cf === null || typeof (cf) !== "object") {
        return undefined;
    }

    if (typeof (cf["name"]) !== "string" || !/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(cf["name"])) {
        return undefined;
    }

    let macros: string[] = [];
    if (cf["macros"] !== undefined) {
        if (!Array.isArray(cf["macros"])) {
            return undefined;
        }
        const macrosmap = cf["macros"].map((mm) => {
            if (typeof (mm) !== "string" || !/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(mm)) {
                return undefined;
            }
            return mm;
        });

        if(macrosmap.includes(undefined)) {
            return undefined;
        }
        macros = macrosmap as string[];
    }

    let globalmacros: string[] = [];
    if (cf["globalmacros"] !== undefined) {
        if (!Array.isArray(cf["globalmacros"])) {
            return undefined;
        }
        const globalmacrosmap = cf["globalmacros"].map((mm) => {
            if (typeof (mm) !== "string" || !/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(mm)) {
                return undefined;
            }
            return mm;
        });

        if (globalmacrosmap.includes(undefined)) {
            return undefined;
        }
        globalmacros = globalmacrosmap as string[];
    }

    let buildlevel: "debug" | "test" | "release" = "debug";
    let pc: any = undefined;
    if (tag === "run") {
        buildlevel = "test";
        pc = parseConfigRun(cf);
    }
    else if (tag === "build") {
        buildlevel = "test";
        pc = parseConfigBuild(cf);
    }
    else if (tag === "test") {
        buildlevel = "test";
        pc = parseConfigTest(cf);
    }
    else if (tag === "apptest") {
        buildlevel = "test";
        pc = parseConfigAppTest(cf);
    }
    else {
        buildlevel = "test";
        pc = parseConfigFuzz(cf);
    }

    if(cf["buildlevel"] !== undefined) {    
        if (cf["buildlevel"] !== "debug" && cf["buildlevel"] !== "test" && cf["buildlevel"] !== "release") {
            return undefined
        }
        buildlevel = cf["buildlevel"] as "debug" | "test" | "release";
    } 

    return {
        name: cf["name"] as string,
        macros: macros as string[],
        globalmacros: globalmacros as string[],
        buildlevel: buildlevel,
        params: pc as T
    };
}

function parseAppDependency(dep: any): Dependency | undefined {
    if (dep === null || typeof (dep) !== "object") {
        return undefined;
    }

    const format = parsePackageFormat(dep["format"]);
    if (format === undefined) {
        return undefined;
    }

    if (typeof (dep["name"]) !== "string") {
        return undefined
    }

    const vc = parseVersionConstraint(dep["version"]);
    if (vc === undefined) {
        return undefined;
    }

    let src: URIPath | undefined = undefined;
    if (dep["src"] !== undefined) {
        src = parseURIPath(dep["src"]);
        if (src === undefined) {
            return undefined;
        }
    }

    return {
        name: dep["name"] as string,
        version: vc,
        format: format,
        internal: dep["internal"] === true,
        src: src
    };
}

function parseDevDependency(dep: any): Dependency | undefined {
    if (dep === null || typeof (dep) !== "object") {
        return undefined;
    }

    const format = parsePackageFormat(dep["format"]);
    if (format === undefined) {
        return undefined;
    }

    if (typeof (dep["name"]) !== "string") {
        return undefined
    }

    const vc = parseVersionConstraint(dep["version"]);
    if (vc === undefined) {
        return undefined;
    }

    let src: URIPath | undefined = undefined;
    if (dep["src"] !== undefined) {
        src = parseURIPath(dep["src"]);
        if (src === undefined) {
            return undefined;
        }
    }

    return {
        name: dep["name"] as string,
        version: vc,
        format: format,
        internal: true,
        src: src
    };
}

function parsePackage(jp: any): Package | string {
    if (jp === null || typeof (jp) !== "object") {
        return "package not a valid JSON object";
    }

    if (typeof (jp["name"]) !== "string") {
        return "invalid 'name' field";
    }

    const version = parseVersion(jp["version"]);
    if (version === undefined) {
        return "invalid 'version' field";
    }

    if (typeof (jp["description"]) !== "string") {
        return "invalid 'description' field";
    }

    let keywords: string[] = [];
    if (jp["keywords"] !== undefined) {
        if (!Array.isArray(jp["keywords"]) || jp["keywords"].some((ee) => typeof (ee) !== "string")) {
            return "invalid 'keywords'";
        }

        keywords = jp["keywords"];
    }

    let homepage: URIPath | undefined = undefined;
    if (jp["homepage"] !== undefined) {
        homepage = parseURIPath(jp["homepage"]);
        if (homepage === undefined) {
            return "invalid 'homepage' field";
        }
    }

    let repository: URIPath | undefined = undefined;
    if (jp["repository"] !== undefined) {
        repository = parseURIPath(jp["repository"]);
        if (repository === undefined) {
            return "invalid 'repository' field";
        }
    }

    if (typeof (jp["license"]) !== "string") {
        return "invalid 'license' field";
    }

    let people: Contact[] = [];
    if (jp["people"] !== undefined) {
        if (!Array.isArray(jp["people"])) {
            return "'people' field should be an array";
        }

        const peoplemap = jp["people"].map((pp) => parseContact(pp));
        if (peoplemap.includes(undefined)) {
            return "invalid 'contact' in 'people' field";
        }
        people = peoplemap as Contact[];
    }

    const srcinfo = parseSourceInfo(jp["src"]);
    if (srcinfo === undefined) {
        return "invalid 'src' field";
    }

    let documentation: { files: URIPath[], root: URIPath } | undefined = undefined;
    if (jp["documentation"] !== undefined) {
        if (jp["documentation"] === null || typeof (jp["documentation"]) !== "object") {
            return "invalid 'documentation' field";
        }

        let docfiles: URIPath[] = [];
        if (!Array.isArray(jp["documentation"]["files"])) {
            return "'documentation.files' needs to be an array";
        }

        const docfilesmap = jp["documentation"]["files"].map((df) => parseURIPath(df));
        if (docfilesmap.includes(undefined)) {
            return "invalid 'documentation.files' entry";
        }
        docfiles = docfilesmap as URIPath[];

        const docroot = parseURIPath(jp["documentation"]["root"]);
        if (docroot === undefined) {
            return "invalid 'documentation.root' field";
        }

        documentation = {
            files: docfiles,
            root: docroot
        };
    }

    let runconfigs: Config<ConfigRun>[] = [];
    let buildconfigs: Config<ConfigBuild>[] = [];
    let testconfigs: Config<ConfigTest>[] = [];
    let apptestconfigs: Config<ConfigAppTest>[] = [];
    let fuzzconfigs: Config<ConfigFuzz>[] = [];

    const configs = jp["configs"];
    if (configs !== undefined) {
        if (configs === null || typeof (configs) !== "object") {
            return "invalid 'config' field";
        }

        if (configs["run"] !== undefined) {
            if (!Array.isArray(configs["run"])) {
                return "expected array for 'config.run' field";
            }

            const rcfg = configs["run"].map((cfg) => parseConfig<ConfigRun>(cfg, "run"));
            if (rcfg.includes(undefined)) {
                return "invalid entry in 'config.run' array";
            }
            runconfigs = rcfg as Config<ConfigRun>[];
        }

        if (configs["build"] !== undefined) {
            if (!Array.isArray(configs["build"])) {
                return "expected array for 'config.build' field";
            }

            const rcfg = configs["build"].map((cfg) => parseConfig<ConfigBuild>(cfg, "build"));
            if (rcfg.includes(undefined)) {
                return "invalid entry in 'config.build' array";
            }
            buildconfigs = rcfg as Config<ConfigBuild>[];
        }

        if (configs["test"] !== undefined) {
            if (!Array.isArray(configs["test"])) {
                return "expected array for 'config.test' field";
            }

            const rcfg = configs["test"].map((cfg) => parseConfig<ConfigTest>(cfg, "test"));
            if (rcfg.includes(undefined)) {
                return "invalid entry in 'config.test' array";
            }
            testconfigs = rcfg as Config<ConfigTest>[];
        }

        if (configs["apptest"] !== undefined) {
            if (!Array.isArray(configs["apptest"])) {
                return "expected array for 'config.apptest' field";
            }

            const rcfg = configs["apptest"].map((cfg) => parseConfig<ConfigAppTest>(cfg, "apptest"));
            if (rcfg.includes(undefined)) {
                return "invalid entry in 'config.apptest' array";
            }
            apptestconfigs = rcfg as Config<ConfigAppTest>[];
        }

        if (configs["fuzz"] !== undefined) {
            if (!Array.isArray(configs["fuzz"])) {
                return "expected array for 'config.fuzz' field";
            }

            const rcfg = configs["fuzz"].map((cfg) => parseConfig<ConfigFuzz>(cfg, "fuzz"));
            if (rcfg.includes(undefined)) {
                return "invalid entry in 'config.fuzz' array";
            }
            fuzzconfigs = rcfg as Config<ConfigFuzz>[];
        }
    }

    let dependencies: Dependency[] = [];
    if (jp["dependencies"] !== undefined) {
        if (!Array.isArray(jp["dependencies"])) {
            return "expected array for 'dependencies' field";
        }

        const dependenciesmap = jp["dependencies"].map((dep) => parseAppDependency(dep));
        if (dependenciesmap.includes(undefined)) {
            return "invalid entry in 'dependencies' array";
        }
        dependencies = dependenciesmap as Dependency[];
    }

    let devDependencies: Dependency[] = [];
    if (jp["devDependencies"] !== undefined) {
        if (!Array.isArray(jp["devDependencies"])) {
            return "expected array for 'devDependencies' field";
        }

        const devDependenciesmap = jp["devDependencies"].map((pp) => parseDevDependency(pp));
        if (devDependenciesmap.includes(undefined)) {
            return "invalid entry in 'devDependencies' array";
        }
        devDependencies = devDependenciesmap as Dependency[];
    }

    return {
        name: jp["name"] as string,
        version: version,
        description: jp["description"] as string,
        keywords: keywords,
        homepage: homepage,
        repository: repository,
        license: jp["license"] as string,
        people: people,
        src: srcinfo,
        documentation: documentation,
        configs: {
            run: runconfigs,
            build: buildconfigs,
            test: testconfigs,
            apptest: apptestconfigs,
            fuzz: fuzzconfigs
        },
        dependencies: dependencies,
        devDependencies: devDependencies
    };
}

export {
    URIPath, URIPathGlob, Version, VersionConstraint, PackageFormat, Contact, SourceInfo, ConfigRun, ConfigBuild, ConfigTest, ConfigAppTest, ConfigFuzz, Config, Dependency, Package,
    parseURIPath, parseURIPathGlob, parsePackage
};

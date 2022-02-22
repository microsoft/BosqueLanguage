


function generateMASM(buildlevel: BuildLevel, usercode: PackageConfig[], corecode: CodeFileInfo[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.Executable, [coreconfig, ...usercode], buildlevel, entrypoint);
}

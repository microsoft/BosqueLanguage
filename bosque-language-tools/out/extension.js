"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const vscode = require("vscode");
const Path = require("path");
const child_process_1 = require("child_process");
function activate(context) {
    let tcdisposable = vscode.commands.registerCommand('extension.typecheck', () => {
        const rootws = (vscode.workspace.workspaceFolders || [])[0];
        if (rootws !== undefined) {
            const tcpath = Path.join(__dirname, "../bsqdrop/runtimes/vscmd/vscmd.js");
            const configdir = rootws.uri.fsPath;
            const cmd = `node ${tcpath} typecheck \"${configdir}\"`;
            let oc = vscode.window.createOutputChannel("Bosque TypeCheck");
            oc.clear();
            try {
                const outinfo = child_process_1.execSync(cmd).toString();
                const errs = JSON.parse(outinfo).map((err) => JSON.parse(err));
                if (errs.length === 0) {
                    oc.appendLine("Ok");
                    oc.show();
                }
                else {
                    const byfile = errs.sort((a, b) => a[0].localeCompare(b[0]));
                    const report = byfile.map((err) => `Error in "${err[0]}" on line ${err[1]}: ${err[2]}.`);
                    oc.appendLine(report.join("\n"));
                    oc.show();
                }
            }
            catch (ex) {
                oc.appendLine(ex.toString());
                oc.show();
            }
        }
    });
    context.subscriptions.push(tcdisposable);
    let vdisposable = vscode.commands.registerCommand('extension.symtest', () => {
        const rootws = (vscode.workspace.workspaceFolders || [])[0];
        if (rootws !== undefined) {
            const tcpath = Path.join(__dirname, "../bsqdrop/runtimes/vscmd/vscmd.js");
            const configdir = rootws.uri.fsPath;
            const cmd = `node ${tcpath} verify \"${configdir}\"`;
            let oc = vscode.window.createOutputChannel("Bosque SymTest");
            oc.clear();
            try {
                const outinfo = child_process_1.execSync(cmd).toString();
                if (outinfo.length === 0) {
                    oc.appendLine("No errors were found!");
                    oc.show();
                }
                else {
                    oc.appendLine(`Error on input when given -- ${outinfo}`);
                    oc.show();
                }
            }
            catch (ex) {
                oc.appendLine(ex.toString());
                oc.show();
            }
        }
    });
    context.subscriptions.push(vdisposable);
    let bdisposable = vscode.commands.registerCommand('extension.bsqcompile', () => {
        const rootws = (vscode.workspace.workspaceFolders || [])[0];
        if (rootws !== undefined) {
            const tcpath = Path.join(__dirname, "../bsqdrop/runtimes/vscmd/vscmd.js");
            const configdir = rootws.uri.fsPath;
            const cmd = `node ${tcpath} compile \"${configdir}\"`;
            let oc = vscode.window.createOutputChannel("Bosque Build");
            oc.clear();
            try {
                const outinfo = child_process_1.execSync(cmd).toString();
                if (outinfo.length === 0) {
                    oc.appendLine("Build Ok");
                    oc.show();
                }
                else {
                    oc.appendLine(`Error -- ${outinfo}`);
                    oc.show();
                }
            }
            catch (ex) {
                oc.appendLine(ex.toString());
                oc.show();
            }
        }
    });
    context.subscriptions.push(bdisposable);
}
exports.activate = activate;
function deactivate() { }
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map
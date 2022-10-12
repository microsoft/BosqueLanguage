//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";

import { MIRType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";

class Hex0Constraint {
    readonly path: number[];
    readonly condition: string;

    constructor(path: number[], condition: string) {
        this.path = path;
        this.condition = condition;
    }

    static create(condition: string): Hex0Constraint {
        return new Hex0Constraint([], condition);
    }

    extend(step: number): Hex0Constraint {
        return new Hex0Constraint([step, ...this.path], this.condition);
    }
}

class Hex0TestOption {
    readonly constraints: Hex0Constraint[];

    constructor(constraints: Hex0Constraint[]) {
        this.constraints = constraints;
    }

    extend(step: number): Hex0TestOption {
        return new Hex0TestOption(this.constraints.map((c) => c.extend(step)));
    }

    augment(condition: string) {
        return new Hex0TestOption([Hex0Constraint.create(condition), ...this.constraints]);
    }
}

class Hex0Generator {
    readonly temitter: SMTTypeEmitter;

    constructor(temitter: SMTTypeEmitter) {
        this.temitter = temitter;
    }

    private generateHex0Options_Bool(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(= (BBool@UFCons_API ;;PATH;;) true)")]), 
            new Hex0TestOption([Hex0Constraint.create("(= (BBool@UFCons_API ;;PATH;;) false)")])
        ];
    }

    private generateHex0Options_Nat(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(= (BNat@UFCons_API ;;PATH;;) 0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateHex0Options_Int(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(< (BInt@UFCons_API ;;PATH;;) 0)")]),
            new Hex0TestOption([Hex0Constraint.create("(= (BInt@UFCons_API ;;PATH;;) 0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateHex0Options_BigNat(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(= (BBigNat@UFCons_API ;;PATH;;) 0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BBigNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateHex0Options_BigInt(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(< (BBigInt@UFCons_API ;;PATH;;) 0)")]),
            new Hex0TestOption([Hex0Constraint.create("(= (BBigInt@UFCons_API ;;PATH;;) 0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BBigInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateHex0Options_Float(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(< (BFloat@UFCons_API ;;PATH;;) 0.0)")]),
            new Hex0TestOption([Hex0Constraint.create("(= (BFloat@UFCons_API ;;PATH;;) 0.0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BFloat@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateHex0Options_Decimal(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(< (BDecimal@UFCons_API ;;PATH;;) 0.0)")]),
            new Hex0TestOption([Hex0Constraint.create("(= (BDecimal@UFCons_API ;;PATH;;) 0.0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BDecimal@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateHex0Options_Rational(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(< (BRational@UFCons_API ;;PATH;;) 0.0)")]),
            new Hex0TestOption([Hex0Constraint.create("(= (BRational@UFCons_API ;;PATH;;) 0.0)")]), 
            new Hex0TestOption([Hex0Constraint.create("(> (BRational@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateHex0Options_String(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(= (BString@UFCons_API ;;PATH;;) \"\")")]),
            new Hex0TestOption([Hex0Constraint.create("(> (len (BString@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateHex0Options_ByteBuffer(): Hex0TestOption[] {
        return [
            new Hex0TestOption([Hex0Constraint.create("(= (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")]),
            new Hex0TestOption([Hex0Constraint.create("(> (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateHex0Options_DateTime(): Hex0TestOption[] {
        return [
            xxxx
        ];
    }
  
    private generateHex0Options_UTCDateTime(): Hex0TestOption[] {
        return [
            xxxx
        ];
    }
  
  private generateHex0Options_CalendarDate(): Hex0TestOption[] {
        return [
            xxxx
        ];
    }

    private generateHex0Options_BTickTime@UFCons_API (HavocSequence) BTickTime)
    private generateHex0Options_BLogicalTime@UFCons_API (HavocSequence) BLogicalTime)
    private generateHex0Options_BUUID4@UFCons_API (HavocSequence) BUUID4)
    private generateHex0Options_BUUID7@UFCons_API (HavocSequence) BUUID7)
    private generateHex0Options_BSHAContentHash@UFCons_API (HavocSequence) BSHAContentHash)
    private generateHex0Options_BLatitude@UFCons_API (HavocSequence) BFloat)
    private generateHex0Options_BLongitude@UFCons_API (HavocSequence) BFloat)
}

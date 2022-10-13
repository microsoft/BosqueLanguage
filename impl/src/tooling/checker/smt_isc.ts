//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";

import { MIRType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";

class ISCConstraint {
    readonly path: number[];
    readonly condition: string;

    constructor(path: number[], condition: string) {
        this.path = path;
        this.condition = condition;
    }

    static create(condition: string): ISCConstraint {
        return new ISCConstraint([], condition);
    }

    extend(step: number): ISCConstraint {
        return new ISCConstraint([step, ...this.path], this.condition);
    }
}

class ISCTestOption {
    readonly constraints: ISCConstraint[];

    constructor(constraints: ISCConstraint[]) {
        this.constraints = constraints;
    }

    extend(step: number): ISCTestOption {
        return new ISCTestOption(this.constraints.map((c) => c.extend(step)));
    }

    augment(condition: string) {
        return new ISCTestOption([ISCConstraint.create(condition), ...this.constraints]);
    }
}

class ISCGenerator {
    readonly temitter: SMTTypeEmitter;

    constructor(temitter: SMTTypeEmitter) {
        this.temitter = temitter;
    }

    private generateISCOptions_Bool(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BBool@UFCons_API ;;PATH;;) true)")]), 
            new ISCTestOption([ISCConstraint.create("(= (BBool@UFCons_API ;;PATH;;) false)")])
        ];
    }

    private generateISCOptions_Nat(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BNat@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_Int(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BInt@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BInt@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_BigNat(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BBigNat@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BBigNat@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_BigInt(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BBigInt@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BBigInt@UFCons_API ;;PATH;;) 0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BBigInt@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_Float(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BFloat@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BFloat@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BFloat@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_Decimal(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BDecimal@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BDecimal@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BDecimal@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_Rational(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(< (BRational@UFCons_API ;;PATH;;) 0.0)")]),
            new ISCTestOption([ISCConstraint.create("(= (BRational@UFCons_API ;;PATH;;) 0.0)")]), 
            new ISCTestOption([ISCConstraint.create("(> (BRational@UFCons_API ;;PATH;;) 0.0)")])
        ];
    }

    private generateISCOptions_String(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BString@UFCons_API ;;PATH;;) \"\")")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BString@UFCons_API ;;PATH;;)) 1)")]),
            new ISCTestOption([ISCConstraint.create("(> (len (BString@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateISCOptions_ByteBuffer(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (len (BByteBuffer@UFCons_API ;;PATH;;)) 0)")])
        ];
    }

    private generateISCOptions_DateTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 11)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 31)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 23)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2019)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 10)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 3)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 1)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) \"PST\")")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2019)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 10)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 3)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 1)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 0)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) \"PDT\")")
            ])
        ];
    }
  
    private generateISCOptions_UTCDateTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 11)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 31)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 23)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 59)")
            ])
        ];
    }
  
  private generateISCOptions_CalendarDate(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ])
        ];
    }

    private generateISCOptions_TickTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BTickTime@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (BTickTime@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_LogicalTime(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (BLogicalTime@UFCons_API ;;PATH;;) 0)")]),
            new ISCTestOption([ISCConstraint.create("(> (BLogicalTime@UFCons_API ;;PATH;;) 0)")])
        ];
    }

    private generateISCOptions_UUID4(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_UUID7(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_SHAContentHash(): ISCTestOption[] {
        return [];
    }

    private generateISCOptions_LatLongCoordinate(): ISCTestOption[] {
        return [
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1909)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 1999)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2014)")]),
            new ISCTestOption([ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2105)")]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2012)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 28)")
            ]),
            new ISCTestOption([
                ISCConstraint.create("(= (len (BDateYear@UFCons_API ;;PATH;;)) 2011)"),
                ISCConstraint.create("(= (len (BDateMonth@UFCons_API ;;PATH;;)) 2)"),
                ISCConstraint.create("(= (len (BDateDay@UFCons_API ;;PATH;;)) 27)")
            ])
        ];
    }
}

/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        ir.getParams().forEach(var -> {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(entry -> {
            Var var = entry.getKey();
            Value v = entry.getValue();
            target.update(var, meetValue(v, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else {
            if (v1.equals(v2)) return v1;
            else return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            LValue left = defStmt.getLValue();
            RValue right = defStmt.getRValue();
            if (left instanceof Var leftVar && canHoldInt(leftVar)) {
                Value newValue = evaluate(right, in);
                changed |= out.update(leftVar, newValue);
            }
        }
        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof BinaryExp binExp) {
            Value v1 = evaluate(binExp.getOperand1(), in);
            Value v2 = evaluate(binExp.getOperand2(), in);
            if (v1.isConstant() && v2.isConstant()) {
                int val1 = v1.getConstant();
                int val2 = v2.getConstant();
                if (binExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD:
                            return Value.makeConstant(val1 + val2);
                        case SUB:
                            return Value.makeConstant(val1 - val2);
                        case MUL:
                            return Value.makeConstant(val1 * val2);
                        case DIV:
                            if (val2 != 0) {
                                return Value.makeConstant(val1 / val2);
                            } else {
                                return Value.getUndef();
                            }
                        case REM:
                            if (val2 != 0) {
                                return Value.makeConstant(val1 % val2);
                            } else {
                                return Value.getUndef();
                            }
                    }
                } else if (binExp instanceof BitwiseExp bitwiseExp) {
                    return switch (bitwiseExp.getOperator()) {
                        case AND -> Value.makeConstant(val1 & val2);
                        case OR -> Value.makeConstant(val1 | val2);
                        case XOR -> Value.makeConstant(val1 ^ val2);
                    };
                } else if (binExp instanceof ShiftExp shiftExp) {
                    return switch (shiftExp.getOperator()) {
                        case SHL -> Value.makeConstant(val1 << val2);
                        case SHR -> Value.makeConstant(val1 >> val2);
                        case USHR -> Value.makeConstant(val1 >>> val2);
                    };
                } else if (binExp instanceof ConditionExp conditionExp) {
                    return switch (conditionExp.getOperator()) {
                        case EQ -> Value.makeConstant(val1 == val2 ? 1 : 0);
                        case NE -> Value.makeConstant(val1 != val2 ? 1 : 0);
                        case LT -> Value.makeConstant(val1 < val2 ? 1 : 0);
                        case LE -> Value.makeConstant(val1 <= val2 ? 1 : 0);
                        case GT -> Value.makeConstant(val1 > val2 ? 1 : 0);
                        case GE -> Value.makeConstant(val1 >= val2 ? 1 : 0);
                    };
                }
            } else if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            } else if (v1.isNAC() && v2.isConstant() && v2.getConstant() == 0) {
                if (binExp instanceof ArithmeticExp arithmeticExp
                        && (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV
                        || arithmeticExp.getOperator() == ArithmeticExp.Op.REM)) {
                    return Value.getUndef();
                }
                return Value.getNAC();
            }
        } else if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        return Value.getNAC();
    }
}

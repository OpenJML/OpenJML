package com.sun.tools.javac.comp;

import java.math.BigInteger;

import freeboogie.ast.*;
import freeboogie.ast.AssertAssumeCmd.CmdType;
import freeboogie.ast.AtomLit.AtomType;
import freeboogie.ast.BinaryOp.Op;
import freeboogie.ast.PrimitiveType.Ptype;
import freeboogie.ast.Specification.SpecType;

public interface IBoogie {
    ArrayType ArrayType(Type rowType, Type colType, Type elemType, AstLocation location);
    AssertAssumeCmd AssertAssumeCmd(CmdType type, Expr expr, AstLocation location);
    AssignmentCmd AssignmentCmd(Expr lhs, Expr rhs);
    AtomId AtomId(String id, AstLocation location);
    AtomLit AtomLit(AtomType val, AstLocation location);
    AtomNum AtomNum(BigInteger val, AstLocation location);
    AtomOld AtomOld(Expr e, AstLocation location);
    
    BinaryOp BinaryOp(BinaryOp.Op op, Expr left, Expr right);
    
    Block Block(String name, Commands cmds, Identifiers succ, AstLocation location);
    Blocks Blocks(Block block, Blocks tail);
    Body Body(Declaration vars, Blocks blocks, AstLocation location);
    
    Commands Commands(Command cmd, Commands tail);
    
    Implementation Implementation(Signature sig, Body body, Declaration tail, AstLocation location);
    AstLocation Location(String file, int line, int col);
    PrimitiveType PrimitiveType(Ptype ptype, AstLocation location);
    
    Procedure Procedure(Signature sig, Specification spec, Declaration tail, AstLocation location);

    Signature Signature(String name, Declaration args, Declaration results, AstLocation location);
    Specification Specification(SpecType type, Expr expr, boolean free, Specification tail, AstLocation location);

    UnaryOp UnaryOp(UnaryOp.Op op, Expr e);
    VariableDecl VariableDecl(String name, Type type, Declaration tail, AstLocation location);
}

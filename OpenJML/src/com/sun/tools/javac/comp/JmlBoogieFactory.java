package com.sun.tools.javac.comp;

import java.math.BigInteger;

import freeboogie.ast.*;
import freeboogie.ast.AssertAssumeCmd.CmdType;
import freeboogie.ast.AtomLit.AtomType;
import freeboogie.ast.BinaryOp.Op;
import freeboogie.ast.PrimitiveType.Ptype;
import freeboogie.ast.Specification.SpecType;

public class JmlBoogieFactory implements IBoogie {

    public ArrayType ArrayType(Type rowType, Type colType, Type elemType, AstLocation location) {
        return ArrayType.mk(rowType,colType,elemType,location);
    }
    
    public AssertAssumeCmd AssertAssumeCmd(CmdType type, Expr expr, AstLocation location){
        return AssertAssumeCmd.mk(type,expr,location);
    }
    
    public AssignmentCmd AssignmentCmd(Expr lhs, Expr rhs) {
        return AssignmentCmd.mk(lhs,rhs);
    }
    
    public AtomId AtomId(String id, AstLocation location) {
        return AtomId.mk(id,location);
    }
    
    public AtomLit AtomLit(AtomType val, AstLocation location) {
        return AtomLit.mk(val,location);
    }
    
    public AtomNum AtomNum(BigInteger val, AstLocation location) {
        return AtomNum.mk(val,location);
    }
    
    public AtomOld AtomOld(Expr e, AstLocation location) {
        return AtomOld.mk(e, location);
    }
    
    public BinaryOp BinaryOp(BinaryOp.Op op, Expr left, Expr right) {
        return BinaryOp.mk(op,left,right);
    }
    
    public Block Block(String name, Commands cmds, Identifiers succ, AstLocation location) {
        return Block.mk(name,cmds,succ,location);
    }
    
    public Blocks Blocks(Block block, Blocks tail) {
        return Blocks.mk(block,tail);
    }
    
    public Body Body(Declaration vars, Blocks blocks, AstLocation location) {
        return Body.mk(vars,blocks,location);
    }

    public Commands Commands(Command cmd, Commands tail) {
        return Commands.mk(cmd,tail);
    }

    public Implementation Implementation(Signature sig, Body body, Declaration tail, AstLocation location) {
        return Implementation.mk(sig,body,tail,location);
    }
    
    public AstLocation Location(String file, int line, int col) {
        return new AstLocation(file,line,col);
    }

    public PrimitiveType PrimitiveType(Ptype ptype, AstLocation location) {
        return PrimitiveType.mk(ptype, location);
    }
    
    public Procedure Procedure(Signature sig, Specification spec, Declaration tail, AstLocation location) {
        return Procedure.mk(sig,spec,tail,location);
    }
    
    public Signature Signature(String name, Declaration args, Declaration results, AstLocation location) {
        return Signature.mk(name,args,results,location);
    }
    
    public Specification Specification(SpecType type, Expr expr, boolean free, Specification tail, AstLocation location) {
        return Specification.mk(type,expr,free,tail,location);
    }
    
    public UnaryOp UnaryOp(UnaryOp.Op op, Expr e) {
        return UnaryOp.mk(op,e);
    }
    
    public VariableDecl VariableDecl(String name, Type type, Declaration tail, AstLocation location) {
        return VariableDecl.mk(name,type,tail,location);
    }

}

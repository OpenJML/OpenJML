grammar Fb;

@header {
  package freeboogie.parser; 
  import freeboogie.ast.*; 
  import freeboogie.tc.TypeUtils;
  import java.math.BigInteger;
}
@lexer::header {
  package freeboogie.parser;
}

@parser::members {
  public String fileName = null; // the file being processed
  private AstLocation tokLoc(Token t) {
    return new AstLocation(fileName,t.getLine(),t.getCharPositionInLine()+1);
  }
  private AstLocation astLoc(Ast a) {
    return a == null? AstLocation.unknown() : a.loc();
  }
  
  public boolean ok = true;
  
  @Override
  public void reportError(RecognitionException x) {
    ok = false;
    super.reportError(x);
  }
}

program returns [Declaration v]:
  declarations EOF { if(ok) $v=$declarations.v; }
;

declarations returns [Declaration v]:
                                                { $v=null; }
  | 'type' d=type_decl_tail                     { $v=$d.v; }
  | 'const' d=const_decl_tail                   { $v=$d.v; }
  | 'function' d=function_decl_tail             { $v=$d.v; }
  | 'axiom' d=axiom_tail                        { $v=$d.v; }
  | 'var' d=global_decl_tail                    { $v=$d.v; }
  | 'procedure' d=procedure_decl_tail           { $v=$d.v; }
  | 'implementation' d=implementation_decl_tail { $v=$d.v; }
;

type_decl_tail returns [Declaration v]:
    ID (
    (';' t1=declarations { if(ok) $v=TypeDecl.mk($ID.text,$t1.v,tokLoc($ID));})
  | (',' t2=type_decl_tail { if(ok) $v=TypeDecl.mk($ID.text,$t2.v,tokLoc($ID)); }))
;

const_decl_tail returns [Declaration v]:
    'unique'? ID ':' type (
    (';' t1=declarations    { if(ok) $v=ConstDecl.mk($ID.text,$type.v,$t1.v,tokLoc($ID)); })
  | (',' t2=const_decl_tail { if(ok) $v=ConstDecl.mk($ID.text,$type.v,$t2.v,tokLoc($ID)); }))
;

function_decl_tail returns [Declaration v]:
  s=signature ';' declarations
    { if(ok) $v=Function.mk($s.v,$declarations.v,astLoc($s.v)); }
;

axiom_tail returns [Declaration v]:
  e=expr ';' declarations { if(ok) $v=Axiom.mk($e.v,$declarations.v,astLoc($e.v)); }
;

global_decl_tail returns [Declaration v]:
    ID ':' type (
    (';' t1=declarations     { if(ok) $v=VariableDecl.mk($ID.text,$type.v,$t1.v,tokLoc($ID)); })
  | (',' t2=global_decl_tail { if(ok) $v=VariableDecl.mk($ID.text,$type.v,$t2.v,tokLoc($ID)); }))
;

procedure_decl_tail returns [Declaration v]:
  s=signature ';'? spec_list body? t=declarations
    { if(ok) {
        Declaration proc_tail = $t.v;
        if ($body.v != null)
          proc_tail = Implementation.mk(TypeUtils.stripDep($s.v),$body.v,proc_tail,astLoc($s.v));
        $v=Procedure.mk($s.v,$spec_list.v,proc_tail,astLoc($s.v)); 
    }}
;
	
implementation_decl_tail returns [Declaration v]:
  s=signature body t=declarations
    { if(ok) $v = Implementation.mk($s.v,$body.v,$t.v,astLoc($s.v)); }
;

signature returns [Signature v]:
  ID '(' (a=opt_id_type_list)? ')' ('returns' '(' (b=opt_id_type_list)? ')')?
    { if(ok) $v = Signature.mk($ID.text,$a.v,$b.v,tokLoc($ID)); }
;

spec_list returns [Specification v]:
      { $v=null; }
  | (f='free')? 'requires' h=expr ';' t=spec_list
      { if(ok) $v=Specification.mk(Specification.SpecType.REQUIRES,$h.v,$f!=null,$t.v,astLoc($h.v)); }
  | 'modifies' t=modifies_tail
      { $v=$modifies_tail.v; }
  | (f='free')? 'ensures' h=expr ';' t=spec_list
      { if(ok) $v=Specification.mk(Specification.SpecType.ENSURES,$h.v,$f!=null,$t.v,astLoc($h.v)); }
;

modifies_tail returns [Specification v]:
    ';' spec_list { $v = $spec_list.v; }
  | h=atom_id ','? t=modifies_tail
      { if(ok) $v=Specification.mk(Specification.SpecType.MODIFIES,$h.v,false,$t.v,astLoc($h.v)); }
;
	
body returns [Body v]:
  '{' ('var' var_id_type_list)? b=block_list '}'
    { if(ok) $v = Body.mk($var_id_type_list.v,$b.v,astLoc($b.v)); }
;

block_list returns [Block v]:
  ID ':' (command_list)? block_succ (t=block_list)?
    { if(ok) $v=Block.mk($ID.text,$command_list.v,$block_succ.v,$t.v,tokLoc($ID));}
;

block_succ returns [Identifiers v]:
    a='goto' id_list ';' 
      { if(ok) $v=$id_list.v; }
  |  a='return' ';'
      { if(ok) $v=null; }
;
	
command	returns [Command v]:
    a=atom_id (i=index)? ':=' b=expr ';' 
      { if(ok) { 
          Atom lhs = $a.v;
          if ($i.v!=null) lhs=AtomIdx.mk(lhs,$i.v,astLoc($a.v));
          $v=AssignmentCmd.mk(lhs,$b.v,astLoc($a.v));
      }}
  | t='assert' expr ';'
      { if(ok) $v=AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSERT,$expr.v,tokLoc($t)); }
  | t='assume' expr ';'
      { if(ok) $v=AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME,$expr.v,tokLoc($t)); }
  | t='havoc' atom_id ';'
      { if(ok) $v=HavocCmd.mk($atom_id.v,tokLoc($t));}
  | t='call' (l=id_list ':=')? ID '(' (r=expr_list)? ')' ';'
      { if(ok) $v=CallCmd.mk($ID.text,$l.v,$r.v,tokLoc($t));}
;
	
index returns [Index v]:
  '[' a=expr (',' b=expr)? ']' { if(ok) $v = Index.mk($a.v, $b.v,astLoc($a.v)); }
;

/* BEGIN expression grammar.

   See http://www.engr.mun.ca/~theo/Misc/exp_parsing.htm
   for a succint presentation of how to implement precedence
   and associativity in a LL-grammar, the classical way.

   The precedence increases
     <==>
     ==>
     &&, ||
     =, !=, <, <=, >=, >, <:
     +, -
     *, /, %

   <==> is associative
   ==> is right associative
   Others are left associative.
   The unary operators are ! and -.
   Typechecking takes care of booleans added to integers 
   and the like.
 */

expr returns [Expr v]:
  l=expr_a {$v=$l.v;} 
    (t='<==>' r=expr_a {if(ok) $v=BinaryOp.mk(BinaryOp.Op.EQUIV,$v,$r.v,tokLoc($t));})*
;

expr_a returns [Expr v]: 
  l=expr_b {$v=$l.v;} 
    (t='==>' r=expr_a {if(ok) $v=BinaryOp.mk(BinaryOp.Op.IMPLIES,$v,$r.v,tokLoc($t));})?
;

// TODO: these does not keep track of location quite correctly
expr_b returns [Expr v]:
  l=expr_c {$v=$l.v;} 
    (op=and_or_op r=expr_c {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,astLoc($r.v));})*
;

expr_c returns [Expr v]:
  l=expr_d {$v=$l.v;}
    (op=comp_op r=expr_d {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,astLoc($r.v));})*
;

expr_d returns [Expr v]:
  l=expr_e {$v=$l.v;}
    (op=add_op r=expr_e {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,astLoc($r.v));})*
;

expr_e returns [Expr v]: 
  l=expr_f {$v=$l.v;}
    (op=mul_op r=expr_f {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,astLoc($r.v));})*
;

expr_f returns [Expr v]:
    atom index? 
      { if (ok) {
         if ($index.v==null) $v=$atom.v;
          else $v=AtomIdx.mk($atom.v,$index.v,astLoc($atom.v));
      }}
  | '(' expr ')' {$v=$expr.v;}
  | t='-' a=expr_f   {if(ok) $v=UnaryOp.mk(UnaryOp.Op.MINUS,$a.v,tokLoc($t));}
  | t='!' a=expr_f   {if(ok) $v=UnaryOp.mk(UnaryOp.Op.NOT,$a.v,tokLoc($t));}
;

and_or_op returns [BinaryOp.Op v]:
    '&&' { $v = BinaryOp.Op.AND; }
  | '||' { $v = BinaryOp.Op.OR; }
;

comp_op returns [BinaryOp.Op v]:
    '==' { $v = BinaryOp.Op.EQ; }
  | '!=' { $v = BinaryOp.Op.NEQ; }
  | '<'  { $v = BinaryOp.Op.LT; }
  | '<=' { $v = BinaryOp.Op.LE; }
  | '>=' { $v = BinaryOp.Op.GE; }
  | '>'  { $v = BinaryOp.Op.GT; }
  | '<:' { $v = BinaryOp.Op.SUBTYPE; }
;

add_op returns [BinaryOp.Op v]:
    '+' { $v = BinaryOp.Op.PLUS; }
  | '-' { $v = BinaryOp.Op.MINUS; }
;

mul_op returns [BinaryOp.Op v]:
    '*' { $v = BinaryOp.Op.MUL; }
  | '/' { $v = BinaryOp.Op.DIV; }
  | '%' { $v = BinaryOp.Op.MOD; }
;

atom returns [Atom v]:
    t='false' { if(ok) $v = AtomLit.mk(AtomLit.AtomType.FALSE,tokLoc($t)); }
  | t='true'  { if(ok) $v = AtomLit.mk(AtomLit.AtomType.TRUE,tokLoc($t)); }
  | t='null'  { if(ok) $v = AtomLit.mk(AtomLit.AtomType.NULL,tokLoc($t)); }
  | t=INT     { if(ok) $v = AtomNum.mk(new BigInteger($INT.text),tokLoc($t)); }
  | atom_id   { $v = $atom_id.v; }
  |	t=ID '(' (expr_list?) ')'
              { if(ok) $v = AtomFun.mk($ID.text, $expr_list.v,tokLoc($t)); }
  | t='old' '(' expr ')'
              { if(ok) $v = AtomOld.mk($expr.v,tokLoc($t)); }
  | t='cast' '(' expr ',' type ')'
              { if(ok) $v = AtomCast.mk($expr.v, $type.v,tokLoc($t)); }
  | t='(' a=quant_op b=id_type_list '::' c=triggers d=expr ')'
              { if(ok) $v = AtomQuant.mk($a.v,$b.v,$c.v,$d.v,tokLoc($t)); }
;

atom_id returns [AtomId v]:
    ID      { if(ok) $v = AtomId.mk($ID.text,tokLoc($ID)); }
;

// END of the expression grammar 
	
quant_op returns [AtomQuant.QuantType v]:
    'forall' { $v = AtomQuant.QuantType.FORALL; }
  | 'exists' { $v = AtomQuant.QuantType.EXISTS; }
;

triggers returns [Trigger v]:
    { $v=null; }
  | a='{' (':' ID)? c=expr_list '}' d=triggers
      { if(ok) $v=Trigger.mk($ID==null?null:$ID.text,$c.v,$d.v,tokLoc($a)); }
;


// BEGIN list rules 
	
expr_list returns [Exprs v]:
  h=expr (',' t=expr_list)? { if(ok) $v = Exprs.mk($h.v, $t.v,astLoc($h.v)); }
;

id_list	returns [Identifiers v]:	
    a=atom_id (',' r=id_list)? { if(ok) $v=Identifiers.mk($a.v,$r.v,astLoc($a.v)); }
;

opt_id_type_list returns [Declaration v]:
  (hi=ID ':')? ht=type (',' t=opt_id_type_list)? 
    { if(ok) $v = VariableDecl.mk(($hi==null)?null:$hi.text, $ht.v, $t.v,astLoc($ht.v)); }
;

id_type_list returns [Declaration v]:
  hi=ID ':' ht=type (',' t=id_type_list)? 
    { if(ok) $v = VariableDecl.mk($hi.text, $ht.v, $t.v,tokLoc($ID)); }
;

var_id_type_list returns [Declaration v]:
    ';' { $v = null; }
  | hi=ID ':' ht=type (','|';' 'var')? t=var_id_type_list
      { if(ok) $v = VariableDecl.mk($hi.text, $ht.v, $t.v,tokLoc($ID)); }
;

command_list returns [Commands v]:
  h=command (t=command_list)? { if(ok) $v=Commands.mk($h.v,$t.v,astLoc($h.v)); }
;
	
// END list rules 


simple_type returns [Type v]:
    t='bool' { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.BOOL,tokLoc($t)); }
  | t='int'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.INT,tokLoc($t)); }
  | t='ref'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.REF,tokLoc($t)); }
  | t='name' { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.NAME,tokLoc($t)); }
  | t='any'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.ANY,tokLoc($t)); }
  | t=ID     { if(ok) $v = UserType.mk($ID.text,tokLoc($t)); }
  | t='[' r=simple_type (',' c=simple_type)? ']' e=simple_type
             { if(ok) $v = ArrayType.mk($r.v,$c.v,$e.v,tokLoc($t)); }
  | t='<' p=simple_type '>' st=simple_type
             { if(ok) $v = GenericType.mk($p.v,$st.v,tokLoc($t)); }
;

type returns [Type v]:
  t=simple_type ('where' p=expr)?
    {  if (ok) {
         if ($p.v==null) $v=$t.v;
         else $v=DepType.mk($t.v,$p.v,astLoc($t.v));
    }}
;
	
ID:
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^') 
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'|'`'|'0'..'9')*
;
	
INT     : 	'0'..'9'+ ;
WS      : 	(' '|'\t'|'\n'|'\r')+ {$channel=HIDDEN;};
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

LINE_COMMENT
    : '//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    ;

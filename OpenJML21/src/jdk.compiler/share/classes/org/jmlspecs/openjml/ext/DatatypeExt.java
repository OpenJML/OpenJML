package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Pair;

public class DatatypeExt extends JmlExtension {

    public static final String datatypeID = "datatype";
    public final IJmlClauseKind dataTypeKind = new DatatypeKind();
    
    public static class DatatypeKind extends IJmlClauseKind.ClassLikeKind {

        public DatatypeKind() {
            super(datatypeID);
        }

        @Override
        public JmlDatatypeDecl parse(JCModifiers xmods, String keyword,
                IJmlClauseKind clauseKind, JmlParser parser) {
            init(parser);
            Comment dc = parser.token().comment(CommentStyle.JAVADOC);
            int pos = parser.token().pos;
            JCModifiers mods = parser.modifiersOpt(xmods);
            parser.nextToken();
            Name datatypeName = parser.ident(); // Simple name of the datatype
            List<JCTypeParameter> typarams = parser.typeParametersOpt();
            System.out.println("Parsing datatype named " + datatypeName.toString());
            parser.accept(TokenKind.LBRACE);
            Names names = Names.instance(parser.context);
            ListBuffer<JCTree> defs = new ListBuffer<>();
            ListBuffer<Pair<Name,List<JCVariableDecl> >> cons = new ListBuffer<>();
            while (parser.token().kind != TokenKind.RBRACE && parser.token().kind != TokenKind.SEMI && parser.token().kind != TokenKind.EOF) {
                // FIXME - comma required?
                JmlTreeCopier copier = new JmlTreeCopier(parser.context,parser.jmlF);
                if (parser.token().kind == TokenKind.COMMA) parser.nextToken();
                ListBuffer<JCExpression> tyexpr = new ListBuffer<>();
                for (JCTypeParameter tp: typarams) {
                    tyexpr.add(parser.jmlF.Ident(tp.name));
                }
                List<JCExpression> tye = tyexpr.toList();
                Name cname = parser.ident();
                List<JCVariableDecl> params = parser.formalParameters();
                cons.add(new Pair<Name,List<JCVariableDecl>>(cname,params));
                JCExpression restype = parser.jmlF.Ident(datatypeName);
                if (!typarams.isEmpty()) restype = parser.jmlF.TypeApply(restype, tye);
                JCModifiers mmodstatic = parser.jmlF.Modifiers(Flags.PUBLIC|Flags.STATIC);
                parser.utils.setJML(mmodstatic);
                JCModifiers mmods = parser.jmlF.Modifiers(Flags.PUBLIC|Flags.ABSTRACT);
                parser.utils.setJML(mmods);
                ListBuffer<JCTypeParameter> ntyparams = new ListBuffer<>();
                for (JCTypeParameter tp: typarams) {
                    ntyparams.add(parser.jmlF.TypeParameter(tp.name, tp.bounds));
                }
                JCMethodDecl mdecl = parser.jmlF.MethodDef(mmodstatic,cname,restype,ntyparams.toList(), params, List.<JCExpression>nil(), null, null );
                defs.add(mdecl);
                Name isName = names.fromString("is" + cname.toString());
                mdecl = parser.jmlF.MethodDef(mmods,isName,parser.jmlF.TypeIdent(TypeTag.BOOLEAN),List.<JCTypeParameter>nil(), List.<JCVariableDecl>nil(), List.<JCExpression>nil(), null, null );
                defs.add(mdecl);
                for (JCVariableDecl p: params) {
                    mdecl = parser.jmlF.MethodDef(mmods,p.name,copier.copy(p.vartype),List.<JCTypeParameter>nil(), List.<JCVariableDecl>nil(), List.<JCExpression>nil(), null, null );
                    defs.add(mdecl);
                }
            }
            if (parser.token().kind == TokenKind.SEMI) {
                parser.nextToken();
                while (parser.token().kind != TokenKind.RBRACE && parser.token().kind != TokenKind.EOF) {
                    // Parse a method
                    
                    List<JCTree> t = parser.classOrInterfaceOrRecordBodyDeclaration(mods, datatypeName,false,false);
                    // check that this is a method
                    if (t != null && !t.isEmpty()) defs.add(t.head);
                }
            }
            parser.accept(TokenKind.RBRACE);
            //mods.flags |= Flags.STATIC; // Implicitly static
            mods.flags |= Flags.ABSTRACT; // Implicitly abstract -- FIXME doe sit need to be if it is model?
            // Implicitly model
            JmlSpecs.instance(parser.context).addModifier(pos, Modifiers.MODEL, mods);
            // FIXME - make this a novel primitive type
            Type at = utils.createClassSymbol(com.sun.tools.javac.code.Symtab.instance(parser.context).java_base, "org.jmlspecs.lang.IJmlDatatype").type;
            JCExpression dtype = parser.jmlF.at(pos).Type(at);
            JmlDatatypeDecl d = new JmlDatatypeDecl(mods, datatypeName, typarams, null, List.<JCExpression>of(dtype), defs.toList(), null);
            d.constructors = cons.toList();
            d.pos = pos;
            parser.utils.setJML(d.mods);
            while (parser.isEndJml()) parser.nextToken();
            System.out.println(d.toString());
            return d;
            
            // No upper or lower bounds on type parameters
            // Primitive types allowed
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }

    static public class JmlDatatypeDecl extends JmlClassDecl {
        
        public List<Pair<Name,List<JCVariableDecl> >> constructors;
        
        protected JmlDatatypeDecl(JCModifiers mods, Name name,
                List<JCTypeParameter> typarams, JCExpression extending,
                List<JCExpression> implementing, List<JCTree> defs,
                ClassSymbol sym) {
            super(mods, name, typarams, extending, implementing, defs, sym);
            // TODO Auto-generated constructor stub
        }
        
    }
}

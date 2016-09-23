package org.jmlspecs.openjml.jmldoc;

import java.util.Iterator;
import java.util.List;


import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.MemberSummaryWriter;
import com.sun.tools.doclets.internal.toolkit.builders.MemberSummaryBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.Util;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

public class MemberSummaryBuilderJml extends MemberSummaryBuilder {

    public MemberSummaryBuilderJml(Configuration configuration) { 
        super(configuration);
    }
    
    // FIXME - major change in b144
//    public void buildFieldsSummary(XMLNode node) {
//        super.buildFieldsSummary(node);
//        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
//        ((FieldWriterJml)w).checkJmlSummary(classDoc);
//    }

    // FIXME - major change in b144
//    public void buildFieldsInheritedSummary(XMLNode node) {
//        super.buildFieldsInheritedSummary(node);
//        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
//        VisibleMemberMap visibleMemberMap = visibleMemberMaps[VisibleMemberMap.FIELDS];
//        for (Iterator iter = visibleMemberMap.getVisibleClassesList().iterator(); iter.hasNext();) {
//            ClassDoc inhclass = (ClassDoc) (iter.next());
//            if (! (inhclass.isPublic() ||
//                    Util.isLinkable(inhclass, configuration))) {
//                continue;
//            }
//            if (inhclass == classDoc) {
//                continue;
//            }
//            List inhmembers = visibleMemberMap.getMembersFor(inhclass);
//            ((FieldWriterJml)w).checkJmlInheritedSummary(classDoc,inhmembers);
//        }
//    }

}

package org.jmlspecs.openjml;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.openjml.jmldoc.FieldWriterJml;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.MemberSummaryWriter;
import com.sun.tools.doclets.internal.toolkit.builders.MemberSummaryBuilder;
import com.sun.tools.doclets.internal.toolkit.util.Util;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

public class MemberSummaryBuilderJml extends MemberSummaryBuilder {

    public MemberSummaryBuilderJml(Configuration configuration) { 
        super(configuration);
    }
    
    public void buildFieldsSummary() {
        super.buildFieldsSummary();
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
        ((FieldWriterJml)w).checkJmlSummary(classDoc);
    }

    public void buildFieldsInheritedSummary() {
        super.buildFieldsInheritedSummary();
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
        VisibleMemberMap visibleMemberMap = visibleMemberMaps[VisibleMemberMap.FIELDS];
        for (Iterator iter = visibleMemberMap.getVisibleClassesList().iterator(); iter.hasNext();) {
            ClassDoc inhclass = (ClassDoc) (iter.next());
            if (! (inhclass.isPublic() ||
                    Util.isLinkable(inhclass, configuration))) {
                continue;
            }
            if (inhclass == classDoc) {
                continue;
            }
            List inhmembers = visibleMemberMap.getMembersFor(inhclass);
            ((FieldWriterJml)w).checkJmlInheritedSummary(classDoc,inhmembers);
        }
    }

}

package org.jmlspecs.openjmltest.testcases;

import org.junit.Test;

import com.sun.org.apache.xpath.internal.axes.WalkerFactory;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.jmlspecs.openjmltest.ParseBase;

import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Parser;
import static org.junit.Assert.fail;

public class TestRefiningStatements extends TCBase{
		
	  @Override
	  public void setUp() throws Exception {
	      super.setUp();
	      print = false;
	  }
  

	@Test
	public void testModelProgramWithOneMethod(){
		helpTC(" class Counter { \n"
                +"	private /*@ spec_public @*/  int count = 0; \n"
                + "	private /*@ spec_public @*/ Listener lstnr = null; \n"
                + "	/*@ assignable this.lstnr; \n"
                + "	  @ ensures this.lstnr == lnr; \n"
                + "	 @*/ \n"
                + "	public void register(Listener lnr){ \n"
                + "		this.lstnr = lnr; \n"
                + "	} \n"
                +"	/*@ public model_program { \n"
                +"		@ normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                + "		@ if (this.lstnr==null) { \n"
                + "			@ this.lstnr.actionPerformed(this.count); \n"
                + "		@ }\n"
                +"	@ } \n"
                +"	@*/ \n"
                +"	public void bump(){\n"
                +"		/*@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                +"		@*/ \n"
                + "		this.count  = this.count+1; \n"
                + "		if (this.lstnr==null) { \n"
                + "			this.lstnr.actionPerformed(this.count); \n"
                + "		}\n"
                +"	} \n"
                +"} \n"
                + "interface Listener{ \n"
                + " void actionPerformed(int x); \n"
                + "} \n"
                );
		}
	
	@Test
	public void testModelProgramWithTwoMethods(){
		helpTC(" class Counter { \n"
                +"	private /*@ spec_public @*/  int count = 0; \n"
                + "	private /*@ spec_public @*/ Listener lstnr = null; \n"
                + "	/*@ assignable this.lstnr; \n"
                + "	  @ ensures this.lstnr == lnr; \n"
                + "	 @*/ \n"
                + "	public void register(Listener lnr){ \n"
                + "		this.lstnr = lnr; \n"
                + "	} \n"
                +"	/*@ public model_program { \n"
                +"		@ normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                + "		@ if (this.lstnr==null) { \n"
                + "			@ this.lstnr.actionPerformed(this.count); \n"
                + "		@ }\n"
                +"	@ } \n"
                +"	@*/ \n"
                +"	public void bump(){\n"
                +"		/*@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                +"		@*/ \n"
                + "		this.count  = this.count+1; \n"
                + "		if (this.lstnr==null) { \n"
                + "			this.lstnr.actionPerformed(this.count); \n"
                + "		}\n"
                +"	} \n"
                +"	/*@ public model_program { \n"
                +"		@ normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count-1); \n"
                + "		@ if (this.lstnr==null) { \n"
                + "			@ this.lstnr.actionPerformed(this.count); \n"
                + "		@ }\n"
                +"	@ } \n"
                +"	@*/ \n"
                +"	public void bump2(){\n"
                +"		/*@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count-1); \n"
                +"		@*/ \n"
                + "		this.count  = this.count+1; \n"
                + "		if (this.lstnr==null) { \n"
                + "			this.lstnr.actionPerformed(this.count); \n"
                + "		}\n"
                +"	} \n"                
                +"} \n"
                + "interface Listener{ \n"
                + " void actionPerformed(int x); \n"
                + "} \n"
                );
	}
	
	@Test
	public void testModelProgramWithRefiningBlockInModelProgram(){
		helpTC(" class Counter { \n"
                +"	private /*@ spec_public @*/  int count = 0; \n"
                + "	private /*@ spec_public @*/ Listener lstnr = null; \n"
                + "	/*@ assignable this.lstnr; \n"
                + "	  @ ensures this.lstnr == lnr; \n"
                + "	 @*/ \n"
                + "	public void register(Listener lnr){ \n"
                + "		this.lstnr = lnr; \n"
                + "	} \n"
                +"	/*@ public model_program { \n"
                +"		@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                + "		@ if (this.lstnr==null) { \n"
                + "			@ this.lstnr.actionPerformed(this.count); \n"
                + "		@ }\n"
                +"	@ } \n"
                +"	@*/ \n"
                +"	public void bump(){\n"
                +"		/*@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                +"		@*/ \n"
                + "		this.count  = this.count+1; \n"
                + "		if (this.lstnr==null) { \n"
                + "			this.lstnr.actionPerformed(this.count); \n"
                + "		}\n"
                +"	} \n"
                +"} \n"
                + "interface Listener{ \n"
                + " void actionPerformed(int x); \n"
                + "} \n"
                ,"/TEST.java:11: compiler message file broken: key=compiler.err.jml.invalid.refining.in.modelprogram arguments={0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}",19
                );
	}
	
	@Test
	public void testUnMatchedModelAndRefiningSpecifications(){
		helpTC(" class Counter { \n"
                +"	private /*@ spec_public @*/  int count = 0; \n"
                + "	private /*@ spec_public @*/ Listener lstnr = null; \n"
                + "	/*@ assignable this.lstnr; \n"
                + "	  @ ensures this.lstnr == lnr; \n"
                + "	 @*/ \n"
                + "	public void register(Listener lnr){ \n"
                + "		this.lstnr = lnr; \n"
                + "	} \n"
                +"	/*@ public model_program { \n"
                +"		@ normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count+1); \n"
                + "		@ if (this.lstnr==null) { \n"
                + "			@ this.lstnr.actionPerformed(this.count); \n"
                + "		@ }\n"
                +"	@ } \n"
                +"	@*/ \n"
                +"	public void bump(){\n"
                +"		/*@ refining normal_behavior \n"
                +"		@ assignable this.count; \n"
                +"		@ ensures this.count == \\old(this.count-1); \n"
                +"		@*/ \n"
                + "		this.count  = this.count+1; \n"
                + "		if (this.lstnr==null) { \n"
                + "			this.lstnr.actionPerformed(this.count); \n"
                + "		}\n"
                +"	} \n"
                +"} \n"
                + "interface Listener{ \n"
                + " void actionPerformed(int x); \n"
                + "} \n"
                ,"/TEST.java:11: compiler message file broken: key=compiler.err.specs statements in Refining and Model Program do not match arguments={0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}",19
                );
		
	}
}

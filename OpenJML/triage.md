# Bug Triage 



# Translation Issues

```java
_JML___NEWOBJECT_7181

  public static JSONArray toJSONArray(@NonNull 
  String string) throws JSONException;

```

```java
 /*@
    public normal_behavior
      requires myArrayList != null; 
      {|
        requires value_29373; 
        ensures \result == this; 
        {|
          requires (java.lang.Object)TRUE != null; 
        also
          requires !((java.lang.Object)TRUE != null); 
        |}
      also
        requires !value; 
        ensures \result == this; 
        {|
          requires (java.lang.Object)TRUE != null; 
        also
          requires !((java.lang.Object)TRUE != null); 
        |}
      |}
   */

  @Pure 
  public JSONArray put(boolean value);
```



```java
/*@
    public normal_behavior
      requires myArrayList != null; 
        requires Pre_58_0_8122___6 || Pre_59_0_41643___7; 
        ensures Pre_58 || Pre_59; 
        ensures \result == null; 
   */

  @Pure 
  public String toString();

```




```java
 /*@
    public normal_behavior
      requires true; 
      {|
        requires object != null; 
        requires !(object == null); 
        {|
          ensures \result == null; 
        also
          ensures (\forall int j; 0 <= j && j < i; names_26763_26763___23[j] == java_lang_reflect_Field_getName_357(_heap__, fields_26620_26620___16[j])); 
        |}
      also
        requires (object == null); 
        ensures \result == null; 
      |}
   */

  @Pure 
  public static String[] getNames(@NonNull 
  Object object);
```



```java
public long optLong(@NonNull 
  String key, long defaultValue);
    /*@
    public normal_behavior
      requires this.map != null; 
        requires \old(key) != null; 
        requires "" != null; 
        requires key != null; 
        ensures \result == null; 
        {|
          requires /*missing*/ != null; 
        also
          requires !(key != null); 
          requires \old(key_42603) != null; 
        |}
   */

  @Pure 
  public String optString(@NonNull 
  String key);
```




```java
  /*@
    public normal_behavior
      requires refTokens != null; 
      {|
        requires !Utils.hasNext(_JML_iterator_926); 
        requires _JML___NEWOBJECT_9717 != null; 
        requires null.charArray != null && /*missing*/ != null && (null.charArray != null && /*missing*/ != null && 0 >= 0 && 0 >= 0 && null.charArray.length >= 0 && 0 + null.charArray.length <= /*missing*/.length && 0 + null.charArray.length <= /*missing*/.charArray.length); 
        requires "" != null; 
        requires null.charArray != null && /*missing*/ != null; 
        requires !(null.charArray != null && /*missing*/ != null && (null.charArray != null && /*missing*/ != null && 0 >= 0 && 0 >= 0 && null.charArray.length >= 0 && 0 + null.charArray.length <= /*missing*/.length && 0 + null.charArray.length <= /*missing*/.charArray.length)); 
        ensures _JML_iterator_926 == Utils.iterator(this.refTokens); 
        ensures \result == null; 
        ensures Pre_10 || Pre_11; 
        
      also
        requires "" != null; 
        requires null.charArray != null && /*missing*/ != null; 
        requires _JML___NEWOBJECT_9717 != null; 
        requires !Utils.hasNext(_JML_iterator_926); 
        ensures \result == null; 
        ensures Pre_10 || Pre_11; 
        ensures _JML_iterator_926 == Utils.iterator(this.refTokens); 
        {|
          requires null.charArray != null && /*missing*/ != null && (null.charArray != null && /*missing*/ != null && 0 >= 0 && 0 >= 0 && null.charArray.length >= 0 && 0 + null.charArray.length <= /*missing*/.length && 0 + null.charArray.length <= /*missing*/.charArray.length); 
        also
          requires !(null.charArray != null && /*missing*/ != null && (null.charArray != null && /*missing*/ != null && 0 >= 0 && 0 >= 0 && null.charArray.length >= 0 && 0 + null.charArray.length <= /*missing*/.length && 0 + null.charArray.length <= /*missing*/.charArray.length)); 
        |}
      also
        requires Pre_10_0_8122___6 || Pre_11_0_9610___7; 
      |}
   */

  @Override() @Pure 
  public String toString();
```




```java
   /*@
    public normal_behavior
      requires w != null && maxdepth == 200; 
      {|
        requires !true; 
        
      also
        ensures this.comma_2872_2872___10 == false; 
        ensures this.mode_3078_3078___12 == '\u0000'; 
        ensures this.stack_3186_3186___14 == null; 
        ensures this.top_3329_3329___16 == 0; 
        ensures this.writer_3446_3446___18 == null; 
        ensures this.comma == false; 
        ensures this.mode == 'i'; 
        ensures this.stack.length == maxdepth; 
        ensures this.top == 0; 
        ensures this.writer == w; 
        assignable this.comma_2872_2872___10; 
        assignable this.mode_3078_3078___12; 
        assignable this.stack_3186_3186___14; 
        assignable this.top_3329_3329___16; 
        assignable this.writer_3446_3446___18; 
        assignable this.comma; 
        assignable this.mode; 
        assignable this.stack; 
        assignable this.top; 
        assignable this.writer; 
      |}
   */

  public JSONWriter(@NonNull 
  Writer w);
```

```java
/*@
    public normal_behavior
      requires myArrayList != null; 
      {|
        requires Pre_6_0_99___6 || Pre_7_0_6824___7; 
      also
        requires this.myArrayList != null; 
        ensures Pre_6 || Pre_7; 
      |}
   */

  @Override() @Pure 
  public Iterator<Object> iterator();
```

# Filtering Issues

```java
also
        requires \old(clazz) != null; 
        requires this.myArrayList != null; 
        requires !(clazz != null); 
        ensures \result == null; 
        {|
          requires null != null; 
        also
          requires !(null != null); 
        |}
      also
        requires !(this.myArrayList != null); 
        requires \old(clazz) != null; 
        requires clazz != null; 
        ensures \result == null; 
        {|
          requires null != null; 
        also
          requires !(null != null); 
        |}
      also
        requires !(this.myArrayList != null); 
        requires \old(clazz) != null; 
        requires !(clazz != null); 
        ensures \result == null; 
        {|
          requires null != null; 
        also
          requires !(null != null); 
        |}
      |}
   */

  @Pure 
  public <E extends Enum<E>>E optEnum(@NonNull 
```

# Dumps

```
====STRONGARM FATAL ERROR====
Method: org.json.JSONTokener.syntaxError(java.lang.String)
Date 2017-03-23 16:37:59.819
java.lang.NullPointerException
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:135)
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:122)
	at org.jmlspecs.openjml.strongarm.JDKListUtils.countLOC(JDKListUtils.java:81)
	at org.jmlspecs.openjml.Utils.qualifiedMethodSigWithContractLOC(Utils.java:812)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:827)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONTokener.syntaxError(java.lang.String)
Date 2017-03-23 16:42:27.318
java.lang.NullPointerException
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:135)
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:122)
	at org.jmlspecs.openjml.strongarm.JDKListUtils.countLOC(JDKListUtils.java:81)
	at org.jmlspecs.openjml.Utils.qualifiedMethodSigWithContractLOC(Utils.java:812)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:827)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONArray.isNull(int)
Date 2017-03-23 17:00:05.490
java.util.ConcurrentModificationException
	at java.util.ArrayList$Itr.checkForComodification(ArrayList.java:901)
	at java.util.ArrayList$Itr.next(ArrayList.java:851)
	at org.jmlspecs.openjml.strongarm.SubstitutionCache.getSubstitutionsAlongPathForIdent(SubstitutionCache.java:102)
	at org.jmlspecs.openjml.strongarm.SubstitutionCache.getSubstitutionsAlongPath(SubstitutionCache.java:134)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.canReplace(SubstituteTree2.java:380)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.handleField(SubstituteTree2.java:250)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitSelect(SubstituteTree2.java:84)
	at com.sun.tools.javac.tree.JCTree$JCFieldAccess.accept(JCTree.java:1897)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:244)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement2(Prop.java:253)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:226)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:540)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.keySet()
Date 2017-03-23 17:05:37.165
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:202)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement3(Prop.java:282)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace3(Prop.java:181)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:202)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:681)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.length()
Date 2017-03-23 17:05:37.871
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.shouldRemove(PropagateResults.java:76)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.filterBlock(PropagateResults.java:120)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.visitJmlSpecificationCase(PropagateResults.java:147)
	at org.jmlspecs.openjml.JmlTree$JmlSpecificationCase.accept(JmlTree.java:2598)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.simplify(PropagateResults.java:165)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:820)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.opt(java.lang.String)
Date 2017-03-23 17:05:38.960
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:202)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement3(Prop.java:282)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace3(Prop.java:181)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:202)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:681)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optDouble(java.lang.String)
Date 2017-03-23 17:05:41.187
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitIdent(SubstituteTree2.java:100)
	at com.sun.tools.javac.tree.JCTree$JCIdent.accept(JCTree.java:2011)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitSelect(SubstituteTree2.java:86)
	at com.sun.tools.javac.tree.JCTree$JCFieldAccess.accept(JCTree.java:1897)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:244)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:245)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement3(Prop.java:282)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace3(Prop.java:181)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:202)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:681)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optBigDecimal(java.lang.String,java.math.BigDecimal)
Date 2017-03-23 17:05:44.510
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitIdent(SubstituteTree2.java:100)
	at com.sun.tools.javac.tree.JCTree$JCIdent.accept(JCTree.java:2011)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:244)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement3(Prop.java:282)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace3(Prop.java:181)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:202)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:681)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optDouble(java.lang.String,double)
Date 2017-03-23 17:05:44.792
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:202)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement2(Prop.java:253)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:226)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:540)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optInt(java.lang.String)
Date 2017-03-23 17:05:45.190
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:202)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement2(Prop.java:253)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:226)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:33)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:540)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optInt(java.lang.String,int)
Date 2017-03-23 17:05:45.311
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.handleField(SubstituteTree2.java:241)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:224)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:245)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement2(Prop.java:253)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:226)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:41)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:540)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optJSONArray(java.lang.String)
Date 2017-03-23 17:05:46.571
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitIdent(SubstituteTree2.java:100)
	at com.sun.tools.javac.tree.JCTree$JCIdent.accept(JCTree.java:2011)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitTypeCast(TreeScanner.java:250)
	at com.sun.tools.javac.tree.JCTree$JCTypeCast.accept(JCTree.java:1814)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at com.sun.tools.javac.tree.TreeScanner.visitBinary(TreeScanner.java:245)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.visitBinary(SubstituteTree2.java:230)
	at com.sun.tools.javac.tree.JCTree$JCBinary.accept(JCTree.java:1785)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.scan(SubstituteTree2.java:78)
	at org.jmlspecs.openjml.strongarm.transforms.SubstituteTree2.replace(SubstituteTree2.java:450)
	at org.jmlspecs.openjml.strongarm.tree.Prop.doReplacement3(Prop.java:282)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace3(Prop.java:181)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace2(Prop.java:202)
	at org.jmlspecs.openjml.strongarm.tree.Prop.replace(Prop.java:143)
	at org.jmlspecs.openjml.strongarm.tree.And.replace(And.java:42)
	at org.jmlspecs.openjml.strongarm.tree.Or.replace(Or.java:32)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:681)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.optLong(java.lang.String,long)
Date 2017-03-23 17:05:52.712
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.shouldRemove(PropagateResults.java:76)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.filterBlock(PropagateResults.java:120)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.visitJmlSpecificationCase(PropagateResults.java:147)
	at org.jmlspecs.openjml.JmlTree$JmlSpecificationCase.accept(JmlTree.java:2598)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at org.jmlspecs.openjml.JmlTreeScanner.visitJmlMethodClauseGroup(JmlTreeScanner.java:159)
	at org.jmlspecs.openjml.JmlTree$JmlMethodClauseGroup.accept(JmlTree.java:2059)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:57)
	at org.jmlspecs.openjml.JmlTreeScanner.visitJmlSpecificationCase(JmlTreeScanner.java:224)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.visitJmlSpecificationCase(PropagateResults.java:149)
	at org.jmlspecs.openjml.JmlTree$JmlSpecificationCase.accept(JmlTree.java:2598)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at org.jmlspecs.openjml.JmlTreeScanner.visitJmlMethodClauseGroup(JmlTreeScanner.java:159)
	at org.jmlspecs.openjml.JmlTree$JmlMethodClauseGroup.accept(JmlTree.java:2059)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:57)
	at org.jmlspecs.openjml.JmlTreeScanner.visitJmlSpecificationCase(JmlTreeScanner.java:224)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.visitJmlSpecificationCase(PropagateResults.java:149)
	at org.jmlspecs.openjml.JmlTree$JmlSpecificationCase.accept(JmlTree.java:2598)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.scan(PropagateResults.java:158)
	at org.jmlspecs.openjml.strongarm.transforms.PropagateResults.simplify(PropagateResults.java:165)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:820)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.quote(java.lang.String)
Date 2017-03-23 17:05:55.932
java.lang.NullPointerException
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.toString()
Date 2017-03-23 17:05:58.701
java.lang.NullPointerException
	at org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicateAssignments.shouldRemove(RemoveDuplicateAssignments.java:82)
	at org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicateAssignments.filterBlock(RemoveDuplicateAssignments.java:130)
	at org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicateAssignments.visitJmlSpecificationCase(RemoveDuplicateAssignments.java:144)
	at org.jmlspecs.openjml.JmlTree$JmlSpecificationCase.accept(JmlTree.java:2598)
	at com.sun.tools.javac.tree.TreeScanner.scan(TreeScanner.java:49)
	at org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicateAssignments.scan(RemoveDuplicateAssignments.java:151)
	at org.jmlspecs.openjml.strongarm.transforms.RemoveDuplicateAssignments.simplify(RemoveDuplicateAssignments.java:156)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:802)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.toString(int)
Date 2017-03-23 17:05:59.185
java.lang.NullPointerException
====STRONGARM FATAL ERROR====
Method: org.json.JSONObject.isNull(java.lang.String)
Date 2017-03-23 17:06:38.158
java.lang.NullPointerException
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:135)
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:122)
	at org.jmlspecs.openjml.strongarm.JDKListUtils.countLOC(JDKListUtils.java:81)
	at org.jmlspecs.openjml.Utils.qualifiedMethodSigWithContractLOC(Utils.java:812)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:563)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
====STRONGARM FATAL ERROR====
Method: org.json.JSONPointer.Builder.append(java.lang.String)
Date 2017-03-23 17:11:07.571
java.lang.NullPointerException
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:135)
	at org.jmlspecs.openjml.JmlPretty.write(JmlPretty.java:122)
	at org.jmlspecs.openjml.strongarm.JDKListUtils.countLOC(JDKListUtils.java:81)
	at org.jmlspecs.openjml.Utils.qualifiedMethodSigWithContractLOC(Utils.java:812)
	at org.jmlspecs.openjml.strongarm.Strongarm.cleanupContract(Strongarm.java:563)
	at org.jmlspecs.openjml.strongarm.Strongarm.infer(Strongarm.java:331)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:90)
	at org.jmlspecs.openjml.strongarm.JmlInferPostConditions$1.call(JmlInferPostConditions.java:1)
	at java.util.concurrent.FutureTask.run(FutureTask.java:266)
	at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
	at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
	at java.lang.Thread.run(Thread.java:745)
```


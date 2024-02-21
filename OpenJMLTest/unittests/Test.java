// This Test file launches JUnit tests runs for the OpenJML tests,
// running everything in OpenJMLTest/src/testcases...
// except for rac tests, Specs tests, and those things listed in 'skips'
//
// Some parallelism is implemented -- cf. 'numThreads'
// but currently the tests are run sequentially
// A timeout is enforced -- cf. 'seconds'
// There are some command-line options: -seq -par -t= -s= -v



import org.jmlspecs.openjmltest.*;
import org.jmlspecs.openjmltest.testcases.*;

import java.lang.reflect.*;
import java.util.*;
import java.util.concurrent.*;
import java.io.*;

public class Test {

    static int numThreads = 10;
    static int seconds = 600;
    static ExecutorService eservice;
    static boolean sequential = true;
    static boolean verbose = false;

    public static String[] skips = new String[]{"api","misctests","scanner"};
    {
        Arrays.sort(skips);
    }
    @SuppressWarnings("unchecked")
    public static void main(String... args) throws Exception {
        while (args.length > 0) {
            if (args[0].equals("-seq")) {
                sequential = true;
            } else if (args[0].equals("-par")) {
                sequential = false;
            } else if (args[0].startsWith("-t=")) {
                numThreads = Integer.valueOf(args[0].substring(3));
            } else if (args[0].startsWith("-s=")) {
                seconds = Integer.valueOf(args[0].substring(3));
            } else if (args[0].startsWith("-v")) {
                verbose = true;
            } else {
                break;
            }
            args = Arrays.copyOfRange(args,1,args.length);
        }

        eservice = Executors.newFixedThreadPool(numThreads);
        var dir = new File(JmlTestCase.root + "/OpenJML/OpenJMLTest/src/org/jmlspecs/openjmltest/testcases");
        var lst = args.length == 0 ? dir.list() : args;
        java.util.Arrays.sort(lst);
        int k = args[0].indexOf('#');
        if (k < 0) k = args[0].indexOf('.');
        if (k > 0) lst = new String[] { args[0].substring(0,k) };
        for (var d : lst) {
            if (args.length == 0 && !d.endsWith(".java")) continue;
            if (d.endsWith(".java")) d = d.substring(0,d.length()-5);
            Class<JmlTestCase> clazz;
            try {
                clazz = (Class<JmlTestCase>)Class.forName("org.jmlspecs.openjmltest.testcases." + d);
            } catch (ClassNotFoundException e) {
                System.out.println("Error: There is no unit test named " + d);
                continue;
            }
            if ((d.contains("Specs") || java.util.Arrays.binarySearch(skips,d) >= 0) && args.length == 0 ) {
                System.out.println("Skipping " + clazz);
                continue;
            }
            if (verbose) System.out.println("Queueing " + clazz);
            var cons = clazz.getConstructors();
            if (cons.length != 1) {
                synchronized (sfailures) { failures++; }
                System.out.println("ERROR: Class " + clazz + " should have just one public constructor");
                continue;
            }
            var constr = cons[0];
            var allmethods = clazz.getDeclaredMethods();
            var methods = allmethods;
            java.util.Arrays.sort(methods, (a,b)->a.toString().compareTo(b.toString()));
            if (k > 0) {
                methods = new Method[]{};
                String nm = args[0].substring(k+1,args[0].length());
                for (var m: allmethods) {
                    if (m.getName().equals(nm)) {
                        methods = new Method[] { m };
                        break;
                    }
                }
            }
            java.util.Collection<Object[]> params = java.util.Arrays.<Object[]>asList(new Object[0]);
            if (constr.getParameterCount() != 0) {
                Class c = clazz;
                Method pmethod = null;
                x: while (c != null) {
                    for (var m: c.getDeclaredMethods()) {
                        for (var a: m.getDeclaredAnnotations()) {
                            if (a.toString().contains("org.junit.runners.Parameterized$Parameters")) {
                                pmethod = m;
                                break x;
                            }
                        }
                    }
                    c = c.getSuperclass();
                }
                if (pmethod == null) {
                    System.out.println("No @Parameters found for " + clazz);
                    continue;
                }
                if (verbose) System.out.println("Found @Parameter: " + pmethod);
                params = (java.util.Collection<Object[]>)pmethod.invoke(null);
                if (verbose) System.out.println(params.size() + " PARAMETER SETS");
            }
            for (var p: params) {
                if (verbose && constr.getParameterCount() != 0) {
                    System.out.print("PARAMS");
                    for (var o: p) System.out.print(" " + o);
                    System.out.println();
                }
                java.util.Arrays.sort(methods, (a,b)->a.toString().compareTo(b.toString()));
                for (var method: methods) {
                    var a = method.getAnnotationsByType(org.junit.Test.class);
                    var b = method.getAnnotationsByType(org.junit.Ignore.class);
                    if (a.length == 0) continue; // Not marked with @Test
                    if (b.length != 0) { ignores++; System.out.println("Ignoring test " + method.getName()); continue; }
                    tasks.add(new UnitTest(clazz, method, constr, p));
                }
            }
        }
        System.out.println(tasks.size() + " tasks queued, " + ignores + " ignored");
        if (sequential) {
            threadTask();
        } else {
            for (int i = 0; i < numThreads; i++) {
                var thr = new Thread(()->threadTask(), "T" + i);
                threads.add(thr);
                thr.start();
            }
            for (var t: threads) {
                if (verbose) System.out.println("Joining " + t.getName());
                t.join();
            }
        }
        eservice.shutdownNow(); // Program won't exit without calling this
        System.out.println((tests-timeouts-failures) + " successes, " + timeouts + " timeouts, " + failures + " failures, " + ignores + " ignored");
    }

    static Integer tests = 0; static Object stests = new Object();
    static Integer timeouts = 0; static Object stimeouts = new Object();
    static Integer failures = 0; static Object sfailures = new Object();
    static int ignores = 0;
    static ArrayList<Thread> threads = new ArrayList<>();

    static List<UnitTest> tasks = java.util.Collections.synchronizedList(new LinkedList<UnitTest>());

    static public void threadTask() {
        if (verbose) System.out.println("Launching " + Thread.currentThread().getName());
        UnitTest t;
        while (true) {
            synchronized(tasks) { t = tasks.size() == 0 ? null : tasks.remove(0); }
            if (t == null) {
                if (verbose) System.out.println("Thread " + Thread.currentThread().getName() + " exiting");
                return;
            }
            if (verbose) System.out.println("Thread " + Thread.currentThread().getName() + " has task " + t.method);
            t.run();
            if (verbose) System.out.println("Thread " + Thread.currentThread().getName() + " completed task " + t.method);
        }
    }

    static  public void doMethod(Class<? extends JmlTestCase> clazz, Method method, Constructor constr, Object[] params) {
        synchronized(stests) { tests++; }
        try {
            System.out.println("Testing " + clazz + "." + method.getName() + " using " + Thread.currentThread().getName());
            JmlTestCase t = null;
            try {
                var n = constr.newInstance(params);
                if (n instanceof JmlTestCase) {
                    t = (JmlTestCase)n;
                    t.setUp();
                    method.invoke(t);
                } else if (n instanceof compiler) {
                    compiler tt = (compiler)n;
                    tt.setUp();
                    method.invoke(tt);
                }
            } catch (Throwable e) {
                if (e.getCause() != null) e = e.getCause();
                synchronized(sfailures) { failures++; }
                System.out.println("Test FAILED: " + clazz + "." + method.getName());
                System.out.println(e);
                if (System.getenv("TSTACK") != null) e.printStackTrace(System.out);
            } finally {
                if (t != null) t.tearDown();
                //System.out.println("  Post teardown " + method);
            }
        } catch (Exception e) {
            System.out.println("Failed to construct or execute test: " + method + " " + e);
            if (System.getenv("TSTACK") != null) e.printStackTrace(System.out);
        }
    }

    static class UnitTest implements Runnable {
        final Class<? extends JmlTestCase> clazz;
        final Method method;
        final Constructor constr;
        final Object[] params;

        public UnitTest(final Class<? extends JmlTestCase> clazz, final Method method, final Constructor constr, final Object[] params) {
            this.clazz = clazz;
            this.method = method;
            this.constr = constr;
            this.params = params;
        }

        public void run() {
            Future<?> future = null;
            try {
                future = eservice.submit(()->doMethod(clazz, method, constr, params));
                future.get(seconds, TimeUnit.SECONDS);
            } catch (TimeoutException e) {
                System.out.println("TIMEOUT: " + method + " in thread " + Thread.currentThread().getName());
                synchronized(stimeouts) { timeouts++; }
                future.cancel(true);
                System.out.println("timeout cancelled " + future.isCancelled());
            } catch (Exception e) {
                System.out.println("EXCEPTION: " + method + " " + e);
                synchronized(sfailures) { failures++; }
            } finally {
                if (future != null && !future.isDone()) {
                    System.out.println("PROBLEM: " + method + " not reported as done");
                    future.cancel(true);
                }
                //System.out.println("  Completed " + method);
            }
        }
    }
 }

// This Java program is a custom JUnit command-line runner for OpenJML's unit tests.
// Its arguments are a few options and then the names of OpenJML test suites.
// If no test suites are listed, then all the test suites are run.

// The options allow choosing sequential or parallel running,
// with a given number of threads, given timeout, and verbosity level.

// FIXME -- running with more than one thread does not work because not all of OpenJDK/OpenJML is thread-safe.
package org.openjml.runners;

import org.jmlspecs.openjmltest.*;
import org.jmlspecs.openjmltest.testsuites.*;

import java.lang.reflect.*;
import java.util.*;
import java.util.concurrent.*;
import java.io.*;

public class OpenJMLTestRunner {

    static int numThreads = 0;
    static int seconds = 600;
    static ExecutorService eservice;
    static boolean sequential = true;
    static boolean verbose = false;

    @SuppressWarnings("unchecked")
    public static void main(String... args) throws Exception {
        String th = System.getenv("THREADS");
        if (th != null && !th.isEmpty()) {
            try {
                numThreads = Integer.valueOf(th);
            } catch (Exception e) {
                System.out.println(e);
            }
        }
        while (args.length > 0) {
            if (args[0].equals("-seq")) {
                sequential = true;
                numThreads = 0;
            } else if (args[0].equals("-par")) {
                sequential = false;
                if (numThreads == 0) numThreads = 1;
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
        sequential = numThreads == 0;
        if (!sequential) {
            System.out.println("Concurrent processing of test cases is not implemented fully");
            System.exit(1);
        }

        try {
            eservice = Executors.newFixedThreadPool(numThreads==0?1:numThreads); // argument required to be positive
        } catch (Exception e) {
            System.out.println("Failed to create thread pool for " + numThreads + " threads: " + e);
            System.exit(1);
        }
        var dir = new File(JmlTestSuite.root + "/OpenJML/OpenJMLTest/src/org/jmlspecs/openjmltest/testsuites");
        var lst = args.length == 0 ? dir.list() : args;
        java.util.Arrays.sort(lst);
        for (var item : lst) {
            if (args.length == 0 && !item.endsWith(".java")) continue;
            if (item.endsWith(".java")) item = item.substring(0,item.length()-5);

            String testName = null;
            String suiteName = null;
            String mtestName = null;
            int k = item.indexOf('[');
            if (k > 0) {
                // TODO: Need to generalize this for an arbitrary number and type of parameters -- here it is just a String: the test name
                int kk = item.indexOf('.');
                testName = item.substring(k+1, item.length()-1);
                mtestName = item.substring(kk+1, k);
                suiteName = item.substring(0, kk);
            } else {
                k = item.indexOf('.');
                if (k > 0) {
                    testName = item.substring(k+1);
                    suiteName = item.substring(0,k);
                } else {
                    k = item.indexOf('#');
                    if (k > 0) {
                        testName = item.substring(k+1);
                        suiteName = item.substring(0,k);
                        mtestName = "test"; // FIXME - not all OpenJML parameterized tests use this test name
                    } else {
                        suiteName = item;
                    }
                }
            }
            //System.out.println("SUITE " + suiteName + " METHOD " + mtestName + " TEST " + testName);
            
            Class<JmlTestSuite> clazz;
            try {
                clazz = (Class<JmlTestSuite>)Class.forName("org.jmlspecs.openjmltest.testsuites." + suiteName);
            } catch (ClassNotFoundException e) {
                System.out.println("Error: There is no test suite named " + suiteName);
                failures++;
                continue;
            }

            if (verbose) System.out.println("Queueing " + clazz);
            var cons = clazz.getConstructors();
            if (cons.length != 1) {
                failures++;
                System.out.println("ERROR: Class " + clazz + " should have just one public constructor");
                continue;
            }
            var constr = cons[0];
            
            // Get all methods (which are the test cases) in the test suite
            // Using getMethods, which includes inherited methods, so that we emulate JUnit behavior
            var allmethods = clazz.getMethods();
            var methods = allmethods;
            java.util.Arrays.sort(methods, (a,b)->a.toString().compareTo(b.toString()));
            
            // Replace with just the specific tests if a specific one (or list) has been designated
            if (testName != null) x: {
                methods = new Method[]{};
                if (mtestName == null) {
                    String nm = testName;
                    for (var m: allmethods) {
                        if (m.getName().equals(nm)) {
                            methods = new Method[] { m };
                            break x;
                        }
                    }
                } else {
                    for (var m: allmethods) {
                        if (m.getName().equals(mtestName)) {
                            methods = new Method[] { m };
                            break x;
                        }
                    }
                }
                failures++;
                System.out.println("NO METHOD FOUND FOR " + testName);
            }
            
            // Execute any BeforeClass methods for the suite
            Class c = clazz;
            x: while (c != null) {
                for (var m: c.getDeclaredMethods()) {
                    var a = m.getAnnotationsByType(org.junit.BeforeClass.class);
                    if (a.length != 0) {
                        m.invoke(null); // A BeforeClass method must be public static
                    }
                }
                c = c.getSuperclass();
            }

            // If the tests are parameterized, get the parameters
            // TODO - this is just implemented for the case that the parameters are a list of test names
            // Default is that 'params' is a Collection with a single empty Object[] array
            java.util.Collection<Object[]> params = java.util.Arrays.<Object[]>asList(new Object[0]);
            if (constr.getParameterCount() != 0) {
                // Requires there to be a mtestName
                if (testName == null) {
                    // Do all the parameter sets
                    c = clazz;
                    // Find the static method that is marked with the @Parameters annotation (and is executed to produce the list or parameter arrays)
                    Method pmethod = null;
                    x: while (c != null) {
                        for (var m: c.getDeclaredMethods()) {
                            var a = m.getAnnotationsByType(org.junit.runners.Parameterized.Parameters.class);
                            if (a.length != 0) {
                                pmethod = m;
                                break x;
                            }
                        }
                        c = c.getSuperclass();
                    }
                    if (pmethod == null) {
                        System.out.println("No @Parameters found for " + clazz);
                        continue;
                    }
                    // Execute the found method to get the collection of parameter arrays
                    if (verbose) System.out.println("Found @Parameter: " + pmethod);
                    params = (java.util.Collection<Object[]>)pmethod.invoke(null);
                    if (verbose) System.out.println(params.size() + " PARAMETER SETS");
                } else {
                    // Do just the named test case
                    params = new java.util.LinkedList<Object[]>();
                    params.add( new Object[]{ testName } );
                }
            }
            {
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
        System.exit((failures+timeouts > 0 || tests == 0 )? 1 : 0);
    }

    static Integer tests = 0; static Object stests = new Object();
    static Integer timeouts = 0; static Object stimeouts = new Object();
    static Integer failures = 0; static Object sfailures = new Object();
    static Integer ignores = 0;
    static ArrayList<Thread> threads = new ArrayList<>();

    static List<UnitTest> tasks = java.util.Collections.synchronizedList(new LinkedList<UnitTest>());

    /** Previous code will have created a queue of UnitTest objects. This method takes the front object
        off the queue and then executes it, repeating that action until the queue is empty.
        Note that more than one threadTask may be executing, so access to the queue is synchTest synchronized.
    */
    static public void threadTask() {
        if (verbose) { System.out.println("Launching " + Thread.currentThread().getName()); }
        UnitTest t;
        while (true) {
            // Synchronize here even though we are using a synchronized list, so the size() and remove() calls are in one critical block
            synchronized(tasks) { t = tasks.size() == 0 ? null : tasks.remove(0); }
            if (t == null) {
                if (verbose) { System.out.println("Thread " + Thread.currentThread().getName() + " exiting"); }
                return;
            }
            if (verbose) { System.out.println("Thread " + Thread.currentThread().getName() + " has task " + t.method); }
            t.run(); // Output from the task itself is not synchronized
            if (verbose) { System.out.println("Thread " + Thread.currentThread().getName() + " completed task " + t.method); }
        }
    }

    static class UnitTest implements Runnable {
        final Class<? extends JmlTestSuite> clazz;
        final Method method;
        final Constructor constr;
        final Object[] params;

        public UnitTest(final Class<? extends JmlTestSuite> clazz, final Method method, final Constructor constr, final Object[] params) {
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
                synchronized (System.out) { System.out.println("TIMEOUT: " + method + " in thread " + Thread.currentThread().getName()); }
                synchronized(stimeouts) { timeouts++; }
                future.cancel(true);
                synchronized (System.out) { System.out.println("timeout cancelled " + future.isCancelled()); }
            } catch (Exception e) {
                synchronized (System.out) { System.out.println("EXCEPTION: " + method + " " + e); }
                synchronized(sfailures) { failures++; }
            } finally {
                if (future != null && !future.isDone()) {
                    synchronized (System.out) { System.out.println("PROBLEM: " + method + " not reported as done"); }
                    future.cancel(true);
                }
            }
        }
                
        /** This method is run in the thread doing the testcase and constitutes running the test */
        public void doMethod(Class<? extends JmlTestSuite> clazz, Method method, Constructor constr, Object[] params) {
            String fullname = method.getName() + (params==null||params.length==0?"":Arrays.toString(params));
            String qualname = clazz + "." + fullname;
            synchronized (stests) { tests++; }
            try {
                { System.out.println("Testing " + clazz + "." + method.getName() + (params==null||params.length==0?"":Arrays.toString(params)) + " using " + Thread.currentThread().getName()); }
                JmlTestSuite t = null;
                try {
                    // Essentially, we are creating our own JUnit test runner here, to control the output and metrics
                    // but we ignore some JUnit features such as @Before annotations
                    var n = constr.newInstance(params); // constructs a single test case of the JmlTestSuite
                    if (n instanceof JmlTestSuite tt) {
                        t = tt;
                        t.testname = method.getName(); // FIXME: This is the simple name, not the name + bracketed parameter list
                        t.setUp(); // FIXME - should we use the @Before methods
                        method.invoke(t); // invokes the specific test within the testcase -- any output directly to System.out may be interleaved
                    } else {
                        org.junit.Assert.fail("Test suite " + n.getClass() + " does not extend JmlTestSuite");
                    }
                } finally {
                    if (t != null) t.tearDown(); // FIXME - should we use the @After methods
                }
            } catch (Throwable e) {
                if (e.getCause() != null) e = e.getCause();
                synchronized (sfailures) { failures++; }
                { 
                    System.out.println("Test FAILED: " + qualname);
                    System.out.println("  [Show stack using STACK= ]");
                    System.out.println(e);
                    if (System.getenv("STACK") != null) e.printStackTrace(System.out);
                }
            }
        }
    }
 }

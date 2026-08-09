package com.github.bsideup.jabel;

import java.lang.invoke.*;
import java.lang.reflect.*;

import com.sun.source.util.*;
import com.sun.tools.javac.api.*;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.comp.*;
import com.sun.tools.javac.jvm.*;
import com.sun.tools.javac.util.*;

import sun.misc.*;


@SuppressWarnings({"deprecation", "removal"})
public class JabelCompilerPlugin implements Plugin{
    static final Unsafe unsafe;
    static{
        try{
            Field unsafeField = Unsafe.class.getDeclaredField("theUnsafe");
            unsafeField.setAccessible(true);
            unsafe = (Unsafe)unsafeField.get(null);
        }catch(Exception e){
            throw new RuntimeException(e);
        }

        openCompilerModule();
        forceSourceFeatures();
    }

    @Override
    public void init(JavacTask task, String... args){
        Context context = ((BasicJavacTask)task).getContext();
        patchCachedFeatures(context);
        patchPreview(context);
        removeUnwantedWarnings(context);

        task.addTaskListener(new RecordsRetrofittingTaskListener(context));
        task.addTaskListener(new RecordPatternRetrofittingTaskListener(context));
        task.addTaskListener(new SwitchRetrofittingTaskListener(context));
        task.addTaskListener(new FlexibleMainRetrofittingTaskListener(context));
        task.addTaskListener(new ImplicitClassesRetrofittingTaskListener(context));
    }

    @Override
    public String getName(){
        return "jabel";
    }

    /** Make it auto starts on Java 14+. */
    @Override
    public boolean autoStart(){
        return true;
    }

    /** Play with the JVM to get access to the 'jdk.compiler' packages without '--add-opens' flags. =) */
    static void openCompilerModule() {
        try {
            Class.forName("java.lang.Module");
        } catch (Exception e) {
            return; // No modules on Java 8
        }
        try {
            // Get the trusted lookup that ignores modules checks
            Field implLookupField = MethodHandles.Lookup.class.getDeclaredField("IMPL_LOOKUP");
            long offset = unsafe.staticFieldOffset(implLookupField);
            MethodHandles.Lookup trustedLookup =
                (MethodHandles.Lookup)unsafe.getObject(MethodHandles.Lookup.class, offset);

            // Now use that trusted lookup to open packages
            Module compilerModule = ModuleLayer.boot().findModule("jdk.compiler")
                .orElseThrow(() -> new RuntimeException("jdk.compiler module not found!"));
            MethodHandle addOpens = trustedLookup.findVirtual(
                Module.class,
                "implAddOpens",
                MethodType.methodType(void.class, String.class)
            );
            for (String pkg : compilerModule.getPackages()) {
                addOpens.invokeExact(compilerModule, pkg);
            }

        } catch (Throwable th) {
            // We can't always be lucky ¯\_(ツ)_/¯
            System.err.println("WARNING: Failed to open compiler packages!");
            System.err.println("WARNING: Please add the following arguments to the command:");
            for (String p : new String[] {"api", "code", "comp", "tree", "util", "jvm"}) {
                System.err.println("WARNING:   --add-opens=jdk.compiler/com.sun.tools.javac." + p + "=ALL-UNNAMED");
            }
            throw new RuntimeException(th);
        }
    }

    static void forceSourceFeatures(){
        // We cannot easily force features bellow Java 10.35
        try{
            Class.forName("com.sun.tools.javac.code.Source$Feature");
        }catch(Throwable ignored){
            return;
        }

        try{
            Field featureField = Source.Feature.class.getDeclaredField("minLevel");
            long featureFieldOffset = unsafe.objectFieldOffset(featureField);

            // List of features that are impossible or too difficult to adapt.
            String[] blacklist = {
                "MODULES",               // Extremely difficult as initialization is done very early
                "STRING_TEMPLATES",      // Appeared on Java 21 and removed on Java 23 because of a confusing design
                "MODULE_IMPORTS",        // Needs the modules system
                "JAVA_BASE_TRANSITIVE",  // Needs the modules system
            };

            // We don't care, enable everything except few ones
            for(Source.Feature feat : Source.Feature.values()){
                if(Arrays_contains(blacklist, feat.name())) continue;
                Source current = (Source)unsafe.getObject(feat, featureFieldOffset);
                if(current.ordinal() > Source.JDK8.ordinal()){
                    unsafe.putObject(feat, featureFieldOffset, Source.JDK8);
                }
            }
        }catch(Exception e){
            throw new RuntimeException(e);
        }
    }

    /**
     * Several compiler components cache {@link Source.Feature#allowedInSource()} results. <br>
     * Since these objects may be created <em>before</em> Jabel,
     * this method will try to force all {@code allow*} fields to {@code true}.
     * (except {@code allowModules} fields, because the module system is not yet supported by Jabel)
     */
    static void patchCachedFeatures(Context context){
        Object[] comps = {
            Attr.instance(context),
            Check.instance(context),
            Resolve.instance(context),
        };

        for(Object comp : comps){
            for(Field f : comp.getClass().getDeclaredFields()){
                try{
                    if(f.getType() != boolean.class || !f.getName().startsWith("allow")) continue;
                    if(f.getName().equals("allowModules")) continue; // special case
                    unsafe.putBoolean(comp, unsafe.objectFieldOffset(f), true);
                }catch(Exception ignored){}
             }
        }
    }

    /** Removes warnings about {@code '_'} and preview features. */
    static void removeUnwantedWarnings(Context context){
        Log.instance(context).new DiscardDiagnosticHandler(){
            @Override
            public void report(JCDiagnostic diag){
                String code = diag.getCode();
                if (code.contains("underscore.as.identifier") ||
                    code.contains("use.of.underscore.not.allowed") ||
                    code.startsWith("compiler.warn.preview") ||
                    code.startsWith("compiler.note.preview")) return;
                prev.report(diag);
            }
        };
    }

    static boolean patchPreview(Context context){
        try{
            Class.forName("com.sun.tools.javac.code.Preview");
        }catch(Throwable ignored){
            return false; // the class doesn't exists bellow Java 11.10
        }

        try{
            // Enable preview features
            Field enabledField = Preview.class.getDeclaredField("enabled");
            unsafe.putBoolean(Preview.instance(context), unsafe.objectFieldOffset(enabledField), true);
        }catch(Exception e){
            System.err.println("WARNING: Failed to enable preview features.");
            return false;
        }

        String source = Source.DEFAULT.name;
        // Disable preview for TypeEnter, to avoid implicit StringTemplate import on JDK 21-23
        if (source.equals("21") || source.equals("22") || source.equals("23")) {
            try{
                Symtab.class.getDeclaredField("stringTemplateType"); // Simple check
                Field previewField = TypeEnter.class.getDeclaredField("preview");
                TypeEnter enter = TypeEnter.instance(context);
                unsafe.putObject(enter, unsafe.objectFieldOffset(previewField), Preview.instance(new Context()));
            }catch(Exception ignored){}
        }

        // Disable preview for ClassWriter, to not write preview version to files
        try{
            Field previewField = ClassWriter.class.getDeclaredField("preview");
            ClassWriter writer = ClassWriter.instance(context);
            unsafe.putObject(writer, unsafe.objectFieldOffset(previewField), Preview.instance(new Context()));
        }catch(Exception ignored){}

        return true;
    }

    private static <T> boolean Arrays_contains(T[] arr, T item){
        for(T e : arr){
            if(e == item || e != null && e.equals(item))
                return true;
        }
        return false;
    }
}

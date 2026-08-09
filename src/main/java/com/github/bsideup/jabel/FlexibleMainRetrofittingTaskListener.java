package com.github.bsideup.jabel;

import java.util.*;

import javax.tools.*;

import com.sun.source.util.*;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.util.List;


/**
 * Will adapts flexible entry points ({@code void main();, void main(String[]);, static void main();,
 * static void main(String[])}) by attempting to create a bridge.
 * <p>
 * This is pretty limited as non-static main entry points with arguments cannot be adapted, due to a
 * signature duplication with the static one.
 * <p>
 * Moreover, classes containing multiple entry points with ones that are private,
 * will not work properly on older JVMs. <br>
 * For example this code:
 * <pre>{@code
 * class Main {
 *   static void main() {}
 *   private static void main(String[] args) {}
 * }
 * }</pre>
 * The first main method will be selected by Java 25's JVM, because the standard one is private,
 * whereas on an older JVM, an error will be displayed. <br>
 * And Jabel cannot create a bridge for the first main, because there would be a signature duplication
 * with the second declared main.
 */
public class FlexibleMainRetrofittingTaskListener implements TaskListener{
    // region compiler compatibility

    // Because JCDiagnostic.DiagnosticInfo and ResourceBundle doesn't exists in JDK 8
    private static class WarnMaker{
        static void init(Context context){
            // Proper way to make warnings
            JavacMessages.instance(context).add(locale -> new ResourceBundle(){
                final Map<String, String> keys = new HashMap<>(2);
                {
                    // Act like it's linting
                    keys.put(
                        "jabel.warn.possible.signature.duplication",
                        "[jabel] possible entry point cannot be adapted " +
                        "due to a signature duplication. " +
                        "''{0}'' cannot therefore be used as an entry point in a JVM bellow Java25."
                    );
                    keys.put(
                        "jabel.warn.no.default.constructor.found",
                        "[jabel] possible entry point cannot be adapted " +
                        "because no instanciable default constructor was found. " +
                        "''{0}'' cannot therefore be used as an entry point in a JVM bellow Java25."
                    );
                }

                @Override
                protected Object handleGetObject(String key){
                    return keys.get(key);
                }

                @Override
                public Enumeration<String> getKeys(){
                    return Collections.enumeration(keys.keySet());
                }
            });
        }

        static JCDiagnostic.DiagnosticInfo make(String key, Object arg){
            return new JCDiagnostic.Warning("jabel", key, arg);
        }
    }

    // end region
    // region listener

    final TreeMaker make;
    final Names names;
    final Symtab syms;
    final Log log;
    final JCDiagnostic.Factory diagFactory;
    final Name mainName;

    FlexibleMainRetrofittingTaskListener(Context context){
        make = TreeMaker.instance(context);
        names = Names.instance(context);
        syms = Symtab.instance(context);
        log = Log.instance(context);
        diagFactory = JCDiagnostic.Factory.instance(context);
        mainName = names.fromString("main"); //syms.main;

        try {
            WarnMaker.init(context);
        }catch (Throwable ignored) {}
    }

    @Override
    public void started(TaskEvent e){
        if(e.getKind() != TaskEvent.Kind.ENTER) return;
        if(!(e.getCompilationUnit() instanceof JCCompilationUnit)) return;
        JCCompilationUnit jcu = (JCCompilationUnit)e.getCompilationUnit();
        JavaFileObject old = log.useSource(jcu.sourcefile);

        for(JCTree def : jcu.defs){
            if(!(def instanceof JCClassDecl)) continue;
            transformClass((JCClassDecl)def);
        }

        log.useSource(old);
    }

    @Override
    public void finished(TaskEvent e){}

    public void transformClass(JCClassDecl classDecl){
        make.at(classDecl.pos);

        // Slots: [0]=static+args, [1]=static, [2]=instance+args, [3]=instance
        JCMethodDecl[] mains = new JCMethodDecl[4];
        boolean canInstanciate = false, hasConstructor = false;
        int ep = mains.length;

        for(JCTree def : classDecl.defs){
            if(!(def instanceof JCMethodDecl)) continue;
            JCMethodDecl method = (JCMethodDecl)def;

            if(!isMain(method)){
                if(method.name == names.init){
                    hasConstructor = true;
                    if(!isPrivate(method) && method.params.isEmpty()) canInstanciate = true;
                }
                continue;
            }

            int slot = (isStatic(method) ? 0 : 2) | (method.params.isEmpty() ? 1 : 0);
            if(mains[slot] != null) continue;
            mains[slot] = method;
            if(slot < ep && !isPrivate(method)) ep = slot;
        }

        // To avoid a signature duplication
        if(mains[0] == null && mains[2] != null) ep = 2;

        switch(ep){
            case 1:
                addMainBridge(classDecl, false);
                break;
            case 2:
                warn(mains[ep], "possible.signature.duplication", classDecl.name);
                break;
            case 3:
                if(canInstanciate || !hasConstructor) addMainBridge(classDecl, true);
                else warn(mains[ep], "no.default.constructor.found", classDecl.name);
        }
    }

    public boolean isPrivate(JCMethodDecl m){
        return (m.mods.flags & Flags.PRIVATE) != 0;
    }

    public boolean isStatic(JCMethodDecl m){
        return (m.mods.flags & Flags.STATIC) != 0;
    }

    private void warn(JCMethodDecl method, String key, Object arg){
        try{
            log.report(diagFactory.create(log.currentSource(), method, WarnMaker.make(key, arg)));
        // At this point nothing can be patched, so we don't care at all
        }catch(NoClassDefFoundError ignored){}
    }

    public boolean isMain(JCMethodDecl method){
        if(mainName != method.name) return false;
        if(!(method.restype instanceof JCPrimitiveTypeTree)) return false;
        if(((JCPrimitiveTypeTree)method.restype).typetag != TypeTag.VOID) return false;
        if(method.params.isEmpty()) return true;
        if(method.params.size() != 1) return false;
        JCTree vartype = method.params.head.vartype;
        if(!(vartype instanceof JCArrayTypeTree)) return false;
        // TODO find a better way?
        switch(((JCArrayTypeTree)vartype).getType().toString()){
            case "java.lang.String":
            case "String":
                return true;
            default:
                return false;
        }
    }

    /** If {@code toLocalMain} is {@code true}, a zero-arg constructor must be present. */
    public JCMethodDecl makeMainBridge(JCClassDecl classDecl, boolean toLocalMain){
        return make.MethodDef(
            make.Modifiers(Flags.PUBLIC | Flags.STATIC),
            mainName,
            make.TypeIdent(TypeTag.VOID),
            List.nil(),
            List.of(make.VarDef(
                make.Modifiers(Flags.PARAMETER), names.fromString("args"),
                make.TypeArray(make.Type(syms.stringType)), null
            )),
            List.nil(),
            make.Block(0, List.of(make.Exec(make.Apply(
                List.nil(),
                toLocalMain ? make.Select(
                    make.NewClass(null, List.nil(), make.Ident(classDecl.name), List.nil(), null),
                    mainName
                ) : make.Select(make.Ident(classDecl.name), mainName),
                List.nil()
            )))),
            null
        );
    }

    /** Creates a main bridge in the specified class. */
    public void addMainBridge(JCClassDecl classDecl, boolean toLocalMain){
        classDecl.defs = classDecl.defs.append(makeMainBridge(classDecl, toLocalMain));
    }

    // end region
}
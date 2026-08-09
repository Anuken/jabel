package com.github.bsideup.jabel;

import com.sun.source.util.*;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;


/**
 * Because implicit classes import the {@code java.base} module, and modules are not yet supported,
 * we need to convert it by adding star import of all exported and existing packages.
 */
public class ImplicitClassesRetrofittingTaskListener implements TaskListener{
    final TreeMaker make;
    final Names names;
    final Symtab syms;
    List<JCImport> javaBaseImports;

    ImplicitClassesRetrofittingTaskListener(Context context){
        make = TreeMaker.instance(context);
        names = Names.instance(context);
        syms = Symtab.instance(context);
    }

    @Override
    public void started(TaskEvent e){
        if(e.getKind() != TaskEvent.Kind.ENTER) return;
        if(!(e.getCompilationUnit() instanceof JCCompilationUnit)) return;
        JCCompilationUnit jcu = (JCCompilationUnit)e.getCompilationUnit();

        for(JCTree def : jcu.defs){
            if(!(def instanceof JCClassDecl)) continue;
            JCClassDecl clazz = (JCClassDecl)def;
            if((clazz.mods.flags & Flags.IMPLICIT_CLASS) == 0) continue;
            clazz.mods.flags &= ~Flags.IMPLICIT_CLASS; // Avoid implicit importation of java.base
            injectJavaBaseImports(jcu);
        }
    }

    @Override
    public void finished(TaskEvent e){}

    @SuppressWarnings("unchecked")
    public void injectJavaBaseImports(JCCompilationUnit jcu){
        if (javaBaseImports == null) javaBaseImports = makeStarImports(getJavaBasePackages());
        // Duplicate imports are not important
        jcu.defs = ((List<JCTree>)(List<?>)javaBaseImports).appendList(jcu.defs);
    }

    /** @return the list of packages that are exported by the {@code java.base} modules. */
    public List<Symbol.PackageSymbol> getJavaBasePackages(){
        // Since modules are not enabled and initialized, {@code syms.java_base.exports} is not populated
        return ModuleLayer.boot().findModule("java.base").map(mod ->
            mod.getPackages().stream()
               .filter(mod::isExported)
               .map(p -> syms.enterPackage(syms.java_base, names.fromString(p)))
               .filter(p -> {
                   try {
                       p.complete();
                   } catch(Exception ignored) {}
                   return p.exists();
               })
               .collect(List.collector())
        ).orElse(List.nil());
    }

    public List<JCImport> makeStarImports(List<Symbol.PackageSymbol> packages) {
        List<JCImport> imports = List.nil();
        for(Symbol.PackageSymbol pkg : packages){
            imports = imports.append(make.Import(make.Select(
                make.QualIdent(pkg),
                names.asterisk
            ), false));
        }
        return imports;
    }
}
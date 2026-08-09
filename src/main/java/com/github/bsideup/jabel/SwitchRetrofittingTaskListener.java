package com.github.bsideup.jabel;

import java.lang.reflect.Method;
import java.util.*;

import com.sun.source.tree.*;
import com.sun.source.util.*;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.*;
import com.sun.tools.javac.comp.*;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;
import com.sun.tools.javac.util.JCDiagnostic.*;
import com.sun.tools.javac.util.List;


/**
 * Transforms modern switch constructs (Java 17+) into Java 8 compatible code.
 * <p><br>
 * This listener will rewrite entirely the switch for a better one.
 * <p>
 * Instead of placing the guard in the case body, it will be evaluated in the switch condition. <br>
 * Avoiding restarting the switch everytimes a guard fail,
 * and storing an index to not reevaluate previous cases.
 * <p>
 * So this method will convert cases labels into a ternary-chain that will placed in the switch condition. <br>
 * And case labels will be changed to match their position in the switch.
 * <p>
 * Also, to avoid double method calls, if the switch condition was a method call,
 * an uninitialized variable is inserted in the previous line, and then initialized in the ternary-chain. <br>
 * Same way goes for cases using a record-pattern with a guard using a component from that record.
 */
public class SwitchRetrofittingTaskListener implements TaskListener{
    // region compiler compatibility

    // Because we're compiling with JDK 25, the old method (without guards) doens't exists.
    private static Method LEGACY_MAKE_CASE;
    // Some internal states to avoid getting errors everytimes we trying to use a found feature.
    // true means that the feature is not present, by default assuming it is.
    private static boolean GUARD, LABELS, BODY, DEFAULT_CASE, CONSTANT_CASE, PATTERN_MATCHING_CATCH, SWITCH_PATTERN;
    /*private*/ static boolean MATCH_EXCEPTION_PRESENT;

    static{
        try{
            Symtab.class.getDeclaredField("matchExceptionType");
            MATCH_EXCEPTION_PRESENT = true;
        }catch(Exception ignored){}
    }

    /** Get the guard expression from a case, or null if guards are unsupported. */
    private static JCExpression getGuard(JCCase caseTree){
        if(GUARD) return null;
        try{
            return caseTree.getGuard();
        }catch(NoSuchMethodError ignored){
            GUARD = true;
            return null;
        }
    }

    /** Get the labels from a case, handling both old and new compiler APIs. */
    @SuppressWarnings("unchecked")
    private static List<JCTree> getLabels(JCCase caseTree){
        if(!LABELS){
           try{
                return (List<JCTree>)(List<? extends JCTree>)caseTree.getLabels();
            }catch(NoSuchMethodError ignored){
                LABELS = true;
            }
        }

        List<JCExpression> labels = caseTree.getExpressions();
        if(labels == null) return List.nil();
        List<JCTree> result = List.nil();
        for(Object label : labels){
            if(!(label instanceof JCTree)) continue;
            result = result.append((JCTree)label);
        }
        return result;
    }

    /** Get the arrow-style body of a case, or null if unsupported. */
    private static JCTree getBody(JCCase caseTree){
        if(BODY) return null;
        try{
            return caseTree.getBody();
        }catch(NoSuchMethodError ignored){
            BODY = true;
            return null;
        }
    }

    //TODO: CaseTree.CaseKind doesn't exists on Java 12-
    //EDIT: Seems to not be a real problem...
    /**
     * Create a new case tree, handling different JDK signatures. <br>
     * JDK 21+: Case(CaseKind, List labels, JCExpression guard, List stats, JCTree body) <br>
     * JDK 17-20: Case(CaseKind, List labels, List stats, JCTree body)
     */
    @SuppressWarnings("unchecked")
    private JCCase makeCase(CaseTree.CaseKind kind, List<? extends JCTree> labels,
                            List<JCStatement> stats, JCTree body){
        // A default case is one that have no labels on JDK < 17
        if(!labels.isEmpty() && labels.head == null) labels = List.nil();

        if(!GUARD){
            try{
                return make.Case(kind, (List<JCCaseLabel>)labels, null, stats, body);
            }catch(NoSuchMethodError ignored){
                GUARD = true;
            }
        }

        try{
            if(LEGACY_MAKE_CASE == null){
                LEGACY_MAKE_CASE = TreeMaker.class.getMethod(
                    "Case", CaseTree.CaseKind.class, List.class, List.class, JCTree.class
                );
            }
            return (JCCase)LEGACY_MAKE_CASE.invoke(make, kind, labels, stats, body);
        }catch(Exception ignored){// Hope this never happen...
            System.err.println("[jabel] Failed to make case with labels: " + labels);
        }
        return null;
    }

    // Because the return type of these two methods may not exist, we need delay the call to an inner class.
    // Like that, the class initialization error can be catched easily.
    private static final class DefaultCaseLabelFactory{
        static JCTree make(TreeMaker m){
            return m.DefaultCaseLabel();
        }
    }
    private static final class ConstantCaseLabelFactory{
        static JCTree make(TreeMaker m, JCExpression lit){
            return m.ConstantCaseLabel(lit);
        }
    }

    /** Create a default case label. Returns null if unsupported (JDK < 17). */
    private JCTree makeDefaultCaseLabel(){
        if(DEFAULT_CASE) return null;
        try{
            return DefaultCaseLabelFactory.make(make);
        }catch(NoSuchMethodError | NoClassDefFoundError ignored){
            DEFAULT_CASE = true;
            return null;
        }
    }

    /** Creates a case label for an {@code Integer}, handling JDK 17-20 and 21+ APIs. */
    private JCTree makeLabel(int i){
        JCLiteral lit = make.Literal(i);
        if(CONSTANT_CASE) return lit;
        try{
            return ConstantCaseLabelFactory.make(make, lit); // JDK 21+
        }catch(NoSuchMethodError | NoClassDefFoundError ignored){
            CONSTANT_CASE = true;
            return lit; // JDK 17-20
        }
    }

    private static final class PatternMatchingCatchAccess{
        static void attach(JCBlock block, JCCatch handler, Set<JCMethodInvocation> calls){
            block.patternMatchingCatch = new JCBlock.PatternMatchingCatch(handler, calls);
        }

        static JCCatch handler(JCBlock block){
            if(block.patternMatchingCatch == null) return null;
            return block.patternMatchingCatch.handler();
        }
    }

    /*private*/ static JCCatch getPatternMatchingCatchHandler(JCBlock block){
        if(PATTERN_MATCHING_CATCH) return null;
        try{
            return PatternMatchingCatchAccess.handler(block);
        }catch(NoSuchFieldError | NoClassDefFoundError ignored){
            PATTERN_MATCHING_CATCH = true;
            return null;
        }
    }

    private static void attachPatternMatchingCatch(JCBlock block, JCCatch body, Set<JCMethodInvocation> calls){
        if(PATTERN_MATCHING_CATCH) return;
        try{
            PatternMatchingCatchAccess.attach(block, body, calls);
        }catch(NoSuchFieldError | NoClassDefFoundError ignored){
            PATTERN_MATCHING_CATCH = true;
        }
    }

    /** Sets {@code patternSwitch = false} on a switch, silently ignoring JDK < 17. */
    private static void clearPatternSwitchStatus(JCTree tree){
        if(SWITCH_PATTERN) return;
        try {
            switch(getClassName(tree)){
                case "JCSwitch":
                    ((JCSwitch)tree).patternSwitch = false;
                    break;
                case "JCSwitchExpression":
                    ((JCSwitchExpression)tree).patternSwitch = false;
                    break;
            }
        }catch(NoSuchFieldError | NoClassDefFoundError ignored){
            SWITCH_PATTERN = true;
        }
    }


    private static String getClassName(Object obj){
        return obj == null ? "" : obj.getClass().getSimpleName();
    }

    private static boolean isBindingPattern(JCTree pattern){
        return pattern != null && getClassName(pattern).equals("JCBindingPattern");
    }

    private static boolean isRecordPattern(JCTree pattern){
        return pattern != null && getClassName(pattern).equals("JCRecordPattern");
    }

    /** Check if this tree node is a pattern (binding, record, case label, or any). */
    private static boolean isPattern(JCTree label){
        if(label == null) return false;
        String name = getClassName(label);
        return name.contains("Pattern") || name.contains("Binding");
    }

    private static boolean isSwitchExpression(JCTree tree){
        return tree != null && getClassName(tree).equals("JCSwitchExpression");
    }

    private static boolean isDefault(JCTree label){
        return label != null && getClassName(label).equals("JCDefaultCaseLabel");
    }

    private static boolean isConstant(JCTree label){
        return label != null && getClassName(label).equals("JCConstantCaseLabel");
    }

    private static boolean isNull(JCTree label){
        if(label instanceof JCLiteral) return ((JCLiteral)label).typetag == TypeTag.BOT;
        if(!isConstant(label)) return false;
        JCExpression expr = ((JCConstantCaseLabel)label).expr;
        return expr instanceof JCLiteral && ((JCLiteral)expr).typetag == TypeTag.BOT;
    }

    private boolean isComplex(JCExpression e){
        if(e instanceof JCIdent || e instanceof JCLiteral) return false;
        if(e instanceof JCFieldAccess) return isComplex(((JCFieldAccess)e).selected);
        if(e instanceof JCParens) return isComplex(((JCParens)e).expr);
        return true;
    }

    /** @return {@code true} if {@code expr} is structurally an enum constant reference. */
    private static boolean isEnumConstant(JCExpression expr){
        return (expr instanceof JCIdent || expr instanceof JCFieldAccess)
            && !(expr instanceof JCLiteral);
    }

    private JCExpression getExpression(JCTree body){
        if(body instanceof JCExpressionStatement) return ((JCExpressionStatement)body).expr;
        if(body instanceof JCExpression) return (JCExpression)body;
        return null;
    }

    private static JCExpression getLabelExpression(JCTree label){
        if(label instanceof JCExpression) return (JCExpression)label;
        if(isConstant(label)) return ((JCConstantCaseLabel)label).expr;
        return null;
    }

    /**
     * Because {@link JCPatternCaseLabel#pat} type is {@link JCPattern},
     * we need to delay access to an inner class. <br>
     * Like that, the class initialization error can be catched easily.
     */
    private static final class PatternCaseLabelAccess{
        static JCTree pat(JCTree label){
            return ((JCPatternCaseLabel)label).pat;
        }
    }

    /** Get the binding variable from a pattern (binding pattern or pattern case label). */
    private static JCVariableDecl getPatternVar(JCTree label){
        if(label == null) return null;
        switch(getClassName(label)){
            case "JCBindingPattern": return ((JCBindingPattern)label).var;
            case "JCPatternCaseLabel": return getPatternVar(PatternCaseLabelAccess.pat(label));
            default: return null;
        }
    }

    /**
     * Get the type from a pattern label (for instanceof check).
     * Works for binding patterns, pattern case labels, and unnamed patterns.
     */
    private static JCExpression getPatternType(JCTree label){
        if(label == null) return null;
        switch(getClassName(label)){
            case "JCBindingPattern":
                JCVariableDecl var = ((JCBindingPattern)label).var;
                return var != null ? var.vartype : null;
            case "JCPatternCaseLabel": return getPatternType(PatternCaseLabelAccess.pat(label));
            //case "JCAnyPattern": return getAnyPatternType(label);
            default: return null;
        }
    }

    /** Get the record type from a record pattern or pattern case label. */
    private static JCExpression getRecordType(JCTree label){
        if(label == null) return null;
        switch(getClassName(label)){
            case "JCRecordPattern": return ((JCRecordPattern)label).deconstructor;
            case "JCPatternCaseLabel": return getRecordType(PatternCaseLabelAccess.pat(label));
            default: return null;
        }
    }

    /** Get nested patterns from a record pattern or pattern case label. */
    private static List<? extends JCTree> getRecordNested(JCTree label){
        if(label == null) return null;
        switch(getClassName(label)){
            case "JCRecordPattern": return ((JCRecordPattern)label).nested;
            case "JCPatternCaseLabel": return getRecordNested(PatternCaseLabelAccess.pat(label));
            default: return null;
        }
    }

    private static boolean hasDefault(List<JCCase> cases){
        if(cases == null) return true;
        for(JCCase c : cases){
            if(c == null) continue;
            List<JCTree> labels = getLabels(c);
            if(labels.isEmpty()) return true;
            for(JCTree label : labels){
                if(isDefault(label)) return true;
            }
        }
        return false;
    }

    private static boolean hasRecordPatterns(List<JCCase> cases){
        if(cases == null) return false;
        for(JCCase c : cases){
            if(c == null) continue;
            for(JCTree l : getLabels(c)){
                if(getRecordType(l) != null) return true;
            }
        }
        return false;
    }

    private static boolean hasGuardRecordPatterns(List<JCCase> cases){
        if(cases == null) return false;
        for(JCCase c : cases){
            if(c == null || getGuard(c) == null) continue;
            for(JCTree l : getLabels(c)){
                if(getRecordType(l) != null) return true;
            }
        }
        return false;
    }

    /** @return whether case labels contains things not handled by a standard switch. */
    private static boolean needsTransform(List<JCCase> cases){
        if(cases == null) return false;
        for(JCCase c : cases){
            if(c == null) continue;
            if(getGuard(c) != null) return true;
            for(JCTree label : getLabels(c)){
                if(isPattern(label) || isNull(label)) return true;
                JCExpression expr = getLabelExpression(label);
                if(!(expr instanceof JCLiteral)) continue;
                switch(((JCLiteral)expr).typetag){
                    case FLOAT:
                    case DOUBLE:
                    case LONG:
                        return true;
                    default:
                }
            }
        }
        return false;
    }

    /** @return whether all cases are just enum constants with a {@code null} and/or an unconditional pattern. */
    private static boolean isEnumSwitch(List<JCCase> cases){
        if(cases == null) return false;
        boolean hasEnumConstant = false, hasUnguardedPattern = false;
        for(JCCase c : cases){
            if(c == null) continue;
            if(getGuard(c) != null) return false;
            for(JCTree label : getLabels(c)){
                if(isDefault(label) || isNull(label)) continue;
                if(isPattern(label)){
                    if(hasUnguardedPattern) return false;
                    hasUnguardedPattern = true;
                    continue;
                }
                JCExpression expr = getLabelExpression(label);
                if(expr == null || !isEnumConstant(expr)) return false;
                hasEnumConstant = true;
            }
        }
        return hasEnumConstant;
    }


    //NOTE: Operators class doesn't exists on JDK 8
    static Method resolveBinary;
    static boolean HAS_OPERATORS = true;
    static {
        try{
            resolveBinary = Operators.class.getDeclaredMethod(
                "resolveBinary", DiagnosticPosition.class, Tag.class, Type.class, Type.class
            );
            resolveBinary.setAccessible(true);
        }catch(Exception ignored){
        }catch (Throwable ignored) {
            HAS_OPERATORS = false;
        }
    }

    /*private*/ static OperatorSymbol resolveBinary(Operators ops, DiagnosticPosition pos, Tag tag, Type op1, Type op2){
        if(resolveBinary != null){
            try{
                return (OperatorSymbol)resolveBinary.invoke(ops, pos, tag, op1, op2);
            } catch(Exception e){
                System.err.println("[jabel] Failed to find operator " + tag + " with " + op1 + "," + op2);
            }
        }
        return null;
    }

    // end region
    // region task listener

    final Context context;
    final TreeMaker make;
    final Symtab syms;
    final Names names;
    final Types types;
    /*final*/ Object/*Operators*/ ops;
    final Attr attr;
    final SymTreeCopier<Void> copier;

    private int tempVarCounter;
    private Set<JCMethodInvocation> pendingAccessorCalls = null;
    private Map<JCCase, Map<Name, VarSymbol>> guardPreVars = null;
    private MethodSymbol currentMethodSym;
    private boolean cacheResolved, useMatchException;
    private MethodSymbol object_equals, object_toString, object_getClass, enum_ordinal, class_getName,
                         float_floatToIntBits, double_doubleToLongBits, icce_ctor, me_ctor;

    public SwitchRetrofittingTaskListener(Context context){
        this.context = context;
        make = TreeMaker.instance(context);
        syms = Symtab.instance(context);
        names = Names.instance(context);
        types = Types.instance(context);
        if (HAS_OPERATORS) ops = Operators.instance(context);
        attr = Attr.instance(context);
        copier = new SymTreeCopier<Void>(make);
    }

    @Override
    public void started(TaskEvent e){}

    @Override
    public void finished(TaskEvent e){
        if(e.getKind() != TaskEvent.Kind.ANALYZE) return;
        if(!(e.getCompilationUnit() instanceof JCCompilationUnit)) return;
        new SwitchTranslator().translate((JCCompilationUnit)e.getCompilationUnit());
    }


    public class SwitchTranslator extends TreeTranslator{
        /** Captures the original selector of a switch expression before replacement by a temp var. */
        private final Map<JCTree, JCExpression> captures = new HashMap<>();
        private Set<JCMethodInvocation> blockAccessorCalls = null;
        private ClassSymbol currentClass;

        // Symbol tracking
        @Override
        public void visitClassDef(JCClassDecl tree){
            ClassSymbol prevClass = currentClass;
            MethodSymbol prevMethod = currentMethodSym;
            try{
                currentClass = tree.sym;
                currentMethodSym = null;
                super.visitClassDef(tree);
            }finally{
                currentClass = prevClass;
                currentMethodSym = prevMethod;
            }
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree){
            MethodSymbol prev = currentMethodSym;
            try{
                currentMethodSym = tree.sym;
                super.visitMethodDef(tree);
            }finally{
                currentMethodSym = prev;
            }
        }

        @Override
        public void visitBlock(JCBlock tree){
            MethodSymbol prev = currentMethodSym;
            // Save and reset blockAccessorCalls for this block scope
            Set<JCMethodInvocation> prevCalls = blockAccessorCalls;
            blockAccessorCalls = null;
            try{
                if(currentMethodSym == null && currentClass != null){
                    currentMethodSym = new MethodSymbol(
                        tree.flags | Flags.BLOCK, names.empty, null, currentClass
                    );
                }
                ListBuffer<JCStatement> buffer = null;
                for(JCStatement stmt : tree.stats){
                    buffer = prepareExprSwitchPrefix(stmt, buffer, tree.stats);
                    if(buffer != null) buffer.append(stmt);
                }
                if(buffer != null) tree.stats = buffer.toList();
                super.visitBlock(tree);

                // Attach patternMatchingCatch to this block if accessor calls were collected
                if(blockAccessorCalls != null){
                    pendingAccessorCalls = blockAccessorCalls;
                    blockAccessorCalls = null;
                    attachPatternMatchingCatch(tree);
                }
            }finally{
                // Propagate remaining calls to the parent scope
                if(blockAccessorCalls != null){
                    if(prevCalls == null) prevCalls = blockAccessorCalls;
                    else prevCalls.addAll(blockAccessorCalls);
                }
                blockAccessorCalls = prevCalls;
                currentMethodSym = prev;
            }
        }

        @Override
        public void visitVarDef(JCVariableDecl tree){
            MethodSymbol prev = currentMethodSym;
            try{
                if(currentMethodSym == null && currentClass != null){
                    currentMethodSym = new MethodSymbol(
                        (tree.mods.flags & Flags.STATIC) | Flags.BLOCK, names.empty, null, currentClass
                    );
                }
                super.visitVarDef(tree);
            }finally{
                currentMethodSym = prev;
            }
        }

        @Override
        public void visitSwitch(JCSwitch tree){
            super.visitSwitch(tree);
            if(!needsTransform(tree.cases)) return;
            clearPatternSwitchStatus(tree); // TransPatterns must not re-process our output

            make.at(tree.pos);
            ListBuffer<JCStatement> prefix = new ListBuffer<>();
            JCExpression sel = captureSelector(tree.selector, prefix, true);
            buildGuardPreDecls(tree.cases, prefix);
            JCSwitch ns = transformSwitch(tree, sel, tree.cases, false, null);
            tree.selector = ns.selector;
            tree.cases = ns.cases;

            collectAccessorCalls();
            if(prefix.isEmpty()) return;
            prefix.append(tree);
            result = make.Block(0, prefix.toList());
        }

        private ListBuffer<JCStatement> prepareExprSwitchPrefix(JCStatement stmt, ListBuffer<JCStatement> buffer,
                                                                List<JCStatement> allStats){
            List<JCTree> found = findPatternSwitches(stmt);
            if (found.isEmpty()) return buffer;

            boolean needsBuffer = false;
            for(JCTree tree : found){
                JCSwitchExpression sw = (JCSwitchExpression)tree;
                if(isComplex(sw.selector) || hasGuardRecordPatterns(sw.cases)){
                    needsBuffer = true;
                    break;
                }
            }
            if(!needsBuffer) return buffer;

            if(buffer == null){
                ListBuffer<JCStatement> buf = new ListBuffer<>();
                for(JCStatement s : allStats){
                    if(s == stmt) break;
                    buf.append(s);
                }
                buffer = buf;
            }

            for(JCTree tree : found){
                JCSwitchExpression sw = (JCSwitchExpression)tree;
                JCExpression sel = captureSelector(sw.selector, buffer, false);
                if(sel != sw.selector){
                    captures.put(tree, sw.selector);
                    sw.selector = sel;
                }
                if(needsTransform(sw.cases)) buildGuardPreDecls(sw.cases, buffer);
            }
            return buffer;
        }

        @Override
        public <T extends JCTree> T translate(T tree){
            if(tree == null) return null;
            if(!isSwitchExpression(tree)) return super.translate(tree);
            clearPatternSwitchStatus(tree);

            JCSwitchExpression sw = (JCSwitchExpression)tree;
            make.at(sw.pos);
            JCExpression rawSel = captures.remove(sw);
            sw.selector = translate(sw.selector);
            sw.cases = translate(sw.cases);

            if(needsTransform(sw.cases)){
                JCSwitch ns = transformSwitch(tree, sw.selector, sw.cases, true, rawSel);
                sw.selector = ns.selector;
                sw.cases = ns.cases;
                collectAccessorCalls();
            }else{
                sw.cases = injectDefault(sw.selector, sw.cases);
            }
            return tree;
        }

        /** TreeTranslator skips the arrow body field. */
        @Override
        public void visitCase(JCCase tree){
            super.visitCase(tree);
            JCTree body = getBody(tree);
            if(body == null) return;
            JCTree saved = result;
            tree.body = translate(body);
            result = saved;
        }

        /** Moves pendingAccessorCalls into blockAccessorCalls. */
        private void collectAccessorCalls(){
            if(pendingAccessorCalls == null) return;
            if(blockAccessorCalls == null) blockAccessorCalls = new HashSet<>();
            blockAccessorCalls.addAll(pendingAccessorCalls);
            pendingAccessorCalls = null;
        }
    }


    @SuppressWarnings("unchecked")
    public List<JCTree> findPatternSwitches(JCTree node){
        ListBuffer<JCSwitchExpression> out = new ListBuffer<>();
        new TreeScanner<Void, Void>(){
            @Override
            public Void scan(Tree t, Void v){
                if(t == null) return null;
                if(!isSwitchExpression((JCTree)t)) return super.scan(t, v);
                JCSwitchExpression se = (JCSwitchExpression)t;
                if(needsTransform(se.cases)) out.append(se);
                return null;
            }
        }.scan(node, null);
        return (List<JCTree>)(List<? extends JCTree>)out.toList();
    }

    /** Builds the standard switch from a pattern/null switch. */
    public JCSwitch transformSwitch(JCTree currentSwitch, JCExpression sel, List<JCCase> cases,
                                    boolean expression, JCExpression rawSel){
        pendingAccessorCalls = hasRecordPatterns(cases) ? new HashSet<>() : null;

        boolean isEnum = isEnumSwitch(cases), hasNull = false;
        List<JCTree> labels = List.nil();
        List<JCCase> slotCases = List.nil();

        // Analyze case and labels
        for(JCCase c : cases){
            JCTree last = null;
            for(JCTree label : getLabels(c)){
                if(isNull(label)){
                    hasNull = true;
                    continue;
                }
                if(isDefault(label) || (isEnum && isPattern(label))) continue;
                if(last != null){
                    labels = labels.append(last);
                    slotCases = slotCases.append(null);
                }
                last = label;
            }
            if(last != null){
                labels = labels.append(last);
                slotCases = slotCases.append(c);
            }
        }

        return make.Switch(
            isEnum
                ? buildEnumSwitchCondition(sel, hasNull, rawSel)
                : buildTypeSwitchCondition(sel, hasNull, labels, slotCases, rawSel),
            prepareSwichCases(currentSwitch, sel, expression, isEnum, cases, labels)
        );
    }

    public List<JCCase> prepareSwichCases(JCTree currentSwitch, JCExpression sel, boolean isExpression,
                                          boolean isEnum, List<JCCase> cases, List<JCTree> labels) {
        ListBuffer<JCCase> newCases = new ListBuffer<>();
        JCCase nc;
        JCStatement body;
        boolean defaultEmitted = false;
        int i = 0;

        for(JCCase c : cases){
            JCTree lastNormal = null;
            boolean seenNull = false, seenDefault = false;
            List<JCTree> caseLabels = getLabels(c);

            // Scan for "null" and "default" labels
            for(JCTree label : caseLabels){
                if(isNull(label)) seenNull = true;
                else if(isDefault(label) || (isEnum && isPattern(label))) seenDefault = true;
                else lastNormal = label;
            }

            // Emit fall-through slots
            for(JCTree label : caseLabels){
                if(isNull(label) || isDefault(label) || (isEnum && isPattern(label))) continue;
                if(label == lastNormal) break;
                int lv = isEnum ? getEnumOrdinal(getLabelExpression(label)) : i++;
                if(lv < 0) continue;
                nc = makeStatementCase(makeLabel(lv), List.nil());
                if(nc != null) newCases.append(nc);
            }

            // Emit the last normal label
            if(lastNormal != null){
                int lv = isEnum ? getEnumOrdinal(getLabelExpression(lastNormal)) : i++;
                if(lv >= 0){
                    body = make.Block(0, buildCaseBody(currentSwitch, c, sel, isExpression));
                    nc = makeStatementCase(makeLabel(lv), List.of(body));
                    if(nc != null) newCases.append(nc);
                }
            }

            // Emit null slot at its original position
            if(seenNull){
                // In case of null and default are on the same case
                body = seenDefault
                    ? null
                    : make.Block(0, buildCaseBody(currentSwitch, c, sel, isExpression));
                nc = makeStatementCase(makeLabel(-1), body == null ? List.nil() : List.of(body));
                if(nc != null) newCases.append(nc);
            }

            // Emit default slot at its original position
            if(seenDefault && !defaultEmitted){
                defaultEmitted = true;
                body = make.Block(0, buildCaseBody(currentSwitch, c, sel, isExpression));
                nc = makeStatementCase(makeDefaultCaseLabel(), List.of(body));
                if(nc != null) newCases.append(nc);
            }
        }

        // Emit default case for exhaustive switches
        if(!defaultEmitted){
            body = makeMatchExceptionThrow(sel, !isEnum);
            nc = makeStatementCase(makeDefaultCaseLabel(), List.of(body));
            if(nc != null) newCases.append(nc);
        }

        return newCases.toList();
    }

    /** Builds a simple {@code sel == null ? -1 : sel.ordinal()} condition. */
    public JCExpression buildEnumSwitchCondition(JCExpression sel, boolean hasNull, JCExpression rawSel){
        resolveMethodsCache();
        VarSymbol selSym = (sel instanceof JCIdent && ((JCIdent)sel).sym instanceof VarSymbol)
            ? (VarSymbol)((JCIdent)sel).sym : null;
        JCExpression base = makeMethodCall(sel, enum_ordinal);
        if(hasNull) base = makeConditional(makeBinary(Tag.EQ, sel, makeNull()), make.Literal(-1), base);
        return rawSel != null && selSym != null ? assignSwitchSelector(base, selSym, rawSel) : base;
    }

    /** Builds a ternary chain and groups the same type-pattern. */
    public JCExpression buildTypeSwitchCondition(JCExpression sel, boolean hasNull, List<JCTree> labels,
                                                 List<JCCase> slotCases, JCExpression rawSel){
        int n = labels.size();
        Map<Symbol, JCConditional> group = new HashMap<>();
        JCExpression[] anchor = new JCExpression[n];

        for(int i = 0; i < n; i++, labels = labels.tail, slotCases = slotCases.tail){
            JCExpression pt = getPatternTypeForGrouping(labels.head);
            Symbol tsym = pt != null && pt.type != null ? types.erasure(pt.type).tsym : null;

            if(tsym == null){
                anchor[i] = buildLabelCondition(labels.head, sel);
                continue;
            }

            JCExpression guard = buildGuard(labels.head, sel, slotCases.head);
            JCConditional open = group.get(tsym);

            if(open == null){
                JCExpression thenpart;
                if(guard != null){
                    thenpart = makeConditional(guard, make.Literal(i), make.Literal(n));
                    group.put(tsym, (JCConditional)thenpart);
                }else{
                    thenpart = make.Literal(i);
                }
                anchor[i] = makeConditional(makeTypeTest(sel, pt), thenpart, make.Literal(n));
            }else{
                anchor[i] = null;
                if(guard != null){
                    JCConditional next = makeConditional(guard, make.Literal(i), make.Literal(n));
                    open.falsepart = next;
                    open.type = syms.intType;
                    group.put(tsym, next);
                }else{
                    open.falsepart = make.Literal(i);
                    open.type = syms.intType;
                    group.remove(tsym);
                }
            }
        }

        // Assemble ternary chain
        sel = TreeInfo.skipParens(sel);
        VarSymbol selSym = (sel instanceof JCIdent && ((JCIdent)sel).sym instanceof VarSymbol)
            ? (VarSymbol)((JCIdent)sel).sym : null;
        boolean inlineInNull = hasNull && rawSel != null && selSym != null;
        JCExpression ternary = make.Literal(n);

        // Null check
        if(!hasNull && sel.type != null && !sel.type.isPrimitive() && selSym != null){
            rawSel = attr.makeNullCheck(rawSel != null ? rawSel : sel);
        }

        for(int i = n - 1; i >= 0; i--){
            JCExpression cond = anchor[i];
            if(cond == null) continue;
            if(i == 0 && !inlineInNull && rawSel != null && selSym != null){
                cond = assignSwitchSelector(cond, selSym, rawSel);
            }
            if(cond instanceof JCConditional){
                ((JCConditional)cond).falsepart = ternary;
                ternary = cond;
            }else{
                ternary = makeConditional(cond, make.Literal(i), ternary);
            }
        }
        // In case of
        if(rawSel != null && selSym != null && !inlineInNull && n > 0 && anchor[0] == null){
            ternary = assignSwitchSelector(ternary, selSym, rawSel);
        }

        if(hasNull){
            JCExpression nullSel = inlineInNull ? makeAssignParens(selSym, rawSel) : sel;
            ternary = makeConditional(makeBinary(Tag.EQ, nullSel, makeNull()), make.Literal(-1), ternary);
        }

        return (n == 0 && rawSel != null && selSym != null) ? makeAssignParens(selSym, rawSel) : ternary;
    }

    private JCExpression getPatternTypeForGrouping(JCTree label){
        if(!isPattern(label)) return null;
        JCVariableDecl pv = getPatternVar(label);
        if(pv != null) return pv.vartype;
        return getRecordType(label);
    }

    /** Cache enum values. */
    //TODO: maybe find a better way to get Enum#ordinal()?
    private final Map<Symbol, Integer> enumOrdinalCache = new HashMap<>();
    public int getEnumOrdinal(JCExpression expr){
        Symbol sym = null;
        if(expr instanceof JCIdent) sym = ((JCIdent)expr).sym;
        else if(expr instanceof JCFieldAccess) sym = ((JCFieldAccess)expr).sym;
        if(!(sym instanceof VarSymbol) || (sym.flags() & Flags.ENUM) == 0) return -1;

        Integer cached = enumOrdinalCache.get(sym);
        if(cached != null) return cached;

        int ordinal = 0;
        for(Symbol s : sym.owner.getEnclosedElements()){
            if((s.flags() & Flags.ENUM) == 0) continue;
            enumOrdinalCache.put(s, ordinal);
            ordinal++;
        }
        cached = enumOrdinalCache.get(sym);
        return cached != null ? cached : -1;
    }

    public JCExpression captureSelector(JCExpression sel, ListBuffer<JCStatement> prefix, boolean init){
        if(!isComplex(sel)) return sel;
        JCVariableDecl v = makeVarDef(switchTempName(), sel.type, init ? sel : null);
        prefix.append(v);
        return make.QualIdent(v.sym);
    }

    private void attachPatternMatchingCatch(JCBlock block){
        if(pendingAccessorCalls == null || !MATCH_EXCEPTION_PRESENT) return;
        //TODO: JDK 19 generates proxy methods, but it was also the first preview of record-pattern-matching.
        //      Should we also generate proxy methods or leave as is, without error handling?
        resolveMethodsCache();
        JCVariableDecl ctch = makeVarDef(recordTempName(), syms.throwableType, null, Flags.PARAMETER);
        JCCatch handler = make.Catch(
            ctch,
            make.Block(0, List.of(make.Throw(makeNewClass(
                syms.matchExceptionType,
                List.of(makeMethodCall(make.Ident(ctch.sym), object_toString), make.Ident(ctch.sym)),
                List.of(syms.stringType, syms.throwableType)
            ))))
        );
        attachPatternMatchingCatch(block, handler, pendingAccessorCalls);
        pendingAccessorCalls = null;
    }

    public List<JCStatement> buildCaseBody(JCTree cSwitch, JCCase c, JCExpression sel, boolean expression){
        ListBuffer<JCStatement> out = new ListBuffer<>();
        addBindings(c, sel, out);
        JCTree body = getBody(c);
        if(body instanceof JCBlock){
            for(JCStatement s : ((JCBlock)body).stats) out.append(s);
        }else if(body != null){
            JCExpression expr = getExpression(body);
            if(expr != null){
                if(expression){
                    JCYield y = make.Yield(expr);
                    y.target = cSwitch;
                    out.append(y);
                }else{
                    out.append(make.Exec(expr));
                    JCBreak b = make.Break(null);
                    b.target = cSwitch;
                    out.append(b);
                }
            }else if(body instanceof JCStatement){
                out.append((JCStatement)body);
            }
        }else if(c.stats != null){
            for(JCStatement s : c.stats) out.append(s);
        }
        return out.toList();
    }

    /** Returns the guard expression for a pattern slot (with binding substitution), or null if none. */
    public JCExpression buildGuard(JCTree label, JCExpression sel, JCCase src){
        if(src == null) return null;
        JCExpression guard = getGuard(src);
        if(guard == null) return null;
        Map<Name, JCExpression> bindings = collectBindings(label, sel, src);
        if(bindings.isEmpty()) return guard;
        return new TreeTranslator(){
            @Override
            public void visitIdent(JCIdent id){
                JCExpression r = bindings.get(id.name);
                result = r != null ? r : id;
            }
        }.translate(guard);
    }

    public JCExpression buildLabelCondition(JCTree label, JCExpression sel){
        if(isDefault(label)) return null;

        if(isPattern(label)){
            // sel instanceof Type
            JCVariableDecl pv = getPatternVar(label);
            if(pv != null) return makeTypeTest(sel, pv.vartype);
            JCExpression rt = getRecordType(label);
            if(rt != null) return makeTypeTest(sel, rt);
            JCExpression pt = getPatternType(label);
            if(pt != null) return makeTypeTest(sel, pt);
        }

        JCExpression expr = getLabelExpression(label);
        if(expr == null) return null;
        if(expr instanceof JCLiteral){
            JCLiteral lit = (JCLiteral)expr;
            switch (lit.typetag) {
                case FLOAT:
                    //TODO: use Float#floatToIntBits() result as a selector?
                case DOUBLE: {
                    // Boxed.xxxxToxxxBits((Boxed)sel) == Boxed.xxxxToxxxBits(expr)
                    //TODO: cache sel result
                    resolveMethodsCache();
                    boolean isFloat = lit.typetag == TypeTag.FLOAT;
                    ClassSymbol type = types.boxedClass(isFloat ? syms.floatType : syms.doubleType);
                    MethodSymbol method = isFloat ? float_floatToIntBits : double_doubleToLongBits;
                    return makeBinary(
                        Tag.EQ,
                        makeMethodCall(make.QualIdent(type), method, List.of(makeCast(sel, type.type))),
                        makeMethodCall(make.QualIdent(type), method, List.of(expr))
                    );
                }
                case CLASS: //$FALL-THROUGH$
                    break;
                case INT:
                    //TODO: we lost O(1) if there is only a null case. Let the compiler decide?
                    //TODO2: process the same ways as JDK 17? (sel == null ? (sel != n ? sel : n+1) : n)
                    //       where the null case is a value not used in labels, instead of -1.
                default:
                    // sel == expr
                    return makeBinary(Tag.EQ, sel, expr);
            }

        }else if(isEnumConstant(expr)){
            // sel == Enum.expr
            if(expr instanceof JCIdent){
                JCIdent id = (JCIdent)expr;
                if(id.sym != null && id.sym.owner != null && id.sym.owner.type != null){
                    JCFieldAccess fa = make.Select(make.Type(id.sym.owner.type), id.name);
                    fa.sym = id.sym;
                    fa.type = id.type;
                    expr = fa;
                }
            }
            return makeBinary(Tag.EQ, sel, expr);
        }

        // ((Object)sel).equals(expr)   (Implicit null check)
        resolveMethodsCache();
        return makeMethodCall(sel, object_equals, List.of(expr));
    }

    /** Injects {@code default: throw new IncompatibleClassChangeError(...)} if no default exists. */
    public List<JCCase> injectDefault(JCExpression sel, List<JCCase> cases){
        if(hasDefault(cases)) return cases;
        CaseTree.CaseKind kind = CaseTree.CaseKind.STATEMENT;
        for(JCCase c : cases){
            if(c != null){
                kind = c.getCaseKind();
                break;
            }
        }

        JCStatement throwStmt = makeMatchExceptionThrow(sel, false);
        JCStatement body = kind == CaseTree.CaseKind.RULE ? throwStmt : null;
        JCCase dc = makeCase(kind, List.of(makeDefaultCaseLabel()), List.of(throwStmt), body);
        return dc != null ? cases.append(dc) : cases;
    }

    public List<Name> getRecordComponentNames(JCTree pattern){
        JCExpression deconstructor = getRecordType(pattern);
        if(deconstructor == null) return List.nil();
        Type recordType = deconstructor.type;
        if(recordType == null || !(recordType.tsym instanceof ClassSymbol)) return List.nil();
        List<Name> result = List.nil();
        for(RecordComponent rc : ((ClassSymbol)recordType.tsym).getRecordComponents()){
            result = result.append(rc.name);
        }
        return result;
    }

    public Map<Name, JCExpression> collectBindings(JCTree label, JCExpression sel, JCCase caseTree){
        Map<Name, VarSymbol> preVars = guardPreVars != null ? guardPreVars.get(caseTree) : null;
        Map<Name, JCExpression> map = new HashMap<>();

        JCVariableDecl pv = getPatternVar(label);
        if(pv != null){
            map.put(pv.name, makeCast(sel, symTypeOf(pv)));
            return map;
        }

        JCExpression rt = getRecordType(label);
        List<? extends JCTree> nested = getRecordNested(label);
        if(rt == null || nested == null) return map;

        Type recType = rt.type != null ? rt.type : syms.objectType;
        List<Name> componentNames = getRecordComponentNames(label);

        for(JCTree np : nested){
            Name cn = componentNames.head;
            componentNames = componentNames.tail;
            JCVariableDecl nv = getPatternVar(np);
            if(nv == null) continue;

            cn = cn != null ? cn : nv.name;
            JCMethodInvocation accessorCall = makeMethodCall(makeCast(sel, recType), cn);
            if(pendingAccessorCalls != null) pendingAccessorCalls.add(accessorCall);

            JCExpression val = preVars != null && preVars.containsKey(nv.name)
                ? makeAssignParens(preVars.get(nv.name), accessorCall)
                : accessorCall;
            map.put(nv.name, val);
        }
        return map;
    }

    /** Emits binding variable declarations at the top of a case body. */
    public void addBindings(JCCase caseTree, JCExpression sel, ListBuffer<JCStatement> out){
        Map<Name, VarSymbol> preVars = guardPreVars != null ? guardPreVars.get(caseTree) : null;

        for(JCTree label : getLabels(caseTree)){
            if(!isPattern(label)) continue;

            JCVariableDecl pv = getPatternVar(label);
            if(pv != null){
                Type castTy = symTypeOf(pv);
                out.append(make.VarDef(pv.sym, makeCast(sel, castTy)));
                continue;
            }

            JCExpression rt = getRecordType(label);
            List<? extends JCTree> nested = getRecordNested(label);
            if(rt == null || nested == null) continue;

            // RecordType $record$N = (RecordType) sel;
            JCVariableDecl v = makeVarDef(recordTempName(), rt.type, makeCast(sel, rt.type));
            out.append(v);

            if(preVars == null || preVars.isEmpty()){
                ListBuffer<JCVariableDecl> bindings = new ListBuffer<>();
                extractRecordBindings(nested, make.Ident(v.sym), getRecordComponentNames(label), bindings);
                for(JCVariableDecl decl : bindings){
                    if(pendingAccessorCalls != null) {
                        collectMethodInvocations(decl.init, pendingAccessorCalls);
                    }
                    out.append(decl);
                }
                return;
            }

            List<Name> componentNames = getRecordComponentNames(label);
            for(JCTree np : nested){
                Name name = componentNames.head;
                componentNames = componentNames.tail;
                if(!isBindingPattern(np)) continue;
                JCVariableDecl npv = ((JCBindingPattern)np).var;
                if(npv == null) continue;

                VarSymbol preVar = preVars.get(npv.name);
                JCExpression init;
                if(preVar != null){
                    init = make.Ident(preVar); // alias the pre-var assigned in the guard
                }else{
                    name = name != null ? name : npv.name;
                    JCMethodInvocation call = makeMethodCall(make.Ident(v.sym), name);
                    if(pendingAccessorCalls != null) pendingAccessorCalls.add(call);
                    init = call;
                }
                out.append(make.VarDef(npv.sym, init));
            }
        }
    }

    /**
     * Recursively extract bindings from nested record pattern components.
     * <p>
     * Generates variable declarations like:
     * {@code final Point $tmp = parent.b(); final int bx = $tmp.x(); final int by = $tmp.y();}
     */
    public void extractRecordBindings(List<? extends JCTree> nested, JCExpression baseAccessor,
                                      List<Name> componentNames, ListBuffer<JCVariableDecl> out){
        for(JCTree pattern : nested){
            Name name = componentNames.head;
            componentNames = componentNames.tail;

            if(isBindingPattern(pattern)){
                JCVariableDecl var = ((JCBindingPattern)pattern).var;
                if(var == null) continue;
                name = name != null ? name : var.name;
                out.append(make.VarDef(var.sym, makeMethodCall(baseAccessor, name)));
                continue;
            }

            if(!isRecordPattern(pattern)) continue;
            JCExpression nestedRecordType = getRecordType(pattern);
            List<? extends JCTree> deepNested = getRecordNested(pattern);
            if(nestedRecordType == null || deepNested == null || name == null) continue;

            JCVariableDecl tmpDecl = makeVarDef(
                recordTempName(),
                nestedRecordType.type,
                makeMethodCall(baseAccessor, name)
            );
            out.append(tmpDecl);
            extractRecordBindings(
                deepNested,
                make.Ident(tmpDecl.sym),
                getRecordComponentNames(pattern),
                out
            );
        }
    }

    /**
     * Pre-declares variables for record components referenced in a guard. <br>
     * These are assigned inline in the ternary-chain via {@link #collectBindings},
     * and aliased in the case body via {@link #addBindings}.
     */
    public void buildGuardPreDecls(List<JCCase> cases, ListBuffer<JCStatement> out){
        guardPreVars = null;

        for(JCCase c : cases){
            JCExpression guard = getGuard(c);
            if(guard == null) continue;

            for(JCTree label : getLabels(c)){
                if(getRecordType(label) == null) continue;
                List<? extends JCTree> nested = getRecordNested(label);
                if(nested == null) continue;

                // Collect names referenced in the guard
                Set<Name> guardNames = new HashSet<>();
                new TreeScanner<Void, Void>(){
                    @Override
                    public Void visitIdentifier(IdentifierTree node, Void v){
                        if(node instanceof JCIdent) guardNames.add(((JCIdent) node).name);
                        return null;
                    }
                }.scan(guard, null);

                Map<Name, VarSymbol> varMap = new HashMap<>();
                if(guardPreVars == null) guardPreVars = new HashMap<>();
                guardPreVars.put(c, varMap);

                for(JCTree np : nested){
                    JCVariableDecl pv = getPatternVar(np);
                    if(pv == null || pv.name == null || pv.vartype == null) continue;
                    if(!guardNames.contains(pv.name)) continue;

                    JCVariableDecl v = makeVarDef(
                        recordTempName(),
                        symTypeOf(pv),
                        makeDefaultValue(pv.vartype),
                        0
                    );
                    varMap.put(pv.name, v.sym);
                    out.append(v);
                }
            }
        }
    }

    // end region
    // region making

    private JCMethodInvocation makeMethodCall(JCExpression receiver, Name methodName){
        return makeMethodCall(receiver, findMethod(receiver.type, methodName, List.nil()), List.nil());
    }

    private JCMethodInvocation makeMethodCall(JCExpression receiver, MethodSymbol meth){
        return makeMethodCall(receiver, meth, List.nil());
    }

    private JCMethodInvocation makeMethodCall(JCExpression receiver, MethodSymbol meth, List<JCExpression> args){
        JCFieldAccess fa = make.Select(copier.copy(receiver), meth.name);
        fa.sym = meth;
        fa.type = meth.erasure(types);
        JCMethodInvocation call = make.Apply(List.nil(), fa, args);
        call.type = types.erasure(meth.getReturnType());
        return call;
    }

    private JCNewClass makeNewClass(Type ctype, List<JCExpression> args, List<Type> argsType) {
        return makeNewClass(findMethod(ctype, names.init, argsType), args);
    }

    private JCNewClass makeNewClass(MethodSymbol ctor, List<JCExpression> args) {
        JCNewClass tree = make.NewClass(null, null, make.QualIdent(ctor.owner), args, null);
        tree.constructor = ctor;
        tree.constructorType = ctor.erasure(types);
        tree.type = ctor.owner.type;
        return tree;
    }

    private JCInstanceOf makeTypeTest(JCExpression lhs, JCExpression type){
        JCInstanceOf tree = make.TypeTest(copier.copy(lhs), type);
        tree.type = syms.booleanType;
        return tree;
    }

    /** Only with int types. */
    private JCConditional makeConditional(JCExpression cond, JCExpression thenpart, JCExpression elsepart){
        JCConditional c = make.Conditional(cond, thenpart, elsepart);
        c.type = syms.intType;
        return c;
    }

    private JCBinary makeBinary(JCTree.Tag optag, JCExpression lhs, JCExpression rhs){
        JCBinary tree = make.Binary(optag, copier.copy(lhs), rhs); //only copy left side
        tree.operator = HAS_OPERATORS ? resolveBinary((Operators)ops, tree, optag, lhs.type, rhs.type) : null;
        if(tree.operator != null) tree.type = types.erasure(tree.operator.type.getReturnType());
        return tree;
    }

    private JCVariableDecl makeVarDef(Name name, Type type, JCExpression init){
        return makeVarDef(name, type, init, Flags.FINAL);
    }

    private JCVariableDecl makeVarDef(Name name, Type type, JCExpression init, long addFlags){
        return make.VarDef(new VarSymbol(Flags.SYNTHETIC | addFlags, name, type, currentMethodSym), init);
    }

    private JCExpression makeCast(JCExpression expr, Type type){
        if(expr.type != null && types.isSubtype(expr.type, type)) return expr;
        return make.at(expr.pos()).TypeCast(make.Type(type), copier.copy(expr)).setType(type);
    }

    private JCParens makeAssignParens(VarSymbol sym, JCExpression expr){
        JCExpression assign = make.Assign(make.Ident(sym), expr).setType(sym.type);
        JCExpression parens = make.Parens(assign).setType(assign.type);
        return (JCParens)parens;
    }

    private JCExpression makeDefaultValue(JCExpression type){
        if(!(type instanceof JCPrimitiveTypeTree)) return makeNull();
        switch(((JCPrimitiveTypeTree)type).getPrimitiveTypeKind()){
            case BOOLEAN: return make.Literal(false);
            case LONG: return make.Literal(0L);
            case FLOAT: return make.Literal(0.0f);
            case DOUBLE: return make.Literal(0.0d);
            default: return make.Literal(0);
        }
    }

    private JCLiteral makeNull(){
        return make.Literal(TypeTag.BOT, null).setType(syms.botType);
    }

    private JCStatement makeMatchExceptionThrow(JCExpression sel, boolean useType){
        resolveMethodsCache();
        return make.Throw(useMatchException
            ? makeNewClass(me_ctor, List.of(makeNull(), makeNull()))
            : makeNewClass(
                  icce_ctor,
                  List.of(makeBinary(Tag.PLUS,
                      make.Literal("MatchException: Unhandled case: "),
                      useType ? makeMethodCall(makeMethodCall(sel, object_getClass), class_getName) : sel
                  ))
              )
        );
    }

    private JCCase makeStatementCase(JCTree label, List<JCStatement> body){
        // Use an empty label list for JDK < 17
        List<JCTree> labels = label != null ? List.of(label) : List.nil();
        return makeCase(CaseTree.CaseKind.STATEMENT, labels, body, null);
    }

    // end region
    // region other

    //TODO: need to find a way to get an Env, to use Resolve instead
    private MethodSymbol findMethod(Type type, Name name, List<Type> paramTypes){
        if(type == null || type.tsym == null) return null;
        int pSize = paramTypes.size();
        outer:
        for(Symbol s : type.tsym.members().getSymbolsByName(name)){
            if(!(s instanceof MethodSymbol)) continue;
            MethodSymbol ms = (MethodSymbol)s;
            if(ms.params().size() != pSize) continue;
            List<Type> n = paramTypes;
            for(VarSymbol p : ms.params()){
                if(!types.isSameType(p.type, n.head)) continue outer;
                n = n.tail;
            }
            return ms;
        }
        System.err.println("[jabel] Failed to resolve " + type + "." + name + "(" + paramTypes + ")");
        return null;
    }

    private void resolveMethodsCache(){
        if(cacheResolved) return;
        cacheResolved = true;

        object_equals = findMethod(syms.objectType, names.equals, List.of(syms.objectType));
        object_toString = findMethod(syms.objectType, names.toString, List.nil());
        object_getClass = findMethod(syms.objectType, names.getClass, List.nil());
        class_getName = findMethod(syms.classType, names.fromString("getName"), List.nil());
        enum_ordinal = findMethod(syms.enumSym.type, names.ordinal, List.nil());
        float_floatToIntBits = findMethod(
            types.boxedClass(syms.floatType).type,
            names.fromString("floatToIntBits"),
            List.of(syms.floatType)
        );
        double_doubleToLongBits = findMethod(
            types.boxedClass(syms.doubleType).type,
            names.fromString("doubleToLongBits"),
            List.of(syms.doubleType)
        );
        icce_ctor = findMethod(syms.incompatibleClassChangeErrorType, names.init, List.of(syms.stringType));
        if(!MATCH_EXCEPTION_PRESENT) return;
        me_ctor = findMethod(syms.matchExceptionType, names.init, List.of(syms.stringType, syms.throwableType));
        // Use MatchException if available in classpath
        useMatchException = ((ClassSymbol)syms.matchExceptionType.tsym).classfile != null;
    }

    private Type symTypeOf(JCVariableDecl pv){
        if(pv.sym != null && pv.sym.type != null) return pv.sym.type;
        if(pv.vartype != null && pv.vartype.type != null) return pv.vartype.type;
        return syms.objectType;
    }

    private JCExpression assignSwitchSelector(JCExpression cond, VarSymbol selSym, JCExpression rawSel){
        return new TreeTranslator(){
            boolean first = true;
            @Override
            public void visitIdent(JCIdent id){
                result = first && id.sym == selSym ? makeAssignParens(selSym, rawSel) : id;
                first = false;
            }
        }.translate(cond);
    }

    /** Recursively collects {@link JCMethodInvocation} nodes from an expression init. */
    private static void collectMethodInvocations(JCTree tree, Set<JCMethodInvocation> out){
        if(tree instanceof JCMethodInvocation){
            out.add((JCMethodInvocation)tree);
        }else if(tree instanceof JCTypeCast){
            collectMethodInvocations(((JCTypeCast)tree).expr, out);
        }
    }

    private Name switchTempName(){
        return names.fromString("$switch$" + tempVarCounter++);
    }

    private Name recordTempName(){
        return names.fromString("$record$" + tempVarCounter++);
    }

    // end region

    /** {@link TreeCopier} that preserves types and symbols. This does not includes declarations.  */
    public static class SymTreeCopier<T> extends TreeCopier<T>{
        public SymTreeCopier(TreeMaker M){
            super(M);
        }

        @Override
        public <Z extends JCTree> Z copy(Z tree, T p){
            Z fresh = super.copy(tree, p);
            if(fresh != null && fresh != tree && tree instanceof JCExpression && fresh instanceof JCExpression){
                ((JCExpression)fresh).type = ((JCExpression)tree).type;
            }
            return fresh;
        }

        @Override
        public JCTree visitBinary(BinaryTree node, T p){
            JCTree fresh = super.visitBinary(node, p);
            ((JCBinary)fresh).operator = ((JCBinary)node).operator;
            return fresh;
        }

        @Override
        public JCTree visitUnary(UnaryTree node, T p){
            JCTree fresh = super.visitUnary(node, p);
            ((JCUnary)fresh).operator = ((JCUnary)node).operator;
            return fresh;
        }

        @Override
        public JCTree visitIdentifier(IdentifierTree node, T p){
            JCTree fresh = super.visitIdentifier(node, p);
            ((JCIdent)fresh).sym  = ((JCIdent)node).sym;
            return fresh;
        }

        @Override
        public JCTree visitNewClass(NewClassTree node, T p){
            JCTree fresh = super.visitNewClass(node, p);
            ((JCNewClass)fresh).constructor = ((JCNewClass)node).constructor;
            ((JCNewClass)fresh).constructorType = ((JCNewClass)node).constructorType;
            return fresh;
        }

        @Override
        public JCTree visitMemberSelect(MemberSelectTree node, T p){
            JCTree fresh = super.visitMemberSelect(node, p);
            ((JCFieldAccess)fresh).sym  = ((JCFieldAccess)node).sym;
            return fresh;
        }

        @Override
        public JCTree visitMemberReference(MemberReferenceTree node, T p){
            JCTree fresh = super.visitMemberReference(node, p);
            ((JCMemberReference)fresh).sym = ((JCMemberReference)node).sym;
            return fresh;
        }
    }
}
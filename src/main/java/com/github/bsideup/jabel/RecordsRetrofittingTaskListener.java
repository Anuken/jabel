package com.github.bsideup.jabel;

import java.util.Iterator;
import java.util.stream.*;

import javax.lang.model.element.Modifier;

import com.sun.source.tree.*;
import com.sun.source.util.*;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.*;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;


/**
 * Will generate {@code hashCode()}, {@code equals()} and {@code toString()} methods,
 * and remove {@link Flags#RECORD}.
 */
public class RecordsRetrofittingTaskListener implements TaskListener{
    final TreeMaker make;
    final Symtab syms;
    final Types types;
    final Names names;

    public RecordsRetrofittingTaskListener(Context context){
        make = TreeMaker.instance(context);
        syms = Symtab.instance(context);
        types = Types.instance(context);
        names = Names.instance(context);
    }

    @Override
    public void started(TaskEvent e){
        if(e.getKind() != TaskEvent.Kind.ENTER) return;
        new RecordsScanner().scan(e.getCompilationUnit(), false);
    }

    /** Remove {@link Flags#RECORD} to avoid invalid ASM reading. */
    @Override
    public void finished(TaskEvent e){
        if(e.getKind() != TaskEvent.Kind.ANALYZE) return;
        new RecordsScanner().scan(e.getCompilationUnit(), true);
    }


    public class RecordsScanner extends TreeScanner<Void, Boolean>{
        @Override
        public Void visitClass(ClassTree node, Boolean endPhase){
            if("RECORD".equals(node.getKind().toString())){
                JCClassDecl classDecl = (JCClassDecl)node;

                if(endPhase != null && endPhase){
                    if(classDecl.sym != null) classDecl.sym.flags_field &= ~Flags.RECORD;

                }else{
                    if(classDecl.extending == null){
                        // Prevent implicit "extends java.lang.Record"
                        classDecl.extending = make.Type(syms.objectType);
                    }
                    generateToStringIfNeeded(classDecl);
                    generateHashcodeIfNeeded(classDecl);
                    generateEqualsIfNeeded(classDecl);
                }
            }
            return super.visitClass(node, endPhase);
        }
    }


    public void generateToStringIfNeeded(JCClassDecl classDecl) {
        if(containsMethod(classDecl, names.toString)) return;
        classDecl.defs = classDecl.defs.append(make.MethodDef(
            new MethodSymbol(
                Flags.PUBLIC | Flags.FINAL,
                names.toString,
                new Type.MethodType(
                    List.nil(),
                    syms.stringType,
                    List.nil(),
                    syms.methodClass
                ),
                syms.objectType.tsym
            ),
            make.Block(0, generateToString(classDecl))
        ));
    }

    public void generateHashcodeIfNeeded(JCClassDecl classDecl) {
        if(containsMethod(classDecl, names.hashCode)) return;
        classDecl.defs = classDecl.defs.append(make.MethodDef(
            new MethodSymbol(
                Flags.PUBLIC | Flags.FINAL,
                names.hashCode,
                new Type.MethodType(
                    List.nil(),
                    syms.intType,
                    List.nil(),
                    syms.methodClass
                ),
                syms.objectType.tsym
            ),
            make.Block(0, generateHashCode(classDecl))
        ));
    }

    public void generateEqualsIfNeeded(JCClassDecl classDecl) {
        if(containsMethod(classDecl, names.equals)) return;
        MethodSymbol methodSymbol = new MethodSymbol(
            Flags.PUBLIC | Flags.FINAL,
            names.equals,
            new Type.MethodType(
                List.of(syms.objectType),
                syms.booleanType,
                List.nil(),
                syms.methodClass
            ),
            syms.objectType.tsym
        );
        JCMethodDecl methodDecl = make.MethodDef(
            methodSymbol,
            make.Block(0, generateEquals(classDecl, methodSymbol.params().head.name))
        );

        // THIS ONE IS IMPORTANT! Otherwise, Flow.AssignAnalyzer#visitVarDef will have track=false
        methodDecl.params.head.pos = classDecl.pos;
        classDecl.defs = classDecl.defs.append(methodDecl);
    }

    public boolean containsMethod(JCClassDecl classDecl, Name name){
        for(Iterator<JCTree> iterator = classDecl.defs.iterator(); iterator.hasNext();){
            JCTree next = iterator.next();
            if (!(next instanceof JCMethodDecl)) continue;
            JCMethodDecl def = (JCMethodDecl)next;
            if (def.getName() != name) continue;
            if(name != names.equals) return true;
            if(def.params.size() != 1) continue;
            // TODO find a better way?
            switch(def.params.head.getType().toString()){
                case "java.lang.Object":
                case "Object":
                    return true;
                default:
            }
        }
        return false;
    }

    public Stream<JCVariableDecl> getRecordComponents(JCClassDecl classDecl){
        return classDecl.getMembers().stream()
                        .filter(JCVariableDecl.class::isInstance)
                        .map(JCVariableDecl.class::cast)
                        .filter(it -> !it.getModifiers().getFlags().contains(Modifier.STATIC));
    }

    public List<JCStatement> generateToString(JCClassDecl classDecl){
        JCExpression stringBuilder = make.NewClass(
            null,
            null,
            make.QualIdent(syms.stringBuilderType.tsym),
            List.of(make.Literal(classDecl.name + "[")),
            null
        );

        for(Iterator<JCVariableDecl> iterator = getRecordComponents(classDecl).iterator(); iterator.hasNext();){
            JCVariableDecl fieldDecl = iterator.next();
            Name fieldName = fieldDecl.name;

            stringBuilder = stringAppend(stringBuilder, make.Literal(fieldName + "="));
            stringBuilder = stringAppend(stringBuilder, make.Select(make.This(Type.noType), fieldName));
            if(iterator.hasNext()){
                stringBuilder = stringAppend(stringBuilder, make.Literal(", "));
            }
        }
        stringBuilder = stringAppend(stringBuilder, make.Literal("]"));

        return List.of(make.Return(make.App(make.Select(stringBuilder, names.toString).setType(syms.stringType))));
    }

    private JCMethodInvocation stringAppend(JCExpression builder, JCExpression arg) {
        return make.App(make.Select(builder, names.append).setType(syms.stringBuilderType), List.of(arg));
    }

    public List<JCStatement> generateEquals(JCClassDecl classDecl, Name otherName){
        ListBuffer<JCStatement> statements = new ListBuffer<>();

        // if (o == this) return true;
        statements.add(make.If(
            make.Binary(
                Tag.EQ,
                make.This(Type.noType),
                make.Ident(otherName)
            ),
            make.Return(make.Literal(true)),
            null
        ));

        // if (o == null) return false;
        statements.add(make.If(
            make.Binary(
                Tag.EQ,
                make.Ident(otherName),
                make.Literal(TypeTag.BOT, null)
            ),
            make.Return(make.Literal(false)),
            null
        ));

        // if (o.getClass() != getClass()) return false;
        statements.add(make.If(
            make.Binary(
                Tag.EQ,
                make.App(make.Select(make.Ident(otherName), names.getClass).setType(syms.classType)),
                make.App(make.Select(make.This(Type.noType), names.getClass).setType(syms.classType))
            ),
            make.Block(0, List.nil()),
            make.Return(make.Literal(false))
        ));

        // Create casted variable: ClassName other = (ClassName)o;
        Name thatName = names.fromString("other");
        statements.add(make.VarDef(
            make.Modifiers(0),
            thatName,
            make.Ident(classDecl.name),
            make.TypeCast(make.Ident(classDecl.name), make.Ident(otherName))
        ));

        // fields - use the casted variable
        for(Iterator<JCVariableDecl> iterator = getRecordComponents(classDecl).iterator(); iterator.hasNext();){
            JCVariableDecl fieldDecl = iterator.next();
            JCExpression myFieldAccess = make.Select(make.This(Type.noType), fieldDecl.name);
            JCExpression otherFieldAccess = make.Select(make.Ident(thatName), fieldDecl.name);

            final JCExpression condition;
            if(fieldDecl.getType() instanceof JCPrimitiveTypeTree){
                condition = make.Binary(Tag.EQ, otherFieldAccess, myFieldAccess);
            }else{
                condition = make.App(
                    // call Objects.equals
                    make.Select(
                        make.QualIdent(syms.objectsType.tsym),
                        names.equals
                    ).setType(syms.objectsType),
                    List.of(otherFieldAccess, myFieldAccess)
                );
            }
            statements.add(make.If(
                condition,
                make.Block(0, List.nil()),
                make.Return(make.Literal(false))
            ));
        }

        // return true;
        statements.add(make.Return(make.Literal(true)));

        return statements.toList();
    }


    public List<JCStatement> generateHashCode(JCClassDecl classDecl) {
        ListBuffer<JCExpression> expressions = new ListBuffer<>();

        for(Iterator<JCVariableDecl> iterator = getRecordComponents(classDecl).iterator(); iterator.hasNext();){
            JCVariableDecl fieldDecl = iterator.next();

            JCTree fType = fieldDecl.getType();
            JCExpression myFieldAccess = make.Select(make.This(Type.noType), fieldDecl.name);

            if(fType instanceof JCPrimitiveTypeTree){
                //TODO simplify that?
                switch(((JCPrimitiveTypeTree)fType).getPrimitiveTypeKind()){
                    case BOOLEAN:
                        /* this.fieldName ? 1 : 0 */
                        expressions.append(make.Conditional(
                            myFieldAccess,
                            make.Literal(TypeTag.INT, 1),
                            make.Literal(TypeTag.INT, 0)
                        ));
                        break;

                    case LONG:
                        expressions.append(make.TypeCast(
                            make.TypeIdent(syms.intType.getTag()),
                            make.Parens(make.Binary(
                                Tag.BITXOR,
                                myFieldAccess,
                                make.Parens(make.Binary(Tag.USR, myFieldAccess, make.Literal(32)))
                            ))
                        ));
                        break;

                    case FLOAT:
                        /* this.fieldName != 0f ? Float.floatToIntBits(this.fieldName) : 0 */
                        expressions.append(make.Conditional(
                            make.Binary(Tag.NE, myFieldAccess, make.Literal(0f)),
                            make.App(
                                make.Select(
                                    make.QualIdent(types.boxedClass(syms.floatType)),
                                    names.fromString("floatToIntBits")
                                ).setType(syms.intType),
                                List.of(myFieldAccess)
                            ),
                            make.Literal(TypeTag.INT, 0)
                        ));
                        break;

                    case DOUBLE:
                        /* Double.hashCode(this.fieldName) */
                        expressions.append(make.App(
                            make.Select(
                                make.QualIdent(types.boxedClass(syms.doubleType)),
                                names.hashCode
                            ).setType(syms.intType),
                            List.of(myFieldAccess)
                        ));
                        break;

                    case BYTE:
                    case SHORT:
                    case INT:
                    case CHAR:
                    default:
                        /* just the field */
                        expressions.append(myFieldAccess);
                        break;
                }

            }else if(fType instanceof JCArrayTypeTree){
                expressions.append(make.App(
                    make.Select(
                        make.QualIdent(syms.arraysType.tsym),
                        names.hashCode
                    ).setType(syms.intType),
                    List.of(myFieldAccess)
                ));

            }else{
                /* (this.fieldName != null ? this.fieldName.hashCode() : 0) */
                expressions.append(make.Conditional(
                    make.Binary(Tag.NE, myFieldAccess, make.Literal(TypeTag.BOT, null)),
                    make.App(make.Select(myFieldAccess, names.hashCode).setType(syms.intType)),
                    make.Literal(0)
                ));
            }
        }

        ListBuffer<JCStatement> statements = new ListBuffer<>();
        Name resultName = names.fromString("result");
        statements.append(make.VarDef(
            make.Modifiers(0),
            resultName,
            make.TypeIdent(syms.intType.getTag()),
            make.Literal(0)
        ));

        for(JCExpression expression : expressions){
            // result = 31 * result + ${expr}
            statements.append(make.Exec(make.Assign(
                make.Ident(resultName),
                make.Binary(
                    Tag.PLUS,
                    make.Binary(Tag.MUL, make.Literal(TypeTag.INT, 31), make.Ident(resultName)),
                    expression
                )
            )));
        }

        statements.append(make.Return(make.Ident(resultName)));
        return statements.toList();
    }
}

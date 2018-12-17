class Example{
    interface InnerInf1{
    }
    interface InnerInf2{
        // Interfaces are always static, also classes in interfaces are static
    }

    class InnerParent{
    }
    /*
    This code compiles with javac, leading to duplicate annotations on the implemented interface.
    Probably bug (1) in javac, should not compile.
    Possibly this issue: https://bugs.openjdk.java.net/browse/JDK-8077585
    interface A{ // Interfaces are always static
        class B{ // Classes within interfaces are always static
            interface C{
                class D{
                    interface E{}
                }
            }
        }
    }
    static class X implements @JavaAnnot(91) A. @JavaAnnot(92) B. @JavaAnnot(93) C . @JavaAnnot(94) D. @JavaAnnot(95) E{}
    public static void main(String[]args){
       X x = new X();
       java.lang.reflect.AnnotatedType[] annt = x.getClass().getAnnotatedInterfaces();
       for(java.lang.reflect.AnnotatedType a: annt){
           System.out.println(a.getAnnotation(JavaAnnot.class));
       }
    }
    */

    // parent class
    class InnerChild extends @JavaAnnot(1) InnerParent{ }
    // parent interface
    class InnerChild2 extends @JavaAnnot(11) InnerParent implements Example.@JavaAnnot(12) InnerInf1, @JavaAnnot(13) InnerInf2 { }

    // Method parameter, method result
    @JavaAnnot(2) int m(@JavaAnnot(3) int x, @JavaAnnot(4) int y){
        return 0;
    }

    // Field
    @JavaAnnot(5) int f = 0;

    // Method receiver
    int n(@JavaAnnot(6) Example this){
        return 0;
    }

    // Throws
    int o() throws @JavaAnnot(7) Exception{
        throw new Exception();
    }

    // Method type parameter
    <@JavaAnnot(8) T> void p(){ }
    // Method type parameter bound
    <@JavaAnnot(9) T extends @JavaAnnot(10) Example & @JavaAnnot(42) InnerInf1, @JavaAnnot(53) U extends @JavaAnnot(54) String> void q(){
    }

    // Class type parameter
    class InnerGeneric<@JavaAnnot(14) T, @JavaAnnot(24) U>{
        class InnerInnerGeneric<T, U>{
        }
    }
    // Class type parameter bound
    class InnerGeneric2 <@JavaAnnot(15) T extends @JavaAnnot(16) Example & @JavaAnnot(41) InnerInf1, @JavaAnnot(55) U extends @JavaAnnot(56) String>{
        class InnerInnerGeneric2{}
        class InnerInner2Generic2 extends @JavaAnnot(80) InnerInnerGeneric2{}
    }

    static class NestedGeneric<@JavaAnnot(59) T>{
        static class NestedNestedGeneric<@JavaAnnot(60) U>{
        }
    }

    // Type paths
    class GenericApplication extends
            @JavaAnnot(62) Example. @JavaAnnot(17) InnerGeneric<
                    @JavaAnnot(18) InnerGeneric<@JavaAnnot(19) String, @JavaAnnot(25) Object>. @JavaAnnot(69) InnerInnerGeneric<@JavaAnnot(57) String, @JavaAnnot(58) Object>,
                    @JavaAnnot(26) Object
                    >{
    }

    /*
    Possible bug (2) in javac: it should not be possible to select a nested class of a parameterized class.
    However, when there is an annotation on the nested class selection, javac allows it
    class NestedGenericApplication extends
            @JavaAnnot(61) NestedGeneric<
                    NestedGeneric<@JavaAnnot(62) String>. @JavaAnnot(63) NestedNestedGeneric<@JavaAnnot(64) String> >{
    }*/

    class NestedGenericApplication extends
            @JavaAnnot(61) NestedGeneric<
                    NestedGeneric. @JavaAnnot(63) NestedNestedGeneric<@JavaAnnot(64) String> >{ }

    class ArrayApplication extends @JavaAnnot(20) InnerGeneric<@JavaAnnot(21)String @JavaAnnot(22)[] @JavaAnnot(23)[], @JavaAnnot(43) int @JavaAnnot(44)[]>{
    }
    class Inner{
        class Inner2{
            class Inner3{ }
            class InnerParents extends @JavaAnnot(66) Example . @JavaAnnot(27) Inner . @JavaAnnot(28) Inner2 . @JavaAnnot(29) Inner3{ }
        }
    }
    static class Nested{
        static class Nested2{
            static class Nested3{ }
            // scoping constructs cannot be annotated
            class NestedParents extends Nested . Nested2 . @JavaAnnot(49) Nested3{ }
        }
    }
    static class N1{
        static class N2{
            static class N3{
                class I1{
                    class I2{
                        class I3{}
                        // If written @JavaAnnot(39) Example.N1.N2.N3.@JavaAnnot(47) I1 . @JavaAnnot(48) I2. @JavaAnnot(38) I3, the result is the same
                        // which seems to be the same bug (1) as described above
                        class NI extends  Example.N1.N2. @JavaAnnot(39) N3.@JavaAnnot(47) I1 . @JavaAnnot(48) I2. @JavaAnnot(38) I3{ }
                        class NI2 extends @JavaAnnot(52) I2{ }
                    }
                }
            }
        }
    }
    void mGenericApplication(@JavaAnnot(70) InnerGeneric<@JavaAnnot(30) InnerGeneric<@JavaAnnot(31) String, @JavaAnnot(32) Object>, @JavaAnnot(33) Object> a){}
    void mArrayApplication(@JavaAnnot(35)String @JavaAnnot(36)[] @JavaAnnot(37)[] a, @JavaAnnot(45) int @JavaAnnot(46)[] b){}
    void mNestedApplication(Nested . Nested2 . @JavaAnnot(40) Nested3 a){}
    void mInnerApplication(@JavaAnnot(71) Example . @JavaAnnot(50) Inner . @JavaAnnot(51) Inner2 . @JavaAnnot(42) Inner3 a){}
    /*
    Same bug (2) as with NestedGenericApplication
    void mNestedGenericApplication(@JavaAnnot(65) NestedGeneric<
            NestedGeneric<@JavaAnnot(66) String>. @JavaAnnot(67) NestedNestedGeneric<@JavaAnnot(68) String> > a){}*/
    void mNestedGenericApplication(@JavaAnnot(65) NestedGeneric<
            NestedGeneric. @JavaAnnot(67) NestedNestedGeneric<@JavaAnnot(68) String> > a){}

    // Wildcards
    void mUpperBoundWildcard(NestedGeneric<@JavaAnnot(72) ? extends @JavaAnnot(77) NestedGeneric<@JavaAnnot(76) ? extends @JavaAnnot(73) String> > a){}
    void mLowerBoundWildcard(NestedGeneric<@JavaAnnot(74) ? super @JavaAnnot(79) NestedGeneric<@JavaAnnot(78) ? super @JavaAnnot(75) String> >a){}
}

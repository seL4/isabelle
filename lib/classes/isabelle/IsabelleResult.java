/*
 * $Id$
 * 
 * IsabelleResult -- result objects from IsabelleProcess
 */

public class IsabelleResult {
    public enum Kind {
        STDOUT, STDERR, EXIT,                               // Posix results
        WRITELN, PRIORITY, TRACING, WARNING, ERROR, DEBUG,  // Isabelle results
        FAILURE                                             // process wrapper problem
    };
    public Kind kind;
    public String result;
    
    public IsabelleResult(Kind kind, String result) {
        this.kind = kind;
        this.result = result;
    }
    
    public String toString() {
        return this.kind.toString() + " [[" + this.result + "]]";
    }
}

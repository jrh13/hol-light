import java.io.*;
import java.util.*;

public class NamedTheorem {

    public static int proofcounter;
    public static Hashtable table = new Hashtable(1000, 0.3f);

    /**
     * @param w
     * @return skips the leading part of w that consists only of spaces and returns the rest
     */
    public static String skipSpace(String w) {
        for (int i=0; i<w.length(); i++) {
            if (w.charAt(i) != ' ') {
                return w.substring(i);
            }
        }
        return "";
    }

    /**
     * @param w
     * @return the leading part of w that consists only of alphanumeric chars or the underscore char
     */
    public static String readWord (String w) {
        for (int i=0; i<w.length(); i++) {
            char c = w.charAt(i);
            if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                    || c == '_' || (i > 0 && c >= '0' && c <= '9')))
                return w.substring(0,i);
        }
        return w;
    }

    /**
     * Checks if a line is to be replaced and returns the necessary information to do it.
     * @param line the line
     * @return null, if no replacement, otherwise a pair (n,r) so that n is the name of the theorem and r
     * is the trailing rest of the line
     */
    public static String[] filter (String line) {
        line = skipSpace(line);
        String l = readWord(line);
        if (l.equals("let")) {
            line = line.substring(l.length());
            line = skipSpace(line);
            String w = readWord(line);
            line = skipSpace(line.substring(w.length()));
            if (line.length() > 1 && line.charAt(0) == '=') {
                line = skipSpace(line.substring(1));
                String p = readWord(line);
                line = line.substring(p.length());
                if (p.equals("prove") && (line.equals("") || line.startsWith(" ") || line.startsWith("("))) {
                    return new String[] {w, line};
                }
            }
        }
        return null;
    }

    public static boolean ignore (String x) {
        return x.startsWith("pth") || x.startsWith("bth") ||
                x.startsWith("nth") || x.startsWith("tth") ||
                x.startsWith("lem") || x.startsWith("thm") || x.startsWith("rthm");
    }

    public static void convert(String filename) throws IOException {
        File f = new File(filename);
        File fnew = new File(filename+".old");
        f.renameTo(fnew);
        LineNumberReader reader = new LineNumberReader(new FileReader(fnew));
        PrintWriter writer = new PrintWriter(new FileWriter(f));
        do {
            String line = reader.readLine();
            if (line == null) break;
            String proofinfo[] = filter(line);
            if (proofinfo == null)
                writer.println(line);
            else {
                String proofname = proofinfo[0];
                proofcounter++;
                if (ignore(proofname)) {
                    System.out.println("warning: ignoring '"+proofname+"' in "+filename);
                    writer.println(line);
                } else if (table.get(proofname) != null) {
                    System.out.println("warning: duplicate '"+proofname+"' in "+filename);
                    writer.println(line);
                } else {
                    writer.println("let "+proofname+" = nprove \""+
                            proofname+"\""+proofinfo[1]);
                    table.put(proofname, proofname);
                }
            }
        } while (true);
        reader.close();
        writer.close();
    }

    public static void main(String args[]) throws IOException {
        proofcounter = 0;
        for (int i=0; i<args.length; i++) {
            System.out.println("convert "+args[i] +" ...");
            convert(args[i]);
        }
        System.out.println("done. "+proofcounter+" named proofs found.");
    }

}

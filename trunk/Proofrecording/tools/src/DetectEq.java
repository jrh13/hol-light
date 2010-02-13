import java.io.*;
import java.util.regex.Pattern;
import java.util.regex.Matcher;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;

public class DetectEq {

    static class Annotation {
        String type;
        String op;
        String code;
        int from, to, line, true_line;
        void print () {
            System.out.println("from: "+from+", to: "+to+
                    ", type: "+type+", op: "+op);
            System.out.println("line: "+true_line+", code: "+code);
            System.out.println("");
        }
        public boolean equals(Annotation a) {
            return a.from == from && a.to == to;
        }
    }

    static void skip (StringBuffer s) {
        for (int i=0; i<s.length(); i++)
          if (Character.isDigit(s.charAt(i))) {
              s.delete(0, i);
              break;
          }
    }

    static int readnum (StringBuffer s) {
        for (int i=0; ; i++)
          if (i == s.length() || !Character.isDigit(s.charAt(i))) {
              int num = Integer.parseInt(s.substring(0, i));
              s.delete(0, i);
              return num;
          }
    }

    static Pattern thm_patterns[] =
            new Pattern[] {
                Pattern.compile("(.*thm.*) (\\*|->) (.*thm.*) -> bool"),
                Pattern.compile("(.*injust.*) (\\*|->) (.*injust.*) -> bool"),
                Pattern.compile("(.*lineq.*) (\\*|->) (.*lineq.*) -> bool"),
                Pattern.compile("(.*goal.*) (\\*|->) (.*goal.*) -> bool")
            };

    static Pattern typattern = Pattern.compile(".*(thm|injust|lineq|goal).*");

    static String thm_funcs[] = {
        "union", "intersect", "subtract", "subset", "set_eq", "unions", "assoc", "rev_assoc", "assoc2",
        "uniq", "setify", "set_insert", "set_merge", "munion", "msubtract", "assocd", "rev_assocd",
        "apply", "|->", "dom", "graph"
    };

    static void readtype(String s, Annotation a) {
        String t1, t2;
        s = s.trim();
        for (int i=0; i<thm_patterns.length; i++) {
            Matcher matcher = thm_patterns[i].matcher(s);
            while (matcher.find()) {
                t1 = matcher.group(1).trim();
                t2 = matcher.group(3).trim();
                if (t1.equals(t2)) {
                    a.type = t1;
                    a.op = matcher.group(2);
                    break;
                }
            }
        }
    }

    static Annotation parseAnnotation(LineNumberReader r, MLFile mlfile) throws Exception {
        Annotation annot = new Annotation();
        String line1 = r.readLine();
        if (line1 == null) return null;
        if (r.readLine() == null) return null;
        String line2 = "";
        do {
            String l = r.readLine();
            if (l == null) return null;
            l = l.trim();
            if (")".equals(l)) break;
            line2 = line2+" "+l;
        } while (true);
        line2 = line2.trim();
        readtype(line2, annot);
        StringBuffer buf = new StringBuffer(line1);
        skip(buf); annot.line = readnum(buf);
        skip(buf); readnum(buf);
        skip(buf); annot.from = readnum(buf);
        skip(buf); readnum(buf);
        skip(buf); readnum(buf);
        skip(buf); annot.to = readnum(buf);
        annot.code = mlfile.get(annot.from, annot.to);
        annot.true_line = mlfile.line(annot.from);
        Matcher matcher = typattern.matcher(line2);
        if (annot.type == null && matcher.find()) {
            String s = mlfile.get(annot.from,  annot.to);
            for (int i=0; i<thm_funcs.length; i++) {
                if (s.equals(thm_funcs[i])) {
                    annot.type = line2;
                    annot.op = thm_funcs[i];
                }
            }
        }
        return annot;
    }

    static Annotation[] readAnnotations(LineNumberReader r, MLFile mlfile) throws Exception {
        ArrayList array = new ArrayList(100);
        Annotation a;
        do {
            a = parseAnnotation(r, mlfile);
            if (a != null) {
//                if (!(array.size() > 0 && ((Annotation)array.get(array.size()-1)).equals(a))) {
                    array.add(a);
                    if (a.type != null) a.print();
  //              }
            }
        } while (a != null);
        Annotation as[] = new Annotation[array.size()];
        for (int i=0; i<as.length; i++) as[i] = (Annotation) array.get(i);
        return as;
    }

    static class Interval implements Comparable {
        int line;
        int from, to;
        Interval(int l, int f, int t) { line = l; from = f; to = t;}
        public int compareTo(Object o) {
            Interval y = (Interval) o;
            if ((y.from <= from && y.to >= to) ||
                (from <= y.from && to >= y.from))
                return 0;
            if (from < y.from) return -1;
            else if (from > y.from) return 1;
            else if (to < y.to) return -1;
            else return 1;
        }
    }

    static class MLFile {
        File f;
        byte[] data;
        TreeMap lines;

       MLFile (File f) throws Exception {
            this.f = f;
            data = new byte[(int)f.length()];
            FileInputStream in = new FileInputStream(f);
            in.read(data);
            in.close();
            prepareLineLookup();
        }
        void prepareLineLookup() {
            lines = new TreeMap();
            int line = 1;
            int from = 0;
            for (int i=0; i<data.length; i++) {
                if ((char) data[i] == '\n') {
                    Interval v = new Interval (line, from, i);
                    lines.put(v, v);
                    line++;
                    from = i+1;
                }
            }
            Interval v = new Interval(line, from, data.length);
            lines.put(v,v);
        }
        String get(int from, int to) {
            StringBuffer buf = new StringBuffer(to-from);
            for (int i=from; i<to; i++) {
                int c = data[i];
                if (c < 0) c += 256;
                buf.append((char) c);
            }
            return buf.toString();
        }
        int line(int pos) {
            return ((Interval)lines.get(new Interval(0,pos, pos))).line;
        }
    }

    public static void main (String args[]) throws Exception {
        File annot = new File(args[0], "core.annot");
        File ml = new File(args[0], "core.ml");
        MLFile mlfile = new MLFile(ml);
        LineNumberReader in_annot = new LineNumberReader(new FileReader(annot));
        Annotation as[] = readAnnotations(in_annot,mlfile);
        in_annot.close();
        System.out.println("count: "+as.length);
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        mainloop: do {
            String s = reader.readLine();
            int line = Integer.parseInt(s);
            for (int i=0; i<as.length; i++) {
                if (as[i].line == line) {
                    System.out.println(line+" -> "+as[i].true_line);
                    //as[i].print();
                    continue mainloop;
                }
            }
            System.out.println("line not found");
        } while (true);
    }


}

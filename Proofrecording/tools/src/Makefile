install: nametheorems.jar detecteq.jar; mv nametheorems.jar detecteq.jar ..

nametheorems.jar: NamedTheorem.java; \
  javac NamedTheorem.java; \
  jar cvfe nametheorems.jar NamedTheorem NamedTheorem.class; \
  rm -f NamedTheorem.class

detecteq.jar: DetectEq.java; \
  javac DetectEq.java; \
  jar cvfe detecteq.jar DetectEq DetectEq.class; \
  rm -f DetectEq*.class

clean:; rm -f *.class *.jar

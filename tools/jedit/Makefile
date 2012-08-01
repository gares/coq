HIDE=@
empty:=
space:=$(empty) $(empty)
CPX=classes:/usr/share/jedit/jedit.jar:/usr/share/java/scala-swing.jar:$(subst $(space),:,$(wildcard extras/*.jar))
CP=classes
SCALAC=fsc -d classes/ -classpath
JAR=Coq.jar
SRC_PIDE=$(wildcard pide/*.scala)
SRC_JEDIT=$(wildcard pide/jedit/*.scala)
SRC_COQ=$(wildcard coq/*.scala)
META=$(wildcard coq/*.props coq/*.xml pide/jedit/*.xml pide/jedit/*.props)
EXTRAS=$(wildcard extras/*.jar)
SCALA_HOME=/usr/share/java
SCALA_RUNTIME=$(addprefix $(SCALA_HOME)/scala-,library.jar compiler.jar swing.jar)

$(JAR): $(SRC_COQ) $(SRC_JEDIT) $(SCR_PIDE) $(META)
	$(HIDE) mkdir -p classes
	@echo "SCALAC pide/"
	$(HIDE) $(SCALAC) $(CP) $(SRC_PIDE)
	@echo "SCALAC pide/jedit/"
	$(HIDE) $(SCALAC) $(CPX) $(SRC_JEDIT)
	@echo "SCALAC coq/"
	$(HIDE) $(SCALAC) $(CPX) $(SRC_COQ)
	@echo "JAR $(JAR)"
	@cp $(META) classes/
	$(HIDE) (cd classes; jar -cf ../$(JAR) *)

install: $(JAR)
	@echo "INSTALL $(JAR)"
	$(HIDE) mkdir -p ~/.jedit/jars
	$(HIDE) cp $(SCALA_RUNTIME) $(JAR) $(EXTRAS) ~/.jedit/jars

clean:
	rm -rf classes $(JAR)
	fsc -reset

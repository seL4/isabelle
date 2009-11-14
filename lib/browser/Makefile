
DST=classes

all: GraphBrowser.jar

GraphBrowser.jar: GraphBrowser/*.java awtUtilities/*.java
	mkdir -p $(DST)
	javac -source 1.4 -d $(DST) GraphBrowser/GraphBrowser.java GraphBrowser/Console.java
	jar cf GraphBrowser.jar -C $(DST) . 
	rm -rf $(DST)

clean:
	rm -f GraphBrowser/*.class
	rm -f awtUtilities/*.class
	rm -rf $(DST)
	rm -f GraphBrowser.jar

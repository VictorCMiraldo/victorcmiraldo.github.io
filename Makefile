DEPS=$(wildcard *.md)
POSTS=$(wildcard ./posts/*.md)

all: $(DEPS:.md=.html)  $(POSTS:.md=.html)

%.html: %.md my-html5.template
	pandoc --template my-html5.template -f markdown+smart -t html5 -s $< -o $@

posts/%.html: posts/%.md my-html5.template
	pandoc --template my-html5.template -f markdown+smart -t html5 -s $< -o $@

clean: 
	rm *.html
	cd posts && rm *.html

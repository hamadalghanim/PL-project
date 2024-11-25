.PHONY: all clean doc

# Output files
VO := demo.vo
GLOB := demo.glob
HTML := doc/demo.html

all: $(VO) doc

# Compile Coq file
%.vo %.glob: %.v
	coqc $<

# Generate documentation
doc: $(VO)
	coqdoc --toc --toc-depth 2 --html --interpolate \
    --no-lib-name \
	--utf8 --no-index -d docs --with-header header.html --with-footer footer.html  demo.v
	rm -f $(VO) $(GLOB) *.vos *.vok *.v.d *.glob .demo.aux


clean:
	rm -f $(VO) $(GLOB)
	rm -rf docs/*

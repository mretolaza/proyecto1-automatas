TESTS = $(shell find test -type f -name "*js")
BROWERIFY_BIN = './node_modules/browserify/bin/cmd.js'

distribution:
	@mkdir -p lib
	@mkdir -p public
	@$(BROWERIFY_BIN)\
		-r './classes/index.js':regparser > lib/regparser-browser.js 
	@cp classes/index.js lib
	@cp lib/regparser-browser.js public

clean:
	rm -f lib/*.js

.PHONY: test distribution


arm8Lib.sig arm8Lib.sml arm8Script.sml: v8-base.spec v8-fp.spec v8-iset.spec v8-encode.spec CountTrailing.terminates
	l3 --eval 'HolExport.spec ("v8-base.spec, v8-fp.spec, v8-iset.spec, v8-encode.spec","arm8 underflowbefore nosigdocs");' </dev/null
	cp arm8Lib.sig arm8Lib.sml arm8Script.sml ..


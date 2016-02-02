AlphaProlog 0.4 README

This is AlphaProlog, a prototype nominal logic programming language.

To get started:

1.  Edit the Makefile INSTALL variable to indicate where you want to 
    install AlphaProlog

2.  Do

$ make configure
$ make all
$ make install

    Also, it might be convenient to put <install-dir>/bin in your PATH.

3.  To test that AlphaProlog is working correctly, go to the install 
    directory and do 

$ bin/aprolog examples/lam.apl

    This will start aprolog on an example file that defines a syntax 
    representing the simply-typed lambda calculus together with some 
    sample queries.    


4.  To uninstall, do 

$ make uninstall

    Warning: This will delete everything in the install directory, including 
    anything you put there.

A draft user's guide can be found in <install dir>/doc.

If you have any questions, please contact the author at

jcheney@cs.cornell.edu

Have fun!

Contributors:
Alberto Momigliano
Matteo Pessina
James Cheney

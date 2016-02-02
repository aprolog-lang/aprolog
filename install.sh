#/bin/sh
APROLOG_BASE=$1
APROLOG_INSTALL=$2

if [ -d "$APROLOG_INSTALL" ]; then 
 echo "Directory $APROLOG_INSTALL already exists"
else 
 mkdir $APROLOG_INSTALL
 mkdir $APROLOG_INSTALL/bin
 mkdir $APROLOG_INSTALL/lib
 mkdir $APROLOG_INSTALL/examples
 mkdir $APROLOG_INSTALL/examples/simple
 mkdir $APROLOG_INSTALL/doc
 if [ -d "$APROLOG_INSTALL" ]; then 
   echo "Creating install directory $APROLOG_INSTALL"
  else 
   echo "Could not create install directory $APROLOG_INSTALL";
   exit 1
 fi
fi


echo "Copying $APROLOG_BASE/bin to $APROLOG_INSTALL/bin"
cp -rf $APROLOG_BASE/bin/aprolog $APROLOG_INSTALL/bin

echo "Copying $APROLOG_BASE/lib to $APROLOG_INSTALL/lib"
cp  $APROLOG_BASE/lib/*.apl $APROLOG_INSTALL/lib

echo "Copying $APROLOG_BASE/examples to $APROLOG_INSTALL/examples"
cp  $APROLOG_BASE/examples/simple/*.apl $APROLOG_INSTALL/examples/simple

echo "Copying $APROLOG_BASE/doc to $APROLOG_INSTALL/doc"
if [ -f "$APROLOG_BASE/doc/guide.ps" ]; then 
  cp  $APROLOG_BASE/doc/guide.ps $APROLOG_INSTALL/doc
 else 
  true
fi
if [ -f "$APROLOG_BASE/doc/guide.ps" ]; then 
  cp  $APROLOG_BASE/doc/guide.pdf $APROLOG_INSTALL/doc
 else 
  true
fi

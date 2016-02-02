#/bin/sh
APROLOG_INSTALL=$1

if [ -d "$APROLOG_INSTALL" ]; then 
 echo "Deleting install directory $APROLOG_INSTALL";
 rm -rf $APROLOG_INSTALL
else 
 echo "Can't find install directory $APROLOG_INSTALL"
fi

#!/bin/sh

APROLOG_INSTALL=$1

echo "Configuring for install directory \"$APROLOG_INSTALL\"..."

echo "let lib_dirs = ref [\"$APROLOG_INSTALL/lib\"];;" > src/config.ml


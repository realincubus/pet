#!/bin/bash

FILE=$1
OPTS=$2

EXEEXT=
srcdir=.

echo $FILE;
./pet$EXEEXT $OPTS $FILE  > test.scop 
if [ $? -ne 0 ]; then
  echo "error in extraction of $FILE" 
  exit -1
fi
./pet_scop_cmp$EXEEXT test.scop ${FILE%.c}.scop
if [ $? -ne 0 ]; then
  echo "error in comparison of $FILE" 
  exit -1
fi
exit 0


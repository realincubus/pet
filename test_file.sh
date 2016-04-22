#!/bin/bash -xe

PET_CMD=$1
PET_SCOP_CMP_CMD=$2
FILE=$3
OPTS=$4

EXEEXT=
srcdir=.

echo $FILE;
$PET_CMD$EXEEXT $OPTS $FILE  > test.scop 
if [ $? -ne 0 ]; then
  echo "error in extraction of $FILE" 
  exit -1
fi
$PET_SCOP_CMP_CMD$EXEEXT test.scop ${FILE%.c}.scop
if [ $? -ne 0 ]; then
  echo "error in comparison of $FILE" 
  exit -1
fi
exit 0


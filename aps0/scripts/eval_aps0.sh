#! /bin/bash

for i in `ls ../Samples/aps0/*.aps`
do
  echo $i " -> "
	../eval $i
	echo -e
done

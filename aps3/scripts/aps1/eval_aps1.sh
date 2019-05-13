#! /bin/bash

for i in `ls ../../Samples/aps1/*.aps`
do
  echo $i " -> "
	../../eval $i
	echo -e
done

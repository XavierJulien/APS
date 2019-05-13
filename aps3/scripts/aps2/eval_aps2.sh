#! /bin/bash

for i in `ls ../../Samples/aps2/*.aps`
do
  echo $i " -> "
	../../eval $i
	echo -e
done

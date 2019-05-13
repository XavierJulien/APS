#! /bin/bash

for i in `ls ../../Samples/aps3/*.aps`
do
  echo $i " -> "
	../../eval $i
	echo -e
done

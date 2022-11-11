#!/bin/bash

function Test () {
    echo "Running on testcase $1"
    ./build/ast-interpreter "`cat ./test/test$1.c`" 2> output
    g++ -o ./test/test$1 ./test/util.c ./test/test$1.c
    ./test/test$1 > answer
    rm ./test/test$1
    diff output answer
    if [ $? -eq 0 ] 
    then
        echo "Accepted"
    else
        echo "Wrong Answer"
    fi
    rm output answer
}

for num in {0..24}
do
    Test `printf "%02d" $num`
done

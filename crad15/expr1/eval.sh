#!/bin/bash
#arg1=start,arg2=end,format:%s.%N
function getTiming(){
    start=$1
    end=$2
    start_s=$(echo $start | cut -d '.' -f 1)
    start_ns=$(echo $start | cut -d '.' -f 2)
    end_s=$(echo $end | cut -d '.' -f 1)
    end_ns=$(echo $end | cut -d '.' -f 2)
    time=$(( ( 10#$end_s - 10#$start_s ) * 1000 + ( 10#$end_ns / 1000000 - 10#$start_ns / 1000000 ) ))
    echo "$time ms"
}

echo "expr1a_SIRNNI:"
start=$(date +%s.%N)
coqc expr1a_SIRNNI.v > expr1a_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr1a_SMENI:"
start=$(date +%s.%N)
coqc expr1a_SMENI.v > expr1a_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr1b_SIRNNI:"
start=$(date +%s.%N)
coqc expr1b_SIRNNI.v > expr1b_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr1b_SMENI:"
start=$(date +%s.%N)
coqc expr1b_SMENI.v > expr1b_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr1c_SIRNNI:"
start=$(date +%s.%N)
coqc expr1c_SIRNNI.v > expr1c_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr1c_SMENI:"
start=$(date +%s.%N)
coqc expr1c_SMENI.v > expr1c_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

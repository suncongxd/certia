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

echo "expr2a_SIRNNI:"
start=$(date +%s.%N)
coqc expr2a_SIRNNI.v > expr2a_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2a_SMENI:"
start=$(date +%s.%N)
coqc expr2a_SMENI.v > expr2a_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2b_SIRNNI:"
start=$(date +%s.%N)
coqc expr2b_SIRNNI.v > expr2b_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2b_SMENI:"
start=$(date +%s.%N)
coqc expr2b_SMENI.v > expr2b_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2c_SIRNNI:"
start=$(date +%s.%N)
coqc expr2c_SIRNNI.v > expr2c_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2c_SMENI:"
start=$(date +%s.%N)
coqc expr2c_SMENI.v > expr2c_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2d_SIRNNI:"
start=$(date +%s.%N)
coqc expr2d_SIRNNI.v > expr2d_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2d_SMENI:"
start=$(date +%s.%N)
coqc expr2d_SMENI.v > expr2d_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2e_SIRNNI:"
start=$(date +%s.%N)
coqc expr2e_SIRNNI.v > expr2e_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2e_SMENI:"
start=$(date +%s.%N)
coqc expr2e_SMENI.v > expr2e_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2f_SIRNNI:"
start=$(date +%s.%N)
coqc expr2f_SIRNNI.v > expr2f_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2f_SMENI:"
start=$(date +%s.%N)
coqc expr2f_SMENI.v > expr2f_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2g_SIRNNI:"
start=$(date +%s.%N)
coqc expr2g_SIRNNI.v > expr2g_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2g_SMENI:"
start=$(date +%s.%N)
coqc expr2g_SMENI.v > expr2g_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2h_SIRNNI:"
start=$(date +%s.%N)
coqc expr2h_SIRNNI.v > expr2h_SIRNNI.txt
end=$(date +%s.%N)
getTiming $start $end

echo "expr2h_SMENI:"
start=$(date +%s.%N)
coqc expr2h_SMENI.v > expr2h_SMENI.txt
end=$(date +%s.%N)
getTiming $start $end

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

echo "emrghalt:"
start=$(date +%s.%N)
coqc emrghalt.v > emrghalt.txt
end=$(date +%s.%N)
getTiming $start $end

echo "starter:"
start=$(date +%s.%N)
coqc starter.v > starter.txt
end=$(date +%s.%N)
getTiming $start $end

echo "station:"
start=$(date +%s.%N)
coqc station.v > station.txt
end=$(date +%s.%N)
getTiming $start $end

echo "vehicle:"
start=$(date +%s.%N)
coqc vehicle.v > vehicle.txt
end=$(date +%s.%N)
getTiming $start $end

echo "vehicle_starter:"
start=$(date +%s.%N)
coqc vehicle_starter.v > vehicle_starter.txt
end=$(date +%s.%N)
getTiming $start $end

echo "vehicle_station:"
start=$(date +%s.%N)
coqc vehicle_station.v > vehicle_station.txt
end=$(date +%s.%N)
getTiming $start $end

echo "vehicle_starter_emrghalt:"
start=$(date +%s.%N)
coqc vehicle_starter_emrghalt.v > vehicle_starter_emrghalt.txt
end=$(date +%s.%N)
getTiming $start $end

echo "client:"
start=$(date +%s.%N)
coqc client.v > client.txt
end=$(date +%s.%N)
getTiming $start $end

echo "server:"
start=$(date +%s.%N)
coqc server.v > server.txt
end=$(date +%s.%N)
getTiming $start $end

echo "adapter:"
start=$(date +%s.%N)
coqc adapter.v > adapter.txt
end=$(date +%s.%N)
getTiming $start $end

echo "client_adapter:"
start=$(date +%s.%N)
coqc client_adapter.v > client_adapter.txt
end=$(date +%s.%N)
getTiming $start $end

echo "adapter_server:"
start=$(date +%s.%N)
coqc adapter_server.v > adapter_server.txt
end=$(date +%s.%N)
getTiming $start $end

echo "SV:"
start=$(date +%s.%N)
coqc Lee_ENTCS_SV.v > Lee_ENTCS_SV.txt
end=$(date +%s.%N)
getTiming $start $end

echo "TPU:"
start=$(date +%s.%N)
coqc Lee_ENTCS_TPU.v > Lee_ENTCS_TPU.txt
end=$(date +%s.%N)
getTiming $start $end

echo "TS:"
start=$(date +%s.%N)
coqc Lee_ENTCS_TS.v > Lee_ENTCS_TS.txt
end=$(date +%s.%N)
getTiming $start $end

echo "TS_SV:"
start=$(date +%s.%N)
coqc Lee_ENTCS_TS_SV.v > Lee_ENTCS_TS_SV.txt
end=$(date +%s.%N)
getTiming $start $end

echo "TS_TPU:"
start=$(date +%s.%N)
coqc Lee_ENTCS_TS_TPU.v > Lee_ENTCS_TS_TPU.txt
end=$(date +%s.%N)
getTiming $start $end

echo "SV_TPU:"
start=$(date +%s.%N)
coqc Lee_ENTCS_SV_TPU.v > Lee_ENTCS_SV_TPU.txt
end=$(date +%s.%N)
getTiming $start $end

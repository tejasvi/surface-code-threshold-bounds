#!/usr/bin/env bash
# box_tguard.sh UNIT NAME [STOP_S] [TMAX_S]: on a build machine, next to the running systemd unit UNIT (box_ktrun.sh
# runs each module as /usr/bin/time -> timeout -k 15 TMAX_S -> lean): keep a module from being killed by its timeout.
# Every 20 s, for each lean process of the unit that has run STOP_S seconds (default 6900), SIGSTOP its parent timeout
# process (comm checked; the lean process keeps running). When that lean process has exited (a zombie, since its
# parent is stopped), read its exit status from /proc/PID/stat:
#  - status 0 and the timeout process younger than TMAX_S - 5 (default 7200): SIGCONT it; the normal path follows
#    (timeout reaps lean, box_ktrun.sh moves the olean and logs OK);
#  - status 0 and the deadline passed (a resumed timeout would report 124): if the module's output has no error line and
#    its .olean.tmp exists, move it to .olean and log "<module> OK <seconds> <peak KB>" in ktrun_NAME.log, then SIGKILL
#    the timeout process (box_ktrun.sh then also logs FAIL(137) for the module; its rm of the .olean.tmp finds nothing);
#  - any other status: SIGCONT it (the normal failure path).
# Signals go only to processes of the unit's own cgroup with the expected comm and uid. Log: kt/tguard_NAME.log.
# Exits when the unit is no longer active and no module is held.
set -u
UNIT=$1; NAME=$2; STOP_S=${3:-6900}; TMAX_S=${4:-7200}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}
O=$K/lib/QEC/KChecks/$NAME
U=$UNIT
LOG=$K/tguard_$NAME.log
ME=$(id -u)
declare -A HELD MOD T0 HWM
echo "$(date -u +%T) start unit=$U stop=$STOP_S tmax=$TMAX_S" >> "$LOG"
while :; do
  act=$(systemctl is-active "$U" 2>/dev/null)
  cg=$(systemctl show -p ControlGroup --value "$U" 2>/dev/null)
  if [ -n "$cg" ] && [ -f "/sys/fs/cgroup$cg/cgroup.procs" ]; then
    for p in $(cat "/sys/fs/cgroup$cg/cgroup.procs"); do
      [ "$(cat /proc/$p/comm 2>/dev/null)" = lean ] || continue
      [ "$(stat -c %u /proc/$p 2>/dev/null)" = "$ME" ] || continue
      h=$(awk '/^VmHWM/ {print $2}' /proc/$p/status 2>/dev/null)
      [ -n "$h" ] && [ "$h" -gt "${HWM[$p]:-0}" ] && HWM[$p]=$h
      [ -n "${HELD[$p]:-}" ] && continue
      e=$(ps -o etimes= -p "$p" 2>/dev/null | tr -d ' ')
      [ -n "$e" ] && [ "$e" -ge "$STOP_S" ] || continue
      pp=$(awk '{print $4}' /proc/$p/stat 2>/dev/null)
      [ "$(cat /proc/$pp/comm 2>/dev/null)" = timeout ] || continue
      [ "$(stat -c %u /proc/$pp 2>/dev/null)" = "$ME" ] || continue
      # already held by another instance of this guard: leave it to that one
      [ "$(awk '{print $3}' /proc/$pp/stat 2>/dev/null)" = T ] && continue
      out=$(readlink /proc/$p/fd/1 2>/dev/null)
      m=$(basename "$out" .out); m=${m#${NAME}_}
      [ -n "$m" ] || continue
      kill -STOP "$pp" && HELD[$p]=$pp && MOD[$p]=$m && T0[$p]=$(( $(date +%s) - e )) &&
        echo "$(date -u +%T) held $m: lean $p at $e s, timeout $pp stopped" >> "$LOG"
    done
  fi
  for p in "${!HELD[@]}"; do
    pp=${HELD[$p]}; m=${MOD[$p]}
    st=$(awk '{print $3, $52}' /proc/$p/stat 2>/dev/null)
    state=${st%% *}; code=${st##* }
    [ "$state" = Z ] || [ -z "$st" ] || continue
    te=$(ps -o etimes= -p "$pp" 2>/dev/null | tr -d ' ')
    if [ "$state" = Z ] && [ "$code" = 0 ] && [ -n "$te" ] && [ "$te" -ge $((TMAX_S - 5)) ]; then
      if ! command grep -q 'error' "$K/ktimes/${NAME}_$m.out" 2>/dev/null && [ -f "$O/$m.olean.tmp" ]; then
        mv "$O/$m.olean.tmp" "$O/$m.olean"
        echo "$m OK $(( $(date +%s) - T0[$p] )) ${HWM[$p]:-0}" >> "$K/ktrun_$NAME.log"
        echo "$(date -u +%T) rescued $m: lean exit 0 after the deadline, olean moved, OK logged" >> "$LOG"
      else
        echo "$(date -u +%T) $m: lean exit 0 after the deadline but error text or no olean; left to fail" >> "$LOG"
      fi
      kill -KILL "$pp"
    else
      kill -CONT "$pp"
      echo "$(date -u +%T) released $m: lean state ${state:-gone} status ${code:-?}, timeout at ${te:-?} s" >> "$LOG"
    fi
    unset "HELD[$p]" "MOD[$p]" "T0[$p]" "HWM[$p]"
  done
  if [ "$act" != active ] && [ "$act" != activating ] && [ ${#HELD[@]} -eq 0 ]; then
    echo "$(date -u +%T) unit $act, nothing held: exit" >> "$LOG"; exit 0
  fi
  sleep 20
done

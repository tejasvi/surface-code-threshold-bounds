import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2860 = true := by
  decide +kernel

theorem tot2860 : totK PD2M8K2 D2M8K2.t2860 = [89187925547, 137721136019, 138388878143, 349442412957, 162127089738, 8063697217, 0, 0] := by
  decide +kernel

theorem rows2861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2861 = true := by
  decide +kernel

theorem tot2861 : totK PD2M8K2 D2M8K2.t2861 = [156964385308, 464451568384, 247910049387, 13586547250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2862 = true := by
  decide +kernel

theorem tot2862 : totK PD2M8K2 D2M8K2.t2862 = [151318649428, 446230737898, 268515875468, 18794542373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2863 = true := by
  decide +kernel

theorem tot2863 : totK PD2M8K2 D2M8K2.t2863 = [0, 267492079640, 495803125973, 111390494616, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

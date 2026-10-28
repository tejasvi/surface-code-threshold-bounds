import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3500 = true := by
  decide +kernel

theorem tot3500 : totK PD2M8K2 D2M8K2.t3500 = [0, 177009439207, 463771942910, 240804446589, 16131077680, 0, 0, 0] := by
  decide +kernel

theorem rows3501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3501 = true := by
  decide +kernel

theorem tot3501 : totK PD2M8K2 D2M8K2.t3501 = [0, 206322581966, 471568613348, 204864468556, 12064174497, 0, 0, 0] := by
  decide +kernel

theorem rows3502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3502 = true := by
  decide +kernel

theorem tot3502 : totK PD2M8K2 D2M8K2.t3502 = [0, 36480893038, 352430243101, 401991421604, 60657913037, 1021600638, 0, 0] := by
  decide +kernel

theorem rows3503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3503 = true := by
  decide +kernel

theorem tot3503 : totK PD2M8K2 D2M8K2.t3503 = [0, 66658272810, 310398941705, 379597840065, 91918588940, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

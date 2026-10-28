import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3912 = true := by
  decide +kernel

theorem tot3912 : totK PD2M8K2 D2M8K2.t3912 = [0, 0, 179125371784, 477088115020, 213802960251, 9581088325, 0, 0] := by
  decide +kernel

theorem rows3913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3913 = true := by
  decide +kernel

theorem tot3913 : totK PD2M8K2 D2M8K2.t3913 = [0, 175146938256, 427513693742, 211369210622, 63309618854, 11100731106, 0, 0] := by
  decide +kernel

theorem rows3914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3914 = true := by
  decide +kernel

theorem tot3914 : totK PD2M8K2 D2M8K2.t3914 = [0, 203533866854, 471797110786, 202531183901, 10404947084, 0, 0, 0] := by
  decide +kernel

theorem rows3915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3915 = true := by
  decide +kernel

theorem tot3915 : totK PD2M8K2 D2M8K2.t3915 = [0, 0, 275166096464, 496609954874, 105074730446, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

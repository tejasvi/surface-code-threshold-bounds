import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3612 = true := by
  decide +kernel

theorem tot3612 : totK PD2M8K2 D2M8K2.t3612 = [0, 69373448757, 311106680623, 396736875788, 102135074948, 3575904516, 0, 0] := by
  decide +kernel

theorem rows3613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3613 = true := by
  decide +kernel

theorem tot3613 : totK PD2M8K2 D2M8K2.t3613 = [0, 176197973888, 451232313114, 267741088093, 28010388863, 0, 0, 0] := by
  decide +kernel

theorem rows3614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3614 = true := by
  decide +kernel

theorem tot3614 : totK PD2M8K2 D2M8K2.t3614 = [0, 177697891872, 474726679459, 234016901136, 12103576160, 0, 0, 0] := by
  decide +kernel

theorem rows3615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3615 = true := by
  decide +kernel

theorem tot3615 : totK PD2M8K2 D2M8K2.t3615 = [0, 0, 328788089098, 513463985391, 71717106791, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

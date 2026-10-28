import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3240 = true := by
  decide +kernel

theorem tot3240 : totK PD2M8K2 D2M8K2.t3240 = [159571904973, 458265732252, 284971027345, 31214472938, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3241 = true := by
  decide +kernel

theorem tot3241 : totK PD2M8K2 D2M8K2.t3241 = [0, 184910902317, 447800952842, 252076700346, 25324944147, 0, 0, 0] := by
  decide +kernel

theorem rows3242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3242 = true := by
  decide +kernel

theorem tot3242 : totK PD2M8K2 D2M8K2.t3242 = [0, 194185880058, 512353639340, 202549796807, 5424570950, 0, 0, 0] := by
  decide +kernel

theorem rows3243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3243 = true := by
  decide +kernel

theorem tot3243 : totK PD2M8K2 D2M8K2.t3243 = [153501397625, 396747853714, 268939908686, 89214151005, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

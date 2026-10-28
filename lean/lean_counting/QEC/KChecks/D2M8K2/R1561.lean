import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6244 = true := by
  decide +kernel

theorem tot6244 : totK PD2M8K2 D2M8K2.t6244 = [163721061462, 439472609334, 271078413055, 35028031070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6245 = true := by
  decide +kernel

theorem tot6245 : totK PD2M8K2 D2M8K2.t6245 = [159900448456, 456123795956, 267450569913, 18171770317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6246 = true := by
  decide +kernel

theorem tot6246 : totK PD2M8K2 D2M8K2.t6246 = [0, 233599512511, 497442447917, 141988582759, 2348440009, 0, 0, 0] := by
  decide +kernel

theorem rows6247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6247 = true := by
  decide +kernel

theorem tot6247 : totK PD2M8K2 D2M8K2.t6247 = [105481780695, 320847421951, 317788555582, 120524317425, 10902245252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12220 = true := by
  decide +kernel

theorem tot12220 : totK PD2M8K2 D2M8K2.t12220 = [0, 206931572748, 470570656379, 201085423834, 15514803433, 0, 0, 0] := by
  decide +kernel

theorem rows12221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12221 = true := by
  decide +kernel

theorem tot12221 : totK PD2M8K2 D2M8K2.t12221 = [0, 164933832869, 448219063641, 282129357035, 28496840222, 0, 0, 0] := by
  decide +kernel

theorem rows12222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12222 = true := by
  decide +kernel

theorem tot12222 : totK PD2M8K2 D2M8K2.t12222 = [0, 180653652570, 484581891188, 240501871851, 8977779328, 0, 0, 0] := by
  decide +kernel

theorem rows12223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12223 = true := by
  decide +kernel

theorem tot12223 : totK PD2M8K2 D2M8K2.t12223 = [0, 0, 244931015367, 450550309156, 192622846101, 21385604922, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

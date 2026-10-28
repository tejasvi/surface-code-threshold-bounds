import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15264 = true := by
  decide +kernel

theorem tot15264 : totK PD2M8K2 D2M8K2.t15264 = [0, 0, 153101915474, 459731019850, 287679356455, 23827087626, 0, 0] := by
  decide +kernel

theorem rows15265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15265 = true := by
  decide +kernel

theorem tot15265 : totK PD2M8K2 D2M8K2.t15265 = [0, 0, 37176659836, 312061448585, 463167722872, 100242070578, 1527735764, 0] := by
  decide +kernel

theorem rows15266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15266 = true := by
  decide +kernel

theorem tot15266 : totK PD2M8K2 D2M8K2.t15266 = [0, 0, 190172864723, 462808772508, 245907738218, 18742693462, 0, 0] := by
  decide +kernel

theorem rows15267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15267 = true := by
  decide +kernel

theorem tot15267 : totK PD2M8K2 D2M8K2.t15267 = [0, 0, 190362967684, 470624787107, 220380834949, 12373752831, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10032 = true := by
  decide +kernel

theorem tot10032 : totK PD2M8K2 D2M8K2.t10032 = [0, 192963236994, 463557095455, 242475956370, 23437208677, 0, 0, 0] := by
  decide +kernel

theorem rows10033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10033 = true := by
  decide +kernel

theorem tot10033 : totK PD2M8K2 D2M8K2.t10033 = [0, 177709164412, 460752663207, 240473605205, 15892578943, 0, 0, 0] := by
  decide +kernel

theorem rows10034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10034 = true := by
  decide +kernel

theorem tot10034 : totK PD2M8K2 D2M8K2.t10034 = [0, 0, 315143711437, 500656377961, 81871492811, 0, 0, 0] := by
  decide +kernel

theorem rows10035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10035 = true := by
  decide +kernel

theorem tot10035 : totK PD2M8K2 D2M8K2.t10035 = [0, 66761380721, 308481525663, 402861704549, 107928304905, 3867150671, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

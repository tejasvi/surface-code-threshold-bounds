import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10180 = true := by
  decide +kernel

theorem tot10180 : totK PD2M8K2 D2M8K2.t10180 = [0, 0, 161825441543, 473376733654, 269218443471, 14462799775, 0, 0] := by
  decide +kernel

theorem rows10181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10181 = true := by
  decide +kernel

theorem tot10181 : totK PD2M8K2 D2M8K2.t10181 = [0, 0, 199592291498, 452531700363, 237787979702, 26625690833, 0, 0] := by
  decide +kernel

theorem rows10182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10182 = true := by
  decide +kernel

theorem tot10182 : totK PD2M8K2 D2M8K2.t10182 = [0, 0, 184732175927, 485820556934, 221622921782, 9644176565, 0, 0] := by
  decide +kernel

theorem rows10183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10183 = true := by
  decide +kernel

theorem tot10183 : totK PD2M8K2 D2M8K2.t10183 = [0, 0, 0, 312717895238, 488453818119, 89797726600, 1435164049, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

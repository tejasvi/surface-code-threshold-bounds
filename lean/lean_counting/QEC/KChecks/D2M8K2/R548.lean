import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2192 = true := by
  decide +kernel

theorem tot2192 : totK PD2M8K2 D2M8K2.t2192 = [0, 0, 115769868190, 432688959403, 298909761448, 23801035651, 0, 0] := by
  decide +kernel

theorem rows2193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2193 = true := by
  decide +kernel

theorem tot2193 : totK PD2M8K2 D2M8K2.t2193 = [0, 0, 0, 225439249262, 461202430703, 166185171090, 9579374723, 0] := by
  decide +kernel

theorem rows2194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2194 = true := by
  decide +kernel

theorem tot2194 : totK PD2M8K2 D2M8K2.t2194 = [0, 0, 114131532852, 362181527821, 299977763366, 75889006468, 3436822651, 0] := by
  decide +kernel

theorem rows2195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2195 = true := by
  decide +kernel

theorem tot2195 : totK PD2M8K2 D2M8K2.t2195 = [0, 0, 177118841970, 460098227323, 233502168162, 18252358503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

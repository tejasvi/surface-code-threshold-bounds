import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5324 = true := by
  decide +kernel

theorem tot5324 : totK PD2M8K2 D2M8K2.t5324 = [0, 172178331847, 397775076405, 242906400472, 77070157965, 3884009855, 0, 0] := by
  decide +kernel

theorem rows5325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5325 = true := by
  decide +kernel

theorem tot5325 : totK PD2M8K2 D2M8K2.t5325 = [0, 161311331899, 448108704637, 279753027545, 23027905747, 0, 0, 0] := by
  decide +kernel

theorem rows5326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5326 = true := by
  decide +kernel

theorem tot5326 : totK PD2M8K2 D2M8K2.t5326 = [0, 92934196222, 349263597773, 368954904001, 81330887814, 1268739303, 0, 0] := by
  decide +kernel

theorem rows5327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5327 = true := by
  decide +kernel

theorem tot5327 : totK PD2M8K2 D2M8K2.t5327 = [0, 0, 228991288618, 494631653825, 166097273266, 4761634222, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

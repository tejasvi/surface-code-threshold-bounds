import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t304 = true := by
  decide +kernel

theorem tot304 : totK PD2M8K2 D2M8K2.t304 = [0, 173422102699, 464051316300, 227081288373, 13468041724, 0, 0, 0] := by
  decide +kernel

theorem rows305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t305 = true := by
  decide +kernel

theorem tot305 : totK PD2M8K2 D2M8K2.t305 = [0, 0, 278915643171, 470550939059, 107652864593, 1369150432, 0, 0] := by
  decide +kernel

theorem rows306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t306 = true := by
  decide +kernel

theorem tot306 : totK PD2M8K2 D2M8K2.t306 = [0, 105790625839, 415981042315, 323471711265, 33591495300, 0, 0, 0] := by
  decide +kernel

theorem rows307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t307 = true := by
  decide +kernel

theorem tot307 : totK PD2M8K2 D2M8K2.t307 = [0, 191996238375, 470781037852, 222360932232, 12552144954, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

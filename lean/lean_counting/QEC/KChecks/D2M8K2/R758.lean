import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3032 = true := by
  decide +kernel

theorem tot3032 : totK PD2M8K2 D2M8K2.t3032 = [0, 0, 229972086301, 492845207382, 169551694817, 4899792023, 0, 0] := by
  decide +kernel

theorem rows3033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3033 = true := by
  decide +kernel

theorem tot3033 : totK PD2M8K2 D2M8K2.t3033 = [0, 0, 176392489340, 467144073758, 221928545964, 15968327686, 0, 0] := by
  decide +kernel

theorem rows3034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3034 = true := by
  decide +kernel

theorem tot3034 : totK PD2M8K2 D2M8K2.t3034 = [0, 0, 214817750575, 463933972563, 154263865382, 6279558296, 0, 0] := by
  decide +kernel

theorem rows3035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3035 = true := by
  decide +kernel

theorem tot3035 : totK PD2M8K2 D2M8K2.t3035 = [0, 0, 0, 290783578396, 456094506322, 84761882475, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

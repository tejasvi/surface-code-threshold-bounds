import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6268 = true := by
  decide +kernel

theorem tot6268 : totK PD2M8K2 D2M8K2.t6268 = [56666157517, 347057733062, 442400702839, 60332721555, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6269 = true := by
  decide +kernel

theorem tot6269 : totK PD2M8K2 D2M8K2.t6269 = [167358545249, 436819066721, 279659044895, 30318485251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6270 = true := by
  decide +kernel

theorem tot6270 : totK PD2M8K2 D2M8K2.t6270 = [191110652258, 494483929904, 221340088588, 10786994342, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6271 = true := by
  decide +kernel

theorem tot6271 : totK PD2M8K2 D2M8K2.t6271 = [0, 245868707805, 448786984823, 195952505475, 21380039407, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

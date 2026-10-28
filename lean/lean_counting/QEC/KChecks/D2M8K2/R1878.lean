import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7512 = true := by
  decide +kernel

theorem tot7512 : totK PD2M8K2 D2M8K2.t7512 = [0, 200660442541, 464084748596, 249003209965, 23388038350, 0, 0, 0] := by
  decide +kernel

theorem rows7513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7513 = true := by
  decide +kernel

theorem tot7513 : totK PD2M8K2 D2M8K2.t7513 = [0, 173378866008, 476681134463, 232203085851, 12346377983, 0, 0, 0] := by
  decide +kernel

theorem rows7514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7514 = true := by
  decide +kernel

theorem tot7514 : totK PD2M8K2 D2M8K2.t7514 = [0, 0, 288986894599, 508184997626, 109763229877, 1163840124, 0, 0] := by
  decide +kernel

theorem rows7515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7515 = true := by
  decide +kernel

theorem tot7515 : totK PD2M8K2 D2M8K2.t7515 = [0, 0, 201119931395, 473643897532, 185315268704, 11873025674, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

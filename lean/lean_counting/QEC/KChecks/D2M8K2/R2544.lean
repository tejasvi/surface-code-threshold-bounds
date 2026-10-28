import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10176 = true := by
  decide +kernel

theorem tot10176 : totK PD2M8K2 D2M8K2.t10176 = [0, 0, 166444111199, 487720558033, 234942121785, 9354552220, 0, 0] := by
  decide +kernel

theorem rows10177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10177 = true := by
  decide +kernel

theorem tot10177 : totK PD2M8K2 D2M8K2.t10177 = [0, 0, 88513360709, 346955294009, 377693361655, 71635385358, 1310285577, 0] := by
  decide +kernel

theorem rows10178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10178 = true := by
  decide +kernel

theorem tot10178 : totK PD2M8K2 D2M8K2.t10178 = [0, 0, 93375087334, 386677110131, 391040899601, 49764929847, 0, 0] := by
  decide +kernel

theorem rows10179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10179 = true := by
  decide +kernel

theorem tot10179 : totK PD2M8K2 D2M8K2.t10179 = [0, 0, 172450200848, 447055605108, 266436954971, 17842112816, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

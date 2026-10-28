import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14260 = true := by
  decide +kernel

theorem tot14260 : totK PD2M8K2 D2M8K2.t14260 = [165462805984, 444668078729, 281883989521, 30318485251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14261 = true := by
  decide +kernel

theorem tot14261 : totK PD2M8K2 D2M8K2.t14261 = [193986703136, 492316448541, 218678933005, 10798897126, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14262 = true := by
  decide +kernel

theorem tot14262 : totK PD2M8K2 D2M8K2.t14262 = [0, 249699717024, 446991491519, 194707278464, 21380039407, 0, 0, 0] := by
  decide +kernel

theorem rows14263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14263 = true := by
  decide +kernel

theorem tot14263 : totK PD2M8K2 D2M8K2.t14263 = [0, 159345242229, 484235478046, 241715832609, 9219054063, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

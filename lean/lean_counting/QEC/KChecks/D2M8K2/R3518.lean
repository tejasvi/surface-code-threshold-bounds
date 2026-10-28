import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14072 = true := by
  decide +kernel

theorem tot14072 : totK PD2M8K2 D2M8K2.t14072 = [0, 175491399546, 466872377183, 256723421218, 22983046962, 0, 0, 0] := by
  decide +kernel

theorem rows14073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14073 = true := by
  decide +kernel

theorem tot14073 : totK PD2M8K2 D2M8K2.t14073 = [0, 178164570641, 459769239246, 239554516862, 17000544574, 0, 0, 0] := by
  decide +kernel

theorem rows14074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14074 = true := by
  decide +kernel

theorem tot14074 : totK PD2M8K2 D2M8K2.t14074 = [0, 0, 292996688717, 502121073960, 98226623073, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14075 = true := by
  decide +kernel

theorem tot14075 : totK PD2M8K2 D2M8K2.t14075 = [0, 0, 246646685414, 498221239587, 162499892887, 10915202382, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

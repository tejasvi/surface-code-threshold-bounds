import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1276 = true := by
  decide +kernel

theorem tot1276 : totK PD2M8K2 D2M8K2.t1276 = [0, 104414402675, 349012685037, 328769891126, 79074567337, 3552795014, 0, 0] := by
  decide +kernel

theorem rows1277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1277 = true := by
  decide +kernel

theorem tot1277 : totK PD2M8K2 D2M8K2.t1277 = [0, 177156911450, 448651047499, 252020932847, 25338240278, 0, 0, 0] := by
  decide +kernel

theorem rows1278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1278 = true := by
  decide +kernel

theorem tot1278 : totK PD2M8K2 D2M8K2.t1278 = [54140871534, 205485511962, 397017250277, 231507829772, 17476474534, 0, 0, 0] := by
  decide +kernel

theorem rows1279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1279 = true := by
  decide +kernel

theorem tot1279 : totK PD2M8K2 D2M8K2.t1279 = [191609469018, 486919392186, 207904460273, 9822075347, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

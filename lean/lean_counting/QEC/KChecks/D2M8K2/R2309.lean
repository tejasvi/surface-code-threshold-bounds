import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9236 = true := by
  decide +kernel

theorem tot9236 : totK PD2M8K2 D2M8K2.t9236 = [172994857302, 440558151867, 270588826346, 30127170223, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9237 = true := by
  decide +kernel

theorem tot9237 : totK PD2M8K2 D2M8K2.t9237 = [128539345291, 444114584379, 292600923802, 24745799432, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9238 = true := by
  decide +kernel

theorem tot9238 : totK PD2M8K2 D2M8K2.t9238 = [0, 283448307993, 521013444902, 100800810278, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows9239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9239 = true := by
  decide +kernel

theorem tot9239 : totK PD2M8K2 D2M8K2.t9239 = [0, 206075185509, 493463618833, 184084734368, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

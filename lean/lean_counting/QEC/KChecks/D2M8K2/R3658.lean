import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14632 = true := by
  decide +kernel

theorem tot14632 : totK PD2M8K2 D2M8K2.t14632 = [0, 89916998193, 252430514548, 380445921780, 183198016491, 8170972732, 0, 0] := by
  decide +kernel

theorem rows14633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14633 = true := by
  decide +kernel

theorem tot14633 : totK PD2M8K2 D2M8K2.t14633 = [0, 156132549484, 466041835526, 267814570918, 20768967147, 0, 0, 0] := by
  decide +kernel

theorem rows14634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14634 = true := by
  decide +kernel

theorem tot14634 : totK PD2M8K2 D2M8K2.t14634 = [0, 85385489824, 384632545944, 399498280341, 56047004243, 0, 0, 0] := by
  decide +kernel

theorem rows14635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14635 = true := by
  decide +kernel

theorem tot14635 : totK PD2M8K2 D2M8K2.t14635 = [0, 66143812334, 249357335836, 421030102350, 148255833658, 5370412161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3516 = true := by
  decide +kernel

theorem tot3516 : totK PD2M8K2 D2M8K2.t3516 = [0, 268337953290, 510003577772, 118682591025, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows3517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3517 = true := by
  decide +kernel

theorem tot3517 : totK PD2M8K2 D2M8K2.t3517 = [33838848500, 210319388900, 433973644631, 188354717622, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows3518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3518 = true := by
  decide +kernel

theorem tot3518 : totK PD2M8K2 D2M8K2.t3518 = [170550932207, 450618891224, 253263642584, 23143029844, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3519 = true := by
  decide +kernel

theorem tot3519 : totK PD2M8K2 D2M8K2.t3519 = [194833197383, 464371659943, 229392853892, 17094537169, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6556 = true := by
  decide +kernel

theorem tot6556 : totK PD2M8K2 D2M8K2.t6556 = [0, 215047961523, 482326592551, 185134417328, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows6557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6557 = true := by
  decide +kernel

theorem tot6557 : totK PD2M8K2 D2M8K2.t6557 = [83817468306, 327109640920, 362081924531, 100783014157, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows6558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6558 = true := by
  decide +kernel

theorem tot6558 : totK PD2M8K2 D2M8K2.t6558 = [176648850714, 427000861320, 270817147727, 30115119781, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6559 = true := by
  decide +kernel

theorem tot6559 : totK PD2M8K2 D2M8K2.t6559 = [162851094289, 477017591785, 257552906946, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

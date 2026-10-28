import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11940 = true := by
  decide +kernel

theorem tot11940 : totK PD2M8K2 D2M8K2.t11940 = [0, 179527854374, 452826983742, 252227848927, 25330507241, 0, 0, 0] := by
  decide +kernel

theorem rows11941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11941 = true := by
  decide +kernel

theorem tot11941 : totK PD2M8K2 D2M8K2.t11941 = [0, 190690717269, 499505261774, 200979329005, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows11942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11942 = true := by
  decide +kernel

theorem tot11942 : totK PD2M8K2 D2M8K2.t11942 = [176600050142, 417092742831, 224319775449, 85995144638, 6630726990, 0, 0, 0] := by
  decide +kernel

theorem rows11943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11943 = true := by
  decide +kernel

theorem tot11943 : totK PD2M8K2 D2M8K2.t11943 = [181154523674, 457517499073, 258168761725, 18438013872, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11060 = true := by
  decide +kernel

theorem tot11060 : totK PD2M8K2 D2M8K2.t11060 = [172332080960, 447292089834, 273136300913, 26819474067, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11061 = true := by
  decide +kernel

theorem tot11061 : totK PD2M8K2 D2M8K2.t11061 = [180114736652, 480070333227, 234128925166, 13998332970, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11062 = true := by
  decide +kernel

theorem tot11062 : totK PD2M8K2 D2M8K2.t11062 = [0, 280052789917, 523152547910, 100680969396, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11063 = true := by
  decide +kernel

theorem tot11063 : totK PD2M8K2 D2M8K2.t11063 = [0, 232776102011, 498158762961, 163841925227, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

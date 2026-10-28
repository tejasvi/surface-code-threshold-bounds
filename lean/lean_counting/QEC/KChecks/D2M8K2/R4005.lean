import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16020 = true := by
  decide +kernel

theorem tot16020 : totK PD2M8K2 D2M8K2.t16020 = [0, 0, 0, 185415891346, 463255438892, 233191772981, 17093733621, 0] := by
  decide +kernel

theorem rows16021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16021 = true := by
  decide +kernel

theorem tot16021 : totK PD2M8K2 D2M8K2.t16021 = [0, 0, 0, 198262021242, 477316890572, 207867106788, 12439805748, 0] := by
  decide +kernel

theorem rows16022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16022 = true := by
  decide +kernel

theorem tot16022 : totK PD2M8K2 D2M8K2.t16022 = [0, 0, 0, 51735240357, 352027319966, 396524225541, 70304125875, 1171084559] := by
  decide +kernel

theorem rows16023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16023 = true := by
  decide +kernel

theorem tot16023 : totK PD2M8K2 D2M8K2.t16023 = [0, 0, 0, 42292664238, 301717999222, 416219495419, 109078156189, 4254746638] := by
  decide +kernel

end QECKChecks.D2M8K2

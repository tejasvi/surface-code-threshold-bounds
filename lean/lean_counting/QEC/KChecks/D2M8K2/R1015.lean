import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4060 = true := by
  decide +kernel

theorem tot4060 : totK PD2M8K2 D2M8K2.t4060 = [0, 163123545257, 449972322756, 284366296863, 30488455136, 0, 0, 0] := by
  decide +kernel

theorem rows4061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4061 = true := by
  decide +kernel

theorem tot4061 : totK PD2M8K2 D2M8K2.t4061 = [0, 207145565659, 482187318699, 209242436395, 10946697450, 0, 0, 0] := by
  decide +kernel

theorem rows4062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4062 = true := by
  decide +kernel

theorem tot4062 : totK PD2M8K2 D2M8K2.t4062 = [0, 36516442283, 279308630337, 396344490280, 178394532273, 21395095148, 0, 0] := by
  decide +kernel

theorem rows4063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4063 = true := by
  decide +kernel

theorem tot4063 : totK PD2M8K2 D2M8K2.t4063 = [0, 0, 199264017810, 479870359082, 214152356203, 7992090037, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

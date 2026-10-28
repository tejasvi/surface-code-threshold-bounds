import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7952 = true := by
  decide +kernel

theorem tot7952 : totK PD2M8K2 D2M8K2.t7952 = [0, 0, 153088622316, 468194344113, 241753036820, 13782265251, 0, 0] := by
  decide +kernel

theorem rows7953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7953 = true := by
  decide +kernel

theorem tot7953 : totK PD2M8K2 D2M8K2.t7953 = [0, 0, 0, 322188834084, 476901414038, 72135372581, 1198073392, 0] := by
  decide +kernel

theorem rows7954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7954 = true := by
  decide +kernel

theorem tot7954 : totK PD2M8K2 D2M8K2.t7954 = [0, 0, 160401469127, 455527771298, 259665635058, 14898000672, 0, 0] := by
  decide +kernel

theorem rows7955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7955 = true := by
  decide +kernel

theorem tot7955 : totK PD2M8K2 D2M8K2.t7955 = [0, 0, 176961918625, 443239265429, 222647294940, 17104814242, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

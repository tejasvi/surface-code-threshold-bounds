import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5584 = true := by
  decide +kernel

theorem tot5584 : totK PA10K2 A10K2.t5584 = [0, 277626483571, 1191053268836, 1882977426850, 1203856004760, 201900485104, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5585 = true := by
  decide +kernel

theorem tot5585 : totK PA10K2 A10K2.t5585 = [0, 542618031769, 1889555222440, 1791238636056, 453258528839, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5586 = true := by
  decide +kernel

theorem tot5586 : totK PA10K2 A10K2.t5586 = [0, 0, 926935416341, 2382349778345, 1279041491267, 113928931746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5587 = true := by
  decide +kernel

theorem tot5587 : totK PA10K2 A10K2.t5587 = [0, 0, 476395709034, 1795443069974, 1963325221656, 536958277051, 31987755669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

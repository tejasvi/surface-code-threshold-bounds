import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows80 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t80 = true := by
  decide +kernel

theorem tot80 : totK PA10K2 A10K2.t80 = [257580387599, 1375244919259, 2203869166290, 949580721459, 75589217460, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows81 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t81 = true := by
  decide +kernel

theorem tot81 : totK PA10K2 A10K2.t81 = [0, 493851675349, 1837802638240, 1858144278489, 485037423643, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows82 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t82 = true := by
  decide +kernel

theorem tot82 : totK PA10K2 A10K2.t82 = [466252311137, 1634641921801, 1827829020397, 723706805548, 84054203309, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows83 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t83 = true := by
  decide +kernel

theorem tot83 : totK PA10K2 A10K2.t83 = [293434943870, 1503898776038, 2129493081585, 783932236883, 45918807480, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

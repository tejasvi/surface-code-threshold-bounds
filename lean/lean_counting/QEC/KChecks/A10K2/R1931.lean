import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7724 = true := by
  decide +kernel

theorem tot7724 : totK PA10K2 A10K2.t7724 = [0, 0, 593542274757, 1973246404406, 2030812707187, 554475821312, 30902266918, 0, 0, 0] := by
  decide +kernel

theorem rows7725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7725 = true := by
  decide +kernel

theorem tot7725 : totK PA10K2 A10K2.t7725 = [0, 0, 121142009141, 1040663296046, 2210691302499, 1458498636300, 245058391206, 6853348008, 0, 0] := by
  decide +kernel

theorem rows7726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7726 = true := by
  decide +kernel

theorem tot7726 : totK PA10K2 A10K2.t7726 = [0, 0, 0, 537898020747, 1971093099967, 2119073387797, 551366718752, 18540366428, 0, 0] := by
  decide +kernel

theorem rows7727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7727 = true := by
  decide +kernel

theorem tot7727 : totK PA10K2 A10K2.t7727 = [0, 0, 0, 588611314849, 1844542661903, 1879139343197, 593350568255, 50705464940, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

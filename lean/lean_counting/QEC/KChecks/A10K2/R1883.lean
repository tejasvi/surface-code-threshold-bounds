import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7532 = true := by
  decide +kernel

theorem tot7532 : totK PA10K2 A10K2.t7532 = [0, 0, 479425261710, 1561910128497, 1716349339950, 847001477378, 173901146316, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7533 = true := by
  decide +kernel

theorem tot7533 : totK PA10K2 A10K2.t7533 = [0, 0, 362601568456, 1634473820120, 2097321554263, 740535956131, 57425167665, 0, 0, 0] := by
  decide +kernel

theorem rows7534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7534 = true := by
  decide +kernel

theorem tot7534 : totK PA10K2 A10K2.t7534 = [0, 0, 0, 464767173811, 1850450484332, 1882084263581, 457953365219, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7535 = true := by
  decide +kernel

theorem tot7535 : totK PA10K2 A10K2.t7535 = [0, 0, 461452330429, 1739030482241, 1878087872995, 655435297130, 88266409410, 5718040558, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

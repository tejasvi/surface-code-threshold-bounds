import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7464 = true := by
  decide +kernel

theorem tot7464 : totK PA10K2 A10K2.t7464 = [0, 0, 510962829225, 1786644675404, 1885728918527, 710316998644, 70663383760, 0, 0, 0] := by
  decide +kernel

theorem rows7465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7465 = true := by
  decide +kernel

theorem tot7465 : totK PA10K2 A10K2.t7465 = [0, 0, 302107678445, 1506708220885, 2172810145224, 891159507797, 77033475373, 0, 0, 0] := by
  decide +kernel

theorem rows7466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7466 = true := by
  decide +kernel

theorem tot7466 : totK PA10K2 A10K2.t7466 = [0, 0, 142006382960, 942380159964, 2044226664678, 1512093765755, 262721517275, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7467 = true := by
  decide +kernel

theorem tot7467 : totK PA10K2 A10K2.t7467 = [0, 0, 514183048078, 1908716562086, 2029064997936, 570910645994, 23387981378, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

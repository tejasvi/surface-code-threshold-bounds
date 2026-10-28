import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7692 = true := by
  decide +kernel

theorem tot7692 : totK PA10K2 A10K2.t7692 = [0, 0, 0, 570531755480, 1836504799551, 1789841964462, 494168763627, 31941609474, 0, 0] := by
  decide +kernel

theorem rows7693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7693 = true := by
  decide +kernel

theorem tot7693 : totK PA10K2 A10K2.t7693 = [0, 0, 0, 0, 1109036169015, 2475924992630, 1003070083611, 65869213334, 0, 0] := by
  decide +kernel

theorem rows7694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7694 = true := by
  decide +kernel

theorem tot7694 : totK PA10K2 A10K2.t7694 = [0, 0, 0, 511028321977, 1661995585068, 1769037347334, 913308798234, 151155192225, 6354482628, 0] := by
  decide +kernel

theorem rows7695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7695 = true := by
  decide +kernel

theorem tot7695 : totK PA10K2 A10K2.t7695 = [0, 0, 0, 507955215705, 1843284957261, 1917319537835, 610014693474, 58055391887, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

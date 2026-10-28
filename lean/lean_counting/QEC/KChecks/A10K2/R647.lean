import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2588 = true := by
  decide +kernel

theorem tot2588 : totK PA10K2 A10K2.t2588 = [294549363032, 1209056681641, 1852108381852, 1140585345382, 183821060221, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2589 = true := by
  decide +kernel

theorem tot2589 : totK PA10K2 A10K2.t2589 = [455448278151, 1775015889267, 2006046245146, 599948071262, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2590 = true := by
  decide +kernel

theorem tot2590 : totK PA10K2 A10K2.t2590 = [0, 645075977529, 2013901570022, 1688153168487, 406425556706, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2591 = true := by
  decide +kernel

theorem tot2591 : totK PA10K2 A10K2.t2591 = [281821911550, 1133308153119, 1830824372779, 1252950209763, 222281995887, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

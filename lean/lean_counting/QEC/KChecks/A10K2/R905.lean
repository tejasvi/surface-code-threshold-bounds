import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3620 = true := by
  decide +kernel

theorem tot3620 : totK PA10K2 A10K2.t3620 = [0, 217694362673, 827722196598, 1552454611377, 1691121923463, 671716163474, 48083517153, 0, 0, 0] := by
  decide +kernel

theorem rows3621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3621 = true := by
  decide +kernel

theorem tot3621 : totK PA10K2 A10K2.t3621 = [0, 298857731666, 1528901078147, 2076877786478, 686062184390, 52575686575, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3622 = true := by
  decide +kernel

theorem tot3622 : totK PA10K2 A10K2.t3622 = [0, 200310268941, 741638145900, 1612390016503, 1588042977785, 417942703567, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows3623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3623 = true := by
  decide +kernel

theorem tot3623 : totK PA10K2 A10K2.t3623 = [0, 426700598477, 1788374900537, 2012805486499, 581866169995, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

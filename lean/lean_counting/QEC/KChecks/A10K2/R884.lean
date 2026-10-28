import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3536 = true := by
  decide +kernel

theorem tot3536 : totK PA10K2 A10K2.t3536 = [0, 0, 0, 615138157037, 2102006614146, 1981175210083, 397886146780, 6962742351, 0, 0] := by
  decide +kernel

theorem rows3537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3537 = true := by
  decide +kernel

theorem tot3537 : totK PA10K2 A10K2.t3537 = [0, 0, 0, 634745064573, 1957984748603, 1820918290182, 577913204722, 41498607772, 0, 0] := by
  decide +kernel

theorem rows3538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3538 = true := by
  decide +kernel

theorem tot3538 : totK PA10K2 A10K2.t3538 = [0, 0, 0, 466854879512, 1777359442075, 1953260358020, 535243809682, 32288062321, 0, 0] := by
  decide +kernel

theorem rows3539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3539 = true := by
  decide +kernel

theorem tot3539 : totK PA10K2 A10K2.t3539 = [0, 0, 0, 60690433792, 846366842029, 2090637308618, 1512309136336, 355057938367, 25565504801, 0] := by
  decide +kernel

end QECKChecks.A10K2

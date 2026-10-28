import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5672 = true := by
  decide +kernel

theorem tot5672 : totK PA10K2 A10K2.t5672 = [0, 0, 0, 623294151391, 2039073279397, 1695582674297, 402076704058, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5673 = true := by
  decide +kernel

theorem tot5673 : totK PA10K2 A10K2.t5673 = [0, 0, 344552455730, 1250564895327, 1761598642172, 1129846873544, 198954939653, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5674 = true := by
  decide +kernel

theorem tot5674 : totK PA10K2 A10K2.t5674 = [0, 0, 402692973434, 1760037527168, 1983157965372, 581154951850, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows5675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5675 = true := by
  decide +kernel

theorem tot5675 : totK PA10K2 A10K2.t5675 = [0, 0, 0, 705849009229, 2190123601064, 1510016310139, 185829332591, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

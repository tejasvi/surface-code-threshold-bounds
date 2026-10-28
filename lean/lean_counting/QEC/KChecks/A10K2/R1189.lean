import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4756 = true := by
  decide +kernel

theorem tot4756 : totK PA10K2 A10K2.t4756 = [0, 465631835236, 1805285841891, 1996757842786, 572405448547, 24516663070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4757 = true := by
  decide +kernel

theorem tot4757 : totK PA10K2 A10K2.t4757 = [0, 0, 657062302497, 2027558756968, 1666227327652, 401139461203, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4758 = true := by
  decide +kernel

theorem tot4758 : totK PA10K2 A10K2.t4758 = [0, 295989099618, 1147156336539, 1802856060960, 1244477375333, 224137286792, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4759 = true := by
  decide +kernel

theorem tot4759 : totK PA10K2 A10K2.t4759 = [0, 541623971559, 1944193124442, 1837470863417, 459607265781, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

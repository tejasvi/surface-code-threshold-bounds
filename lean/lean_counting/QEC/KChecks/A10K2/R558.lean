import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2232 = true := by
  decide +kernel

theorem tot2232 : totK PA10K2 A10K2.t2232 = [0, 0, 294983387133, 1393264774144, 2185312412287, 1050655763818, 89379582005, 0, 0, 0] := by
  decide +kernel

theorem rows2233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2233 = true := by
  decide +kernel

theorem tot2233 : totK PA10K2 A10K2.t2233 = [0, 0, 291551074069, 1292816674690, 1911101262914, 1104249541222, 210190812822, 7151180950, 0, 0] := by
  decide +kernel

theorem rows2234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2234 = true := by
  decide +kernel

theorem tot2234 : totK PA10K2 A10K2.t2234 = [0, 0, 576105234859, 1970501515044, 1846436139793, 402945214249, 12557093595, 0, 0, 0] := by
  decide +kernel

theorem rows2235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2235 = true := by
  decide +kernel

theorem tot2235 : totK PA10K2 A10K2.t2235 = [0, 0, 499162541144, 1837932492854, 2066349089965, 617088120782, 24957480370, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

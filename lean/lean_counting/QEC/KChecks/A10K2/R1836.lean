import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7344 = true := by
  decide +kernel

theorem tot7344 : totK PA10K2 A10K2.t7344 = [0, 0, 0, 0, 526615524176, 1902504356275, 1857162228261, 534244468127, 48453447732, 0] := by
  decide +kernel

theorem rows7345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7345 = true := by
  decide +kernel

theorem tot7345 : totK PA10K2 A10K2.t7345 = [0, 0, 0, 0, 534406259782, 1905554081888, 1847205653508, 389115197699, 10946789654, 0] := by
  decide +kernel

theorem rows7346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7346 = true := by
  decide +kernel

theorem tot7346 : totK PA10K2 A10K2.t7346 = [0, 0, 0, 0, 0, 765988565635, 2136200602388, 1510187250783, 278700755465, 7903172220] := by
  decide +kernel

theorem rows7347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7347 = true := by
  decide +kernel

theorem tot7347 : totK PA10K2 A10K2.t7347 = [0, 0, 0, 0, 505902306987, 1730681977791, 1819984357370, 620304475249, 45857479925, 0] := by
  decide +kernel

end QECKChecks.A10K2

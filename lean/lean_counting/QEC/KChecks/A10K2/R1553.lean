import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6212 = true := by
  decide +kernel

theorem tot6212 : totK PA10K2 A10K2.t6212 = [0, 0, 287871761280, 1228186004518, 1913768166664, 1137899838628, 194126698644, 5447185874, 0, 0] := by
  decide +kernel

theorem rows6213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6213 = true := by
  decide +kernel

theorem tot6213 : totK PA10K2 A10K2.t6213 = [0, 0, 461445071300, 1780053747868, 1888491129697, 517364322648, 23092108597, 0, 0, 0] := by
  decide +kernel

theorem rows6214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6214 = true := by
  decide +kernel

theorem tot6214 : totK PA10K2 A10K2.t6214 = [0, 0, 0, 704324817849, 2177417679804, 1481857936648, 214632560241, 0, 0, 0] := by
  decide +kernel

theorem rows6215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6215 = true := by
  decide +kernel

theorem tot6215 : totK PA10K2 A10K2.t6215 = [0, 0, 593149538699, 1986991025041, 1928391609361, 519504040276, 32323305334, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

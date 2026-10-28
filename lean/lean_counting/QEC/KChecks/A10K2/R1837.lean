import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7348 = true := by
  decide +kernel

theorem tot7348 : totK PA10K2 A10K2.t7348 = [0, 0, 0, 0, 531925410707, 1890046058703, 1845959273295, 406873977567, 15508376323, 0] := by
  decide +kernel

theorem rows7349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7349 = true := by
  decide +kernel

theorem tot7349 : totK PA10K2 A10K2.t7349 = [0, 0, 0, 306117011728, 1203817791385, 1819962604902, 1243677370706, 348293725091, 29010686974, 0] := by
  decide +kernel

theorem rows7350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7350 = true := by
  decide +kernel

theorem tot7350 : totK PA10K2 A10K2.t7350 = [0, 0, 0, 483587366435, 1776116005658, 1928913303360, 536831172632, 32040661968, 0, 0] := by
  decide +kernel

theorem rows7351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7351 = true := by
  decide +kernel

theorem tot7351 : totK PA10K2 A10K2.t7351 = [0, 0, 0, 0, 808344445686, 2257468367856, 1478338855969, 207991535575, 5300418178, 0] := by
  decide +kernel

end QECKChecks.A10K2

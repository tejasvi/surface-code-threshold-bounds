import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3176 = true := by
  decide +kernel

theorem tot3176 : totK PA10K2 A10K2.t3176 = [0, 322245181260, 977713555127, 848958973902, 359591240770, 740981906542, 1160230896244, 511713723036, 48886019071, 0] := by
  decide +kernel

theorem rows3177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3177 = true := by
  decide +kernel

theorem tot3177 : totK PA10K2 A10K2.t3177 = [0, 554005531953, 1946821383850, 1898595700961, 434931872010, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3178 = true := by
  decide +kernel

theorem tot3178 : totK PA10K2 A10K2.t3178 = [0, 0, 653619147310, 2074073471983, 1732630989503, 403655490736, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3179 = true := by
  decide +kernel

theorem tot3179 : totK PA10K2 A10K2.t3179 = [0, 146952719065, 932183654720, 1942577740051, 1435615108711, 244517811492, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

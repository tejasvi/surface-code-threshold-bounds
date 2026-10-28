import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7204 = true := by
  decide +kernel

theorem tot7204 : totK PA10K2 A10K2.t7204 = [0, 0, 365771833745, 1742470129585, 2120411862869, 597387695398, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows7205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7205 = true := by
  decide +kernel

theorem tot7205 : totK PA10K2 A10K2.t7205 = [0, 0, 271912620389, 1137738991786, 1864595980581, 1214688485959, 193852408168, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7206 = true := by
  decide +kernel

theorem tot7206 : totK PA10K2 A10K2.t7206 = [0, 0, 433858852770, 1627319372761, 1908249637861, 637499825997, 51963961291, 0, 0, 0] := by
  decide +kernel

theorem rows7207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7207 = true := by
  decide +kernel

theorem tot7207 : totK PA10K2 A10K2.t7207 = [0, 0, 113126642960, 1259723057776, 2308911680832, 935296242482, 66279907733, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

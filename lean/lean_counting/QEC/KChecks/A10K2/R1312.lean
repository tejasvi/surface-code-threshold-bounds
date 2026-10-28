import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5248 = true := by
  decide +kernel

theorem tot5248 : totK PA10K2 A10K2.t5248 = [0, 0, 0, 689187928509, 2140835941374, 1620946082236, 367352333684, 25313348169, 0, 0] := by
  decide +kernel

theorem rows5249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5249 = true := by
  decide +kernel

theorem tot5249 : totK PA10K2 A10K2.t5249 = [0, 0, 338743555992, 1392805569353, 2076563498231, 1178116491675, 141464238981, 0, 0, 0] := by
  decide +kernel

theorem rows5250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5250 = true := by
  decide +kernel

theorem tot5250 : totK PA10K2 A10K2.t5250 = [0, 0, 541650405231, 1972056137171, 2055166348950, 545215751089, 27751773878, 0, 0, 0] := by
  decide +kernel

theorem rows5251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5251 = true := by
  decide +kernel

theorem tot5251 : totK PA10K2 A10K2.t5251 = [0, 0, 191685022163, 1163575427746, 2103031959776, 1254784170349, 212521155324, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

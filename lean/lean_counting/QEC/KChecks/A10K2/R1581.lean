import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6324 = true := by
  decide +kernel

theorem tot6324 : totK PA10K2 A10K2.t6324 = [0, 0, 344772736539, 1276514762048, 1765902605082, 978851617659, 169011208113, 5453062850, 0, 0] := by
  decide +kernel

theorem rows6325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6325 = true := by
  decide +kernel

theorem tot6325 : totK PA10K2 A10K2.t6325 = [0, 0, 331908650820, 1577200120141, 1994549478561, 575614126585, 32763013480, 0, 0, 0] := by
  decide +kernel

theorem rows6326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6326 = true := by
  decide +kernel

theorem tot6326 : totK PA10K2 A10K2.t6326 = [0, 0, 193063589417, 966660360188, 1982177958710, 1279818912721, 193580033148, 5685526223, 0, 0] := by
  decide +kernel

theorem rows6327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6327 = true := by
  decide +kernel

theorem tot6327 : totK PA10K2 A10K2.t6327 = [0, 0, 579046821172, 2078436660180, 1935948180744, 432398884823, 20390176567, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

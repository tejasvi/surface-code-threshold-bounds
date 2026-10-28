import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7324 = true := by
  decide +kernel

theorem tot7324 : totK PA10K2 A10K2.t7324 = [0, 0, 298450480597, 1295457591462, 2054652131366, 1188482505222, 195938718520, 5459593153, 0, 0] := by
  decide +kernel

theorem rows7325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7325 = true := by
  decide +kernel

theorem tot7325 : totK PA10K2 A10K2.t7325 = [0, 0, 213902992100, 1249200748554, 2174862395092, 1344093844750, 223377171026, 7380853412, 0, 0] := by
  decide +kernel

theorem rows7326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7326 = true := by
  decide +kernel

theorem tot7326 : totK PA10K2 A10K2.t7326 = [0, 0, 477415298800, 1663995538712, 1999102484781, 846454086892, 83301814005, 0, 0, 0] := by
  decide +kernel

theorem rows7327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7327 = true := by
  decide +kernel

theorem tot7327 : totK PA10K2 A10K2.t7327 = [0, 0, 368284979990, 1646571082429, 2163134990746, 790662283706, 43735518589, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8144 = true := by
  decide +kernel

theorem tot8144 : totK PA10K2 A10K2.t8144 = [0, 0, 0, 200545299540, 1208220608582, 2144568513607, 1215863374923, 173407594913, 6904928264, 0] := by
  decide +kernel

theorem rows8145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8145 = true := by
  decide +kernel

theorem tot8145 : totK PA10K2 A10K2.t8145 = [0, 0, 0, 298479604829, 1372415620921, 2036058134429, 1017954908883, 118588271768, 0, 0] := by
  decide +kernel

theorem rows8146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8146 = true := by
  decide +kernel

theorem tot8146 : totK PA10K2 A10K2.t8146 = [0, 0, 0, 466273731196, 1769070175310, 2000042035383, 643376864943, 30700272673, 0, 0] := by
  decide +kernel

theorem rows8147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8147 = true := by
  decide +kernel

theorem tot8147 : totK PA10K2 A10K2.t8147 = [0, 0, 0, 0, 759419077309, 2215141806412, 1619523799967, 253676430850, 7047025452, 0] := by
  decide +kernel

end QECKChecks.A10K2

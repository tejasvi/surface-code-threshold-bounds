import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5676 = true := by
  decide +kernel

theorem tot5676 : totK PA10K2 A10K2.t5676 = [0, 0, 627544772511, 2052610224333, 1882550797413, 451499183135, 46898054538, 6239673734, 0, 0] := by
  decide +kernel

theorem rows5677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5677 = true := by
  decide +kernel

theorem tot5677 : totK PA10K2 A10K2.t5677 = [0, 0, 0, 772367018260, 2306221314760, 1726434227052, 269722281951, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5678 = true := by
  decide +kernel

theorem tot5678 : totK PA10K2 A10K2.t5678 = [0, 0, 0, 647384107433, 1973439577971, 1730753329640, 425425140153, 26479096260, 0, 0] := by
  decide +kernel

theorem rows5679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5679 = true := by
  decide +kernel

theorem tot5679 : totK PA10K2 A10K2.t5679 = [0, 0, 0, 299231901436, 1642568706754, 2164148251915, 726100751141, 46996116090, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

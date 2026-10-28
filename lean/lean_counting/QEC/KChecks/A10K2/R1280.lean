import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5120 = true := by
  decide +kernel

theorem tot5120 : totK PA10K2 A10K2.t5120 = [0, 0, 509574687410, 1863880243231, 1872332181330, 489324618559, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows5121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5121 = true := by
  decide +kernel

theorem tot5121 : totK PA10K2 A10K2.t5121 = [0, 0, 110080449477, 1266813063584, 2356606136416, 885558117883, 64875200388, 0, 0, 0] := by
  decide +kernel

theorem rows5122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5122 = true := by
  decide +kernel

theorem tot5122 : totK PA10K2 A10K2.t5122 = [0, 0, 455543143337, 1521813771787, 1768553158052, 846988955568, 148680141100, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5123 = true := by
  decide +kernel

theorem tot5123 : totK PA10K2 A10K2.t5123 = [0, 477404030452, 1538955799608, 1708456610165, 943827961190, 216648344013, 6782479114, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

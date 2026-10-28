import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1148 = true := by
  decide +kernel

theorem tot1148 : totK PA10K2 A10K2.t1148 = [0, 474063995440, 1652161779886, 1845056327497, 834398115799, 170200180636, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1149 = true := by
  decide +kernel

theorem tot1149 : totK PA10K2 A10K2.t1149 = [0, 309893393367, 1514680034527, 2178231907053, 895425166124, 76593608008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1150 = true := by
  decide +kernel

theorem tot1150 : totK PA10K2 A10K2.t1150 = [0, 0, 482600353417, 2006170179514, 2154372279037, 461432204903, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows1151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1151 = true := by
  decide +kernel

theorem tot1151 : totK PA10K2 A10K2.t1151 = [0, 0, 426190603225, 1581656988379, 2003620084661, 816584899507, 72699027451, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

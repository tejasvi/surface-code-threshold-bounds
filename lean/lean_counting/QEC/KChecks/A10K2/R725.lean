import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2900 = true := by
  decide +kernel

theorem tot2900 : totK PA10K2 A10K2.t2900 = [510881146888, 1916945326698, 2025479894198, 542311123880, 19857259794, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2901 = true := by
  decide +kernel

theorem tot2901 : totK PA10K2 A10K2.t2901 = [0, 523833179193, 1925614035734, 1835327904852, 439308084572, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2902 = true := by
  decide +kernel

theorem tot2902 : totK PA10K2 A10K2.t2902 = [280788281866, 1322775306223, 2000980630988, 1141456802433, 201098144189, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2903 = true := by
  decide +kernel

theorem tot2903 : totK PA10K2 A10K2.t2903 = [200263369735, 1208815969707, 2180753086399, 1129222089525, 116113243221, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1732 = true := by
  decide +kernel

theorem tot1732 : totK PA10K2 A10K2.t1732 = [0, 0, 0, 302031194261, 1509935894513, 2060510501001, 675778393041, 43663726050, 0, 0] := by
  decide +kernel

theorem rows1733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1733 = true := by
  decide +kernel

theorem tot1733 : totK PA10K2 A10K2.t1733 = [0, 0, 310152219116, 866435418229, 974553768267, 1381216842863, 970951707647, 177482208414, 6354482628, 0] := by
  decide +kernel

theorem rows1734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1734 = true := by
  decide +kernel

theorem tot1734 : totK PA10K2 A10K2.t1734 = [0, 0, 498328713856, 1904977066817, 2024702025407, 528060030536, 31611289403, 0, 0, 0] := by
  decide +kernel

theorem rows1735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1735 = true := by
  decide +kernel

theorem tot1735 : totK PA10K2 A10K2.t1735 = [0, 0, 0, 658119015120, 2086866131012, 1751883858998, 395276091498, 25351274858, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

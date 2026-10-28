import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2744 = true := by
  decide +kernel

theorem tot2744 : totK PA10K2 A10K2.t2744 = [0, 0, 0, 1015427963614, 2421897495452, 1148399435396, 105866975992, 0, 0, 0] := by
  decide +kernel

theorem rows2745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2745 = true := by
  decide +kernel

theorem tot2745 : totK PA10K2 A10K2.t2745 = [0, 0, 485543652834, 1476711129639, 1762430291595, 973323243219, 194271170553, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2746 = true := by
  decide +kernel

theorem tot2746 : totK PA10K2 A10K2.t2746 = [0, 0, 456267876050, 1771899399512, 1963729581983, 557730953618, 32546873520, 0, 0, 0] := by
  decide +kernel

theorem rows2747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2747 = true := by
  decide +kernel

theorem tot2747 : totK PA10K2 A10K2.t2747 = [0, 0, 237971421297, 1364172644638, 2076460163110, 818266494175, 65988555795, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

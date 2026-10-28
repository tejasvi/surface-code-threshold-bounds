import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3716 = true := by
  decide +kernel

theorem tot3716 : totK PA10K2 A10K2.t3716 = [0, 0, 473771900413, 1876321690898, 1984081319086, 483738388241, 13227942247, 0, 0, 0] := by
  decide +kernel

theorem rows3717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3717 = true := by
  decide +kernel

theorem tot3717 : totK PA10K2 A10K2.t3717 = [0, 0, 538854481313, 1757685543274, 1819909741099, 533410187059, 41637886261, 0, 0, 0] := by
  decide +kernel

theorem rows3718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3718 = true := by
  decide +kernel

theorem tot3718 : totK PA10K2 A10K2.t3718 = [0, 0, 40274886064, 1208760476290, 2401090080266, 944540013034, 77820506896, 0, 0, 0] := by
  decide +kernel

theorem rows3719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3719 = true := by
  decide +kernel

theorem tot3719 : totK PA10K2 A10K2.t3719 = [0, 0, 302616931391, 1212431598181, 1816005091761, 1051375315146, 213638840706, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

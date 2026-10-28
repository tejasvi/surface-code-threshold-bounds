import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3760 = true := by
  decide +kernel

theorem tot3760 : totK PA10K2 A10K2.t3760 = [0, 0, 230854897253, 1461414345503, 2248224049507, 897862409137, 57947937055, 0, 0, 0] := by
  decide +kernel

theorem rows3761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3761 = true := by
  decide +kernel

theorem tot3761 : totK PA10K2 A10K2.t3761 = [0, 0, 42689062562, 521154829059, 1834298925335, 1841419951884, 439809748647, 30831673886, 0, 0] := by
  decide +kernel

theorem rows3762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3762 = true := by
  decide +kernel

theorem tot3762 : totK PA10K2 A10K2.t3762 = [0, 0, 516667892269, 1925345950662, 1898916136150, 429715392943, 26056424064, 0, 0, 0] := by
  decide +kernel

theorem rows3763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3763 = true := by
  decide +kernel

theorem tot3763 : totK PA10K2 A10K2.t3763 = [0, 0, 0, 594415130554, 2138867573784, 1744708191143, 252121237538, 5393623172, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

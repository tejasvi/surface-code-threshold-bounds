import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2668 = true := by
  decide +kernel

theorem tot2668 : totK PA10K2 A10K2.t2668 = [0, 0, 0, 1017786857036, 2452303959842, 1092695574710, 78379076963, 0, 0, 0] := by
  decide +kernel

theorem rows2669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2669 = true := by
  decide +kernel

theorem tot2669 : totK PA10K2 A10K2.t2669 = [0, 0, 468465284177, 1612015439395, 1875663526575, 875325446513, 148649796905, 6121173289, 0, 0] := by
  decide +kernel

theorem rows2670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2670 = true := by
  decide +kernel

theorem tot2670 : totK PA10K2 A10K2.t2670 = [0, 238933747472, 1017710494132, 1671594417860, 1418902600539, 505028641096, 35778483473, 0, 0, 0] := by
  decide +kernel

theorem rows2671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2671 = true := by
  decide +kernel

theorem tot2671 : totK PA10K2 A10K2.t2671 = [0, 277618346867, 1301617840153, 1906707719587, 909425037933, 178592048785, 19641144955, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

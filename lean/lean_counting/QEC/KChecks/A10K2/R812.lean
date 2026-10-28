import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3248 = true := by
  decide +kernel

theorem tot3248 : totK PA10K2 A10K2.t3248 = [0, 0, 289153261105, 1480305469246, 2269432493412, 1033506419389, 90124919621, 0, 0, 0] := by
  decide +kernel

theorem rows3249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3249 = true := by
  decide +kernel

theorem tot3249 : totK PA10K2 A10K2.t3249 = [0, 0, 351787732470, 1494990813012, 2105011791470, 993672932788, 103798133194, 0, 0, 0] := by
  decide +kernel

theorem rows3250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3250 = true := by
  decide +kernel

theorem tot3250 : totK PA10K2 A10K2.t3250 = [0, 0, 455869960580, 1775622425396, 2035719520100, 676178361238, 28210332607, 0, 0, 0] := by
  decide +kernel

theorem rows3251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3251 = true := by
  decide +kernel

theorem tot3251 : totK PA10K2 A10K2.t3251 = [0, 0, 0, 542940429789, 1883920316461, 1878309508758, 516074212457, 31285368086, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4320 = true := by
  decide +kernel

theorem tot4320 : totK PA10K2 A10K2.t4320 = [0, 0, 511809732186, 1858642944523, 1882201083488, 585060131722, 57216052285, 0, 0, 0] := by
  decide +kernel

theorem rows4321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4321 = true := by
  decide +kernel

theorem tot4321 : totK PA10K2 A10K2.t4321 = [0, 0, 296671644335, 1401060555580, 2132850871072, 985393784384, 73053362083, 0, 0, 0] := by
  decide +kernel

theorem rows4322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4322 = true := by
  decide +kernel

theorem tot4322 : totK PA10K2 A10K2.t4322 = [0, 0, 279805444759, 1102372309681, 1945079919873, 1339825371341, 244001867865, 6904928264, 0, 0] := by
  decide +kernel

theorem rows4323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4323 = true := by
  decide +kernel

theorem tot4323 : totK PA10K2 A10K2.t4323 = [0, 0, 369100139156, 1641266977810, 2150013937020, 832865801064, 61972529853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

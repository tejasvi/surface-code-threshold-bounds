import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7356 = true := by
  decide +kernel

theorem tot7356 : totK PA10K2 A10K2.t7356 = [0, 0, 0, 455118883607, 1755860914950, 1987264467654, 665097573314, 46999956509, 0, 0] := by
  decide +kernel

theorem rows7357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7357 = true := by
  decide +kernel

theorem tot7357 : totK PA10K2 A10K2.t7357 = [0, 0, 0, 0, 773390117051, 2275828573743, 1531872545859, 289644139691, 13360781053, 0] := by
  decide +kernel

theorem rows7358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7358 = true := by
  decide +kernel

theorem tot7358 : totK PA10K2 A10K2.t7358 = [0, 0, 0, 622644221639, 1894609014781, 1794147399910, 758986971769, 83116478808, 0, 0] := by
  decide +kernel

theorem rows7359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7359 = true := by
  decide +kernel

theorem tot7359 : totK PA10K2 A10K2.t7359 = [0, 0, 0, 553173085458, 1970143825575, 2024470867587, 528605105923, 21929649243, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

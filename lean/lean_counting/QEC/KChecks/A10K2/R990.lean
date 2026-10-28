import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3960 = true := by
  decide +kernel

theorem tot3960 : totK PA10K2 A10K2.t3960 = [0, 0, 0, 768677563141, 2228855576087, 1647168921663, 277519900347, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3961 = true := by
  decide +kernel

theorem tot3961 : totK PA10K2 A10K2.t3961 = [0, 0, 534421757282, 1763207291628, 1852602787186, 701365398849, 62235866236, 0, 0, 0] := by
  decide +kernel

theorem rows3962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3962 = true := by
  decide +kernel

theorem tot3962 : totK PA10K2 A10K2.t3962 = [0, 0, 327291078893, 1569349024598, 2240378259179, 815767855130, 36915635290, 0, 0, 0] := by
  decide +kernel

theorem rows3963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3963 = true := by
  decide +kernel

theorem tot3963 : totK PA10K2 A10K2.t3963 = [0, 0, 0, 581742807504, 1960790310901, 1926658401272, 421506637955, 12224107035, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

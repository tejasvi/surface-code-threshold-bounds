import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6332 = true := by
  decide +kernel

theorem tot6332 : totK PA10K2 A10K2.t6332 = [0, 452811472891, 1613314853156, 1887106202915, 787203260527, 80650322637, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6333 = true := by
  decide +kernel

theorem tot6333 : totK PA10K2 A10K2.t6333 = [0, 290643499251, 1466092728778, 2073986139170, 769267598858, 53438372263, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6334 = true := by
  decide +kernel

theorem tot6334 : totK PA10K2 A10K2.t6334 = [0, 0, 606650268141, 1997730076863, 1650411358224, 285703114400, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6335 = true := by
  decide +kernel

theorem tot6335 : totK PA10K2 A10K2.t6335 = [0, 0, 576431513417, 1832366877836, 1814995891460, 501861464835, 32239129156, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

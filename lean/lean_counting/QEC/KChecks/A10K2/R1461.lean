import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5844 = true := by
  decide +kernel

theorem tot5844 : totK PA10K2 A10K2.t5844 = [0, 0, 0, 0, 800504751991, 2084098632270, 1284799473607, 303146631893, 24810156457, 0] := by
  decide +kernel

theorem rows5845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5845 = true := by
  decide +kernel

theorem tot5845 : totK PA10K2 A10K2.t5845 = [0, 0, 0, 377675826816, 1380063953850, 1757199803840, 922058436700, 164997116139, 5410721913, 0] := by
  decide +kernel

theorem rows5846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5846 = true := by
  decide +kernel

theorem tot5846 : totK PA10K2 A10K2.t5846 = [0, 0, 0, 398432494548, 1763548248045, 2001378327057, 540480287877, 32744407728, 0, 0] := by
  decide +kernel

theorem rows5847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5847 = true := by
  decide +kernel

theorem tot5847 : totK PA10K2 A10K2.t5847 = [0, 0, 0, 183892460298, 1027567081984, 2027066248857, 1169059562834, 171785988602, 5546304973, 0] := by
  decide +kernel

end QECKChecks.A10K2

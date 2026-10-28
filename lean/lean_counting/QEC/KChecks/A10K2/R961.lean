import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3844 = true := by
  decide +kernel

theorem tot3844 : totK PA10K2 A10K2.t3844 = [0, 0, 0, 452061141222, 1762562870219, 1965638585414, 544833727751, 32470943963, 0, 0] := by
  decide +kernel

theorem rows3845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3845 = true := by
  decide +kernel

theorem tot3845 : totK PA10K2 A10K2.t3845 = [0, 0, 0, 534561189226, 1862597191961, 1843064672192, 429051291214, 31169761322, 0, 0] := by
  decide +kernel

theorem rows3846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3846 = true := by
  decide +kernel

theorem tot3846 : totK PA10K2 A10K2.t3846 = [0, 0, 0, 307739496603, 1585889052114, 2080093550661, 656812353655, 51402059204, 0, 0] := by
  decide +kernel

theorem rows3847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3847 = true := by
  decide +kernel

theorem tot3847 : totK PA10K2 A10K2.t3847 = [0, 0, 0, 117105040969, 893023566578, 2052735335473, 1313244850059, 239904770714, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2

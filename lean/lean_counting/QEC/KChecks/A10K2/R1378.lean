import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5512 = true := by
  decide +kernel

theorem tot5512 : totK PA10K2 A10K2.t5512 = [0, 550461195332, 1854762767688, 1721113465887, 433089046684, 26491486257, 118623104844, 91540553519, 6354482628, 0] := by
  decide +kernel

theorem rows5513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5513 = true := by
  decide +kernel

theorem tot5513 : totK PA10K2 A10K2.t5513 = [0, 295110503507, 1455101753028, 2217150802563, 935881599606, 77528735098, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5514 = true := by
  decide +kernel

theorem tot5514 : totK PA10K2 A10K2.t5514 = [0, 0, 519678817344, 1830639833917, 1876460008514, 502566898858, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows5515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5515 = true := by
  decide +kernel

theorem tot5515 : totK PA10K2 A10K2.t5515 = [0, 499381326354, 1667679567889, 1879072242197, 790329090198, 85720966527, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

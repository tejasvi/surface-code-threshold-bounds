import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6244 = true := by
  decide +kernel

theorem tot6244 : totK PA10K2 A10K2.t6244 = [0, 0, 703490606683, 2118638303085, 1729672851209, 404959891421, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows6245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6245 = true := by
  decide +kernel

theorem tot6245 : totK PA10K2 A10K2.t6245 = [0, 278623868914, 1252030831509, 2119342804107, 1295003839364, 201596067281, 5809256573, 0, 0, 0] := by
  decide +kernel

theorem rows6246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6246 = true := by
  decide +kernel

theorem tot6246 : totK PA10K2 A10K2.t6246 = [0, 548284400172, 1967145802063, 1996382402287, 567945279364, 31952187130, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6247 = true := by
  decide +kernel

theorem tot6247 : totK PA10K2 A10K2.t6247 = [0, 0, 689092620209, 2221491947679, 1904434199009, 337382363650, 6585347165, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

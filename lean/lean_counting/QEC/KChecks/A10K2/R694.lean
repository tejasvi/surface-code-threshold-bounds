import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2776 = true := by
  decide +kernel

theorem tot2776 : totK PA10K2 A10K2.t2776 = [0, 537405445349, 1958827081524, 1885557012783, 474048566991, 30810868011, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2777 = true := by
  decide +kernel

theorem tot2777 : totK PA10K2 A10K2.t2777 = [594570731468, 1964809138054, 1921368265741, 590324169402, 53004717785, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2778 = true := by
  decide +kernel

theorem tot2778 : totK PA10K2 A10K2.t2778 = [0, 717330395191, 2150193025677, 1748049576166, 393944291485, 25581633552, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2779 = true := by
  decide +kernel

theorem tot2779 : totK PA10K2 A10K2.t2779 = [539000210498, 1856927184309, 1930345587032, 651364708449, 63554541602, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

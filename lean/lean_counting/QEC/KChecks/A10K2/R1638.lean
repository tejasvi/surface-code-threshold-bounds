import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6552 = true := by
  decide +kernel

theorem tot6552 : totK PA10K2 A10K2.t6552 = [0, 117663513915, 224719663617, 465445859715, 1686815845075, 1940459906748, 594561342464, 41590655314, 0, 0] := by
  decide +kernel

theorem rows6553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6553 = true := by
  decide +kernel

theorem tot6553 : totK PA10K2 A10K2.t6553 = [0, 465796653275, 1853468960142, 1952477838805, 498709675149, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6554 = true := by
  decide +kernel

theorem tot6554 : totK PA10K2 A10K2.t6554 = [0, 258566662976, 1305828953311, 2182890399841, 1076449817246, 102907066620, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6555 = true := by
  decide +kernel

theorem tot6555 : totK PA10K2 A10K2.t6555 = [0, 0, 523375395691, 1846862124925, 1847012755353, 490192242276, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

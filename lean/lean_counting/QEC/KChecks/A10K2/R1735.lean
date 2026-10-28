import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6940 = true := by
  decide +kernel

theorem tot6940 : totK PA10K2 A10K2.t6940 = [0, 68910543473, 868360527064, 2060140559522, 1545159393570, 371892867134, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows6941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6941 = true := by
  decide +kernel

theorem tot6941 : totK PA10K2 A10K2.t6941 = [0, 103659408021, 808156446691, 1984914801787, 1540477255675, 269355476123, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows6942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6942 = true := by
  decide +kernel

theorem tot6942 : totK PA10K2 A10K2.t6942 = [0, 481311407608, 1840494295763, 1901557904453, 495571173790, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6943 = true := by
  decide +kernel

theorem tot6943 : totK PA10K2 A10K2.t6943 = [0, 190150337554, 927669162699, 1980170464491, 1372779538252, 203177879795, 5982052406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

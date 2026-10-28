import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1120 = true := by
  decide +kernel

theorem tot1120 : totK PA10K2 A10K2.t1120 = [0, 0, 0, 432138039261, 1755089431417, 2156163853714, 709337979825, 36116611605, 0, 0] := by
  decide +kernel

theorem rows1121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1121 = true := by
  decide +kernel

theorem tot1121 : totK PA10K2 A10K2.t1121 = [0, 0, 0, 593864691976, 1972899875271, 1849002312177, 425892525587, 32686730107, 0, 0] := by
  decide +kernel

theorem rows1122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1122 = true := by
  decide +kernel

theorem tot1122 : totK PA10K2 A10K2.t1122 = [0, 0, 0, 183190376602, 1147102081770, 2140535785468, 1228281870528, 182046319862, 6860445330, 0] := by
  decide +kernel

theorem rows1123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1123 = true := by
  decide +kernel

theorem tot1123 : totK PA10K2 A10K2.t1123 = [0, 0, 0, 481711655646, 1788051542293, 1993328080926, 680243823763, 59905560340, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

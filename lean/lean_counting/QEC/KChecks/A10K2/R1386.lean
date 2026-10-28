import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5544 = true := by
  decide +kernel

theorem tot5544 : totK PA10K2 A10K2.t5544 = [0, 0, 528909875718, 1920161121796, 1949609320037, 494378521597, 12589269850, 0, 0, 0] := by
  decide +kernel

theorem rows5545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5545 = true := by
  decide +kernel

theorem tot5545 : totK PA10K2 A10K2.t5545 = [0, 0, 0, 563692992541, 1963293332959, 1769656055902, 421238925945, 25680132735, 0, 0] := by
  decide +kernel

theorem rows5546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5546 = true := by
  decide +kernel

theorem tot5546 : totK PA10K2 A10K2.t5546 = [0, 0, 292862383325, 1281381981596, 1954268407395, 1176771391290, 201331010027, 5626791703, 0, 0] := by
  decide +kernel

theorem rows5547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5547 = true := by
  decide +kernel

theorem tot5547 : totK PA10K2 A10K2.t5547 = [0, 0, 268591067345, 1509359398591, 2179171650289, 796504547144, 51296893539, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

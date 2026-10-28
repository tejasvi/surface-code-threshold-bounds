import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5368 = true := by
  decide +kernel

theorem tot5368 : totK PA10K2 A10K2.t5368 = [0, 0, 304495314875, 1479277837216, 2180555206504, 976920976551, 80975464393, 0, 0, 0] := by
  decide +kernel

theorem rows5369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5369 = true := by
  decide +kernel

theorem tot5369 : totK PA10K2 A10K2.t5369 = [0, 0, 0, 582324439511, 2038887611267, 1971223546894, 428372225939, 13653259670, 0, 0] := by
  decide +kernel

theorem rows5370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5370 = true := by
  decide +kernel

theorem tot5370 : totK PA10K2 A10K2.t5370 = [0, 322245181260, 1163813677455, 1214888172607, 748366282245, 978940750525, 502902642157, 49180423016, 0, 0] := by
  decide +kernel

theorem rows5371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5371 = true := by
  decide +kernel

theorem tot5371 : totK PA10K2 A10K2.t5371 = [0, 550059288319, 1917925353697, 1894844907008, 483148713638, 14688695882, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

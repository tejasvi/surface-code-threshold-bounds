import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6272 = true := by
  decide +kernel

theorem tot6272 : totK PA10K2 A10K2.t6272 = [0, 473026868623, 1802995793036, 1919258929527, 508448794320, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6273 = true := by
  decide +kernel

theorem tot6273 : totK PA10K2 A10K2.t6273 = [412332156094, 1569623561246, 1874167924054, 802383602771, 90333153551, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6274 = true := by
  decide +kernel

theorem tot6274 : totK PA10K2 A10K2.t6274 = [271289535470, 1434603759627, 2040205030102, 757073751318, 45031702936, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6275 = true := by
  decide +kernel

theorem tot6275 : totK PA10K2 A10K2.t6275 = [219843767392, 1025975748725, 2010991587707, 1286213201783, 228647653508, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

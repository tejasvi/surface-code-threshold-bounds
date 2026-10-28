import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6140 = true := by
  decide +kernel

theorem tot6140 : totK PA10K2 A10K2.t6140 = [0, 557707638591, 1905524986373, 1949665868718, 559486459257, 37520933532, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6141 = true := by
  decide +kernel

theorem tot6141 : totK PA10K2 A10K2.t6141 = [0, 0, 720713810160, 2223102767234, 1735493201176, 307486427456, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6142 = true := by
  decide +kernel

theorem tot6142 : totK PA10K2 A10K2.t6142 = [0, 0, 460849432582, 1782209237243, 2091558822172, 682279146516, 29860078966, 0, 0, 0] := by
  decide +kernel

theorem rows6143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6143 = true := by
  decide +kernel

theorem tot6143 : totK PA10K2 A10K2.t6143 = [0, 0, 508642500719, 1847868959510, 1892402662437, 544314593241, 51539370173, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

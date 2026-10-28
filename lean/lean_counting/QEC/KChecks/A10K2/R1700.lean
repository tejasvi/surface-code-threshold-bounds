import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6800 = true := by
  decide +kernel

theorem tot6800 : totK PA10K2 A10K2.t6800 = [0, 523212357774, 1818329177194, 1787946279922, 487031770582, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6801 = true := by
  decide +kernel

theorem tot6801 : totK PA10K2 A10K2.t6801 = [444538933688, 1627091430748, 1896947032890, 816034846357, 85720966527, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6802 = true := by
  decide +kernel

theorem tot6802 : totK PA10K2 A10K2.t6802 = [218009607367, 1203831317960, 2115641829915, 1138713735187, 177972430298, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6803 = true := by
  decide +kernel

theorem tot6803 : totK PA10K2 A10K2.t6803 = [614762885360, 1932384739334, 1883377540172, 571612394987, 44469520328, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

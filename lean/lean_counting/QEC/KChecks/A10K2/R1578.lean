import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6312 = true := by
  decide +kernel

theorem tot6312 : totK PA10K2 A10K2.t6312 = [0, 213469110619, 797229042318, 1560172238289, 1650152558756, 625480599625, 55043167628, 0, 0, 0] := by
  decide +kernel

theorem rows6313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6313 = true := by
  decide +kernel

theorem tot6313 : totK PA10K2 A10K2.t6313 = [0, 430508506172, 1743903902627, 1991342841494, 562419028570, 32731286466, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6314 = true := by
  decide +kernel

theorem tot6314 : totK PA10K2 A10K2.t6314 = [0, 225772793739, 1255087149009, 2204368044427, 1223521696284, 125591454856, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6315 = true := by
  decide +kernel

theorem tot6315 : totK PA10K2 A10K2.t6315 = [0, 0, 545691134600, 1881712354586, 1778171354536, 460163347105, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

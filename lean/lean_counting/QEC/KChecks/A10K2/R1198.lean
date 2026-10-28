import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4792 = true := by
  decide +kernel

theorem tot4792 : totK PA10K2 A10K2.t4792 = [0, 548589231577, 1844178396472, 1705836879149, 433089046684, 26491486257, 117388024790, 86874954689, 6354482628, 0] := by
  decide +kernel

theorem rows4793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4793 = true := by
  decide +kernel

theorem tot4793 : totK PA10K2 A10K2.t4793 = [0, 295110503507, 1454165217682, 2212733177874, 934292674237, 77528735098, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4794 = true := by
  decide +kernel

theorem tot4794 : totK PA10K2 A10K2.t4794 = [0, 0, 517806853589, 1829607299339, 1866791020765, 495584060782, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows4795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4795 = true := by
  decide +kernel

theorem tot4795 : totK PA10K2 A10K2.t4795 = [0, 520167364468, 1698733310950, 1830225344622, 768492901834, 85720966527, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

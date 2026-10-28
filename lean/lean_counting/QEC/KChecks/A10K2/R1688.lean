import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6752 = true := by
  decide +kernel

theorem tot6752 : totK PA10K2 A10K2.t6752 = [0, 0, 498007058213, 1914352576080, 2009220618839, 503970006577, 17732757243, 0, 0, 0] := by
  decide +kernel

theorem rows6753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6753 = true := by
  decide +kernel

theorem tot6753 : totK PA10K2 A10K2.t6753 = [0, 557168161444, 1761743104946, 1612586660173, 604393995530, 234691163646, 37310410385, 0, 0, 0] := by
  decide +kernel

theorem rows6754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6754 = true := by
  decide +kernel

theorem tot6754 : totK PA10K2 A10K2.t6754 = [0, 292221444102, 1511948013579, 2174369819104, 878321663121, 68612353862, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6755 = true := by
  decide +kernel

theorem tot6755 : totK PA10K2 A10K2.t6755 = [0, 0, 445436698231, 1772934952457, 1851419854263, 499948151499, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

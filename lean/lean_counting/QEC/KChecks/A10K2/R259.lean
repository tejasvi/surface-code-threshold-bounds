import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1036 = true := by
  decide +kernel

theorem tot1036 : totK PA10K2 A10K2.t1036 = [0, 0, 118410781347, 598356752302, 1603462826035, 1885150661968, 687495961380, 55043167628, 0, 0] := by
  decide +kernel

theorem rows1037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1037 = true := by
  decide +kernel

theorem tot1037 : totK PA10K2 A10K2.t1037 = [0, 0, 462177446453, 1774445921330, 1911501514692, 543214520701, 32731286466, 0, 0, 0] := by
  decide +kernel

theorem rows1038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1038 = true := by
  decide +kernel

theorem tot1038 : totK PA10K2 A10K2.t1038 = [0, 0, 266283149346, 1361428508043, 2182327818886, 1127231821404, 112703890813, 0, 0, 0] := by
  decide +kernel

theorem rows1039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1039 = true := by
  decide +kernel

theorem tot1039 : totK PA10K2 A10K2.t1039 = [0, 0, 0, 524758292726, 1848163911421, 1839190958463, 467768230217, 31543789865, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

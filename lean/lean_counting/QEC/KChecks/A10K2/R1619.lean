import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6476 = true := by
  decide +kernel

theorem tot6476 : totK PA10K2 A10K2.t6476 = [0, 0, 328041330167, 1484598595978, 2147611348165, 934950691188, 68645789942, 0, 0, 0] := by
  decide +kernel

theorem rows6477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6477 = true := by
  decide +kernel

theorem tot6477 : totK PA10K2 A10K2.t6477 = [0, 0, 0, 599933790960, 2019139831884, 1837865743144, 385508334691, 12132367858, 0, 0] := by
  decide +kernel

theorem rows6478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6478 = true := by
  decide +kernel

theorem tot6478 : totK PA10K2 A10K2.t6478 = [0, 322245181260, 1137569404266, 1155071344643, 747840421105, 1017498393708, 501217979401, 48886019071, 0, 0] := by
  decide +kernel

theorem rows6479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6479 = true := by
  decide +kernel

theorem tot6479 : totK PA10K2 A10K2.t6479 = [0, 549999419660, 1943781512458, 1913394143742, 452679334723, 9293389522, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

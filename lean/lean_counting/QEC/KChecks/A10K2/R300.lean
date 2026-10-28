import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1200 = true := by
  decide +kernel

theorem tot1200 : totK PA10K2 A10K2.t1200 = [0, 0, 0, 682851718234, 1990165880949, 1660178951935, 501008091028, 108466906140, 5528811039, 0] := by
  decide +kernel

theorem rows1201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1201 = true := by
  decide +kernel

theorem tot1201 : totK PA10K2 A10K2.t1201 = [0, 0, 323447547955, 1203106883826, 1816341096199, 1257944302021, 371352274899, 29010686974, 0, 0] := by
  decide +kernel

theorem rows1202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1202 = true := by
  decide +kernel

theorem tot1202 : totK PA10K2 A10K2.t1202 = [0, 0, 477695379004, 1827770827107, 1968252156026, 599381223618, 35698002757, 0, 0, 0] := by
  decide +kernel

theorem rows1203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1203 = true := by
  decide +kernel

theorem tot1203 : totK PA10K2 A10K2.t1203 = [0, 0, 0, 537475243303, 1950841195461, 1759953054030, 415619247057, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

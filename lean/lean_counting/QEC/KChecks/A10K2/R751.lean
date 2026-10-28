import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3004 = true := by
  decide +kernel

theorem tot3004 : totK PA10K2 A10K2.t3004 = [0, 0, 317619887890, 1157765193412, 1560291477317, 1278786268347, 520579609458, 48886019071, 0, 0] := by
  decide +kernel

theorem rows3005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3005 = true := by
  decide +kernel

theorem tot3005 : totK PA10K2 A10K2.t3005 = [0, 0, 527099952449, 1877888179241, 1922512942850, 513958240247, 12771851411, 0, 0, 0] := by
  decide +kernel

theorem rows3006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3006 = true := by
  decide +kernel

theorem tot3006 : totK PA10K2 A10K2.t3006 = [0, 0, 0, 592763193588, 1982777804527, 1694974937972, 399796372296, 25371180993, 0, 0] := by
  decide +kernel

theorem rows3007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3007 = true := by
  decide +kernel

theorem tot3007 : totK PA10K2 A10K2.t3007 = [0, 0, 291919316456, 1270048058425, 1919349952237, 1131755996821, 196599579198, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

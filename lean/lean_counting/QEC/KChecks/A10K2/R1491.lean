import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5964 = true := by
  decide +kernel

theorem tot5964 : totK PA10K2 A10K2.t5964 = [0, 0, 642681217549, 2104865354181, 1573370578665, 268390082535, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5965 = true := by
  decide +kernel

theorem tot5965 : totK PA10K2 A10K2.t5965 = [0, 0, 442507190543, 1772097770028, 1916392794772, 504748473774, 25633273041, 0, 0, 0] := by
  decide +kernel

theorem rows5966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5966 = true := by
  decide +kernel

theorem tot5966 : totK PA10K2 A10K2.t5966 = [0, 0, 590102567239, 1974382345385, 1823655616529, 405333900090, 13035108529, 0, 0, 0] := by
  decide +kernel

theorem rows5967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5967 = true := by
  decide +kernel

theorem tot5967 : totK PA10K2 A10K2.t5967 = [0, 0, 530280196164, 1804477615463, 1793117345853, 462695833259, 30637645759, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

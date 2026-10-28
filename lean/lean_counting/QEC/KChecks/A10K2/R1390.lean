import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5560 = true := by
  decide +kernel

theorem tot5560 : totK PA10K2 A10K2.t5560 = [0, 0, 0, 589489073003, 2035724126704, 1896647906176, 379308907225, 12219140272, 0, 0] := by
  decide +kernel

theorem rows5561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5561 = true := by
  decide +kernel

theorem tot5561 : totK PA10K2 A10K2.t5561 = [0, 0, 538234243656, 1864053445571, 1924235840624, 588565791232, 56281024929, 0, 0, 0] := by
  decide +kernel

theorem rows5562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5562 = true := by
  decide +kernel

theorem tot5562 : totK PA10K2 A10K2.t5562 = [0, 0, 329115212409, 1576868068786, 2171588793251, 881933897915, 64470155742, 0, 0, 0] := by
  decide +kernel

theorem rows5563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5563 = true := by
  decide +kernel

theorem tot5563 : totK PA10K2 A10K2.t5563 = [0, 0, 0, 509573548632, 1998208295087, 2059773628996, 435593715910, 13653259670, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

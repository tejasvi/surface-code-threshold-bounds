import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t552 = true := by
  decide +kernel

theorem tot552 : totK PA10K2 A10K2.t552 = [168648963668, 909437708726, 1872084958477, 1445609381479, 356278498564, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t553 = true := by
  decide +kernel

theorem tot553 : totK PA10K2 A10K2.t553 = [283150731151, 1166901585577, 1842581696321, 1221150946765, 220259007262, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t554 = true := by
  decide +kernel

theorem tot554 : totK PA10K2 A10K2.t554 = [416581648771, 1695755264896, 1997923105756, 582651474068, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t555 = true := by
  decide +kernel

theorem tot555 : totK PA10K2 A10K2.t555 = [0, 669412419012, 1959441845833, 1578459707814, 382776683781, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

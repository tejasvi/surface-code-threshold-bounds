import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4948 = true := by
  decide +kernel

theorem tot4948 : totK PA10K2 A10K2.t4948 = [0, 176859691838, 949802043514, 2012720375611, 1329502604386, 192946625267, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4949 = true := by
  decide +kernel

theorem tot4949 : totK PA10K2 A10K2.t4949 = [0, 449418711251, 1780970221696, 1993745400132, 579871496974, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4950 = true := by
  decide +kernel

theorem tot4950 : totK PA10K2 A10K2.t4950 = [0, 155477502832, 983811999736, 1945104180007, 1450420829118, 360945034826, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4951 = true := by
  decide +kernel

theorem tot4951 : totK PA10K2 A10K2.t4951 = [0, 236817354085, 1031522300978, 1860235663360, 1364226101527, 241674566794, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

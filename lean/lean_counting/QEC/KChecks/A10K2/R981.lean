import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3924 = true := by
  decide +kernel

theorem tot3924 : totK PA10K2 A10K2.t3924 = [0, 541416715838, 1841650277598, 1860511004274, 538200104055, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3925 = true := by
  decide +kernel

theorem tot3925 : totK PA10K2 A10K2.t3925 = [0, 0, 722032371730, 2111933917702, 1692920125111, 399027544634, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3926 = true := by
  decide +kernel

theorem tot3926 : totK PA10K2 A10K2.t3926 = [0, 163396409035, 921802696376, 1991721844037, 1450972681871, 245079539789, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows3927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3927 = true := by
  decide +kernel

theorem tot3927 : totK PA10K2 A10K2.t3927 = [0, 480147923864, 1862342748085, 1936576098129, 492704377037, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

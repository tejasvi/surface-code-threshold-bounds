import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7432 = true := by
  decide +kernel

theorem tot7432 : totK PA10K2 A10K2.t7432 = [0, 0, 976067963153, 2352668878152, 1127904896031, 83600470310, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7433 = true := by
  decide +kernel

theorem tot7433 : totK PA10K2 A10K2.t7433 = [0, 478109165658, 1578093326978, 1813294485466, 937592494892, 184217132632, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7434 = true := by
  decide +kernel

theorem tot7434 : totK PA10K2 A10K2.t7434 = [0, 310203719009, 1502000782567, 2201988274615, 963600688490, 78058078513, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7435 = true := by
  decide +kernel

theorem tot7435 : totK PA10K2 A10K2.t7435 = [0, 0, 609641037450, 2083897569396, 1949758732116, 427582917533, 13732569049, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

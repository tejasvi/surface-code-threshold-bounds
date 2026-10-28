import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2020 = true := by
  decide +kernel

theorem tot2020 : totK PA10K2 A10K2.t2020 = [0, 0, 46039240014, 900237966137, 2204557346982, 1595004121563, 269792675276, 6772895877, 0, 0] := by
  decide +kernel

theorem rows2021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2021 = true := by
  decide +kernel

theorem tot2021 : totK PA10K2 A10K2.t2021 = [0, 0, 0, 539822430341, 2009339804019, 2007021278041, 455235228715, 12773195692, 0, 0] := by
  decide +kernel

theorem rows2022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2022 = true := by
  decide +kernel

theorem tot2022 : totK PA10K2 A10K2.t2022 = [0, 0, 0, 456391399560, 1703942836410, 1950923407840, 668942269346, 55284946814, 0, 0] := by
  decide +kernel

theorem rows2023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2023 = true := by
  decide +kernel

theorem tot2023 : totK PA10K2 A10K2.t2023 = [0, 0, 0, 305806834516, 1417485393209, 2153248214244, 1029381742812, 94610905165, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

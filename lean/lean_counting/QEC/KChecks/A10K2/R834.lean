import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3336 = true := by
  decide +kernel

theorem tot3336 : totK PA10K2 A10K2.t3336 = [0, 0, 348838552832, 1428681653671, 1932353184464, 973209160733, 159646694885, 5517381808, 0, 0] := by
  decide +kernel

theorem rows3337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3337 = true := by
  decide +kernel

theorem tot3337 : totK PA10K2 A10K2.t3337 = [0, 0, 207074857515, 1390494053939, 2172176353565, 841844733209, 65953746422, 0, 0, 0] := by
  decide +kernel

theorem rows3338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3338 = true := by
  decide +kernel

theorem tot3338 : totK PA10K2 A10K2.t3338 = [0, 0, 495483244363, 1637088986521, 1814814505973, 822323929993, 138590943121, 6121173289, 0, 0] := by
  decide +kernel

theorem rows3339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3339 = true := by
  decide +kernel

theorem tot3339 : totK PA10K2 A10K2.t3339 = [0, 106966390865, 539045842111, 1482073393831, 1973701857630, 851443209470, 76344806208, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

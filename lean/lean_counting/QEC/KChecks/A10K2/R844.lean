import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3376 = true := by
  decide +kernel

theorem tot3376 : totK PA10K2 A10K2.t3376 = [0, 0, 0, 527355561699, 1963046851872, 2070997172533, 490309716162, 12199886344, 0, 0] := by
  decide +kernel

theorem rows3377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3377 = true := by
  decide +kernel

theorem tot3377 : totK PA10K2 A10K2.t3377 = [0, 0, 321728677231, 1201025609474, 1652153233063, 1323314010167, 533480687011, 42648501256, 0, 0] := by
  decide +kernel

theorem rows3378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3378 = true := by
  decide +kernel

theorem tot3378 : totK PA10K2 A10K2.t3378 = [0, 0, 303506427061, 1438683791014, 2190729922218, 1049735521970, 101852046497, 0, 0, 0] := by
  decide +kernel

theorem rows3379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3379 = true := by
  decide +kernel

theorem tot3379 : totK PA10K2 A10K2.t3379 = [0, 0, 302473110854, 1292344519423, 1996118244856, 1236558761505, 202666745977, 7685602490, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

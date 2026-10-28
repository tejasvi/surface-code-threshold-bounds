import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3864 = true := by
  decide +kernel

theorem tot3864 : totK PA10K2 A10K2.t3864 = [0, 0, 0, 263649460354, 1190436184634, 1912945539923, 1066971578934, 183043125638, 6034215561, 0] := by
  decide +kernel

theorem rows3865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3865 = true := by
  decide +kernel

theorem tot3865 : totK PA10K2 A10K2.t3865 = [0, 0, 0, 577154384443, 1935495425867, 1770521034702, 428262829911, 26386655430, 0, 0] := by
  decide +kernel

theorem rows3866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3866 = true := by
  decide +kernel

theorem tot3866 : totK PA10K2 A10K2.t3866 = [0, 0, 0, 0, 967476607571, 2381607667122, 1154278381981, 106096018005, 0, 0] := by
  decide +kernel

theorem rows3867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3867 = true := by
  decide +kernel

theorem tot3867 : totK PA10K2 A10K2.t3867 = [0, 0, 0, 0, 559780871083, 2015807359861, 1612928460924, 354712591243, 11740475125, 0] := by
  decide +kernel

end QECKChecks.A10K2

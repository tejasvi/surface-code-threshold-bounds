import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5112 = true := by
  decide +kernel

theorem tot5112 : totK PA10K2 A10K2.t5112 = [0, 283653827384, 1188844608231, 1832460368978, 1175963619812, 190379080767, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5113 = true := by
  decide +kernel

theorem tot5113 : totK PA10K2 A10K2.t5113 = [0, 500003266873, 1744751162400, 1855233077215, 625368495824, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5114 = true := by
  decide +kernel

theorem tot5114 : totK PA10K2 A10K2.t5114 = [0, 0, 1029331135517, 2422914905751, 1213704506167, 107172403957, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5115 = true := by
  decide +kernel

theorem tot5115 : totK PA10K2 A10K2.t5115 = [0, 429138988169, 1394933482958, 1767409059581, 984609611865, 193933203403, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

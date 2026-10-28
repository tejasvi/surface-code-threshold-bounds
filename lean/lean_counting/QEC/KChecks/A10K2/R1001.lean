import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4004 = true := by
  decide +kernel

theorem tot4004 : totK PA10K2 A10K2.t4004 = [0, 0, 546919607413, 1921785554047, 1838355515962, 443001853600, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows4005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4005 = true := by
  decide +kernel

theorem tot4005 : totK PA10K2 A10K2.t4005 = [0, 0, 187507762187, 1166125356428, 2051557642320, 1201366732367, 249543402886, 13364899180, 0, 0] := by
  decide +kernel

theorem rows4006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4006 = true := by
  decide +kernel

theorem tot4006 : totK PA10K2 A10K2.t4006 = [0, 0, 264151462795, 1249556485168, 1962413089528, 1192305094526, 174718485061, 0, 0, 0] := by
  decide +kernel

theorem rows4007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4007 = true := by
  decide +kernel

theorem tot4007 : totK PA10K2 A10K2.t4007 = [0, 0, 312323492180, 1497649289644, 2161878878424, 829957904027, 72022002678, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

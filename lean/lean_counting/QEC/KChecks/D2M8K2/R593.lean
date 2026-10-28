import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2372 = true := by
  decide +kernel

theorem tot2372 : totK PD2M8K2 D2M8K2.t2372 = [0, 151040374326, 364890022560, 272623621044, 104526830886, 6799735859, 0, 0] := by
  decide +kernel

theorem rows2373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2373 = true := by
  decide +kernel

theorem tot2373 : totK PD2M8K2 D2M8K2.t2373 = [0, 156935523151, 441694166913, 281681598783, 29718550901, 0, 0, 0] := by
  decide +kernel

theorem rows2374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2374 = true := by
  decide +kernel

theorem tot2374 : totK PD2M8K2 D2M8K2.t2374 = [0, 122942284081, 435643000461, 318421729480, 27631992622, 0, 0, 0] := by
  decide +kernel

theorem rows2375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2375 = true := by
  decide +kernel

theorem tot2375 : totK PD2M8K2 D2M8K2.t2375 = [0, 0, 204360783900, 484963939337, 190020771168, 9668735432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

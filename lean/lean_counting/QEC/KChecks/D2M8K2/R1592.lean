import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6368 = true := by
  decide +kernel

theorem tot6368 : totK PD2M8K2 D2M8K2.t6368 = [0, 122690015995, 354893909793, 319529186697, 84405282959, 3783381897, 0, 0] := by
  decide +kernel

theorem rows6369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6369 = true := by
  decide +kernel

theorem tot6369 : totK PD2M8K2 D2M8K2.t6369 = [0, 174217875790, 440556922540, 271181683634, 29792123112, 0, 0, 0] := by
  decide +kernel

theorem rows6370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6370 = true := by
  decide +kernel

theorem tot6370 : totK PD2M8K2 D2M8K2.t6370 = [0, 126048264038, 437710609046, 317739507740, 22988169556, 0, 0, 0] := by
  decide +kernel

theorem rows6371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6371 = true := by
  decide +kernel

theorem tot6371 : totK PD2M8K2 D2M8K2.t6371 = [0, 0, 211682487984, 494649811874, 170745294529, 4939878662, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

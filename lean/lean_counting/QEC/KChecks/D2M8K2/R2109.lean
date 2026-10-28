import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8436 = true := by
  decide +kernel

theorem tot8436 : totK PD2M8K2 D2M8K2.t8436 = [0, 89898082331, 387807826212, 400704700841, 50292086228, 0, 0, 0] := by
  decide +kernel

theorem rows8437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8437 = true := by
  decide +kernel

theorem tot8437 : totK PD2M8K2 D2M8K2.t8437 = [0, 171981872513, 444772980454, 274685591426, 24431554739, 0, 0, 0] := by
  decide +kernel

theorem rows8438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8438 = true := by
  decide +kernel

theorem tot8438 : totK PD2M8K2 D2M8K2.t8438 = [0, 84636189914, 409257686413, 377763332411, 51475097921, 0, 0, 0] := by
  decide +kernel

theorem rows8439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8439 = true := by
  decide +kernel

theorem tot8439 : totK PD2M8K2 D2M8K2.t8439 = [0, 0, 218018067685, 505602160850, 167052934153, 5348807592, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

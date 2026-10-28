import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14320 = true := by
  decide +kernel

theorem tot14320 : totK PD2M8K2 D2M8K2.t14320 = [0, 0, 186119176682, 468177100227, 195747791941, 10748563089, 0, 0] := by
  decide +kernel

theorem rows14321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14321 = true := by
  decide +kernel

theorem tot14321 : totK PD2M8K2 D2M8K2.t14321 = [0, 0, 206196719662, 493097503262, 180546644155, 5202589208, 0, 0] := by
  decide +kernel

theorem rows14322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14322 = true := by
  decide +kernel

theorem tot14322 : totK PD2M8K2 D2M8K2.t14322 = [0, 0, 257286981279, 489333514649, 149651151077, 3904855968, 0, 0] := by
  decide +kernel

theorem rows14323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14323 = true := by
  decide +kernel

theorem tot14323 : totK PD2M8K2 D2M8K2.t14323 = [0, 183175457280, 372969787088, 266950951893, 101319100043, 8859721110, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

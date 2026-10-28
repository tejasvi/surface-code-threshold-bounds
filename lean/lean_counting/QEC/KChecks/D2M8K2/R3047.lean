import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12188 = true := by
  decide +kernel

theorem tot12188 : totK PD2M8K2 D2M8K2.t12188 = [0, 178379215039, 467444120704, 228794724066, 15826413721, 0, 0, 0] := by
  decide +kernel

theorem rows12189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12189 = true := by
  decide +kernel

theorem tot12189 : totK PD2M8K2 D2M8K2.t12189 = [0, 173455847626, 464702711857, 214557007790, 15367806931, 0, 0, 0] := by
  decide +kernel

theorem rows12190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12190 = true := by
  decide +kernel

theorem tot12190 : totK PD2M8K2 D2M8K2.t12190 = [0, 81747954959, 320983092919, 368746305235, 90670839614, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12191 = true := by
  decide +kernel

theorem tot12191 : totK PD2M8K2 D2M8K2.t12191 = [0, 37180689048, 354739594466, 418517599885, 53345994976, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

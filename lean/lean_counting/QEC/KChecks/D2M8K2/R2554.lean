import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10216 = true := by
  decide +kernel

theorem tot10216 : totK PD2M8K2 D2M8K2.t10216 = [0, 0, 181584601410, 479742811863, 205359756206, 8126438242, 0, 0] := by
  decide +kernel

theorem rows10217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10217 = true := by
  decide +kernel

theorem tot10217 : totK PD2M8K2 D2M8K2.t10217 = [0, 0, 211694734146, 496230709174, 195236681236, 5516070556, 0, 0] := by
  decide +kernel

theorem rows10218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10218 = true := by
  decide +kernel

theorem tot10218 : totK PD2M8K2 D2M8K2.t10218 = [0, 0, 187869081267, 468843432978, 215029342461, 12319708528, 0, 0] := by
  decide +kernel

theorem rows10219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10219 = true := by
  decide +kernel

theorem tot10219 : totK PD2M8K2 D2M8K2.t10219 = [0, 0, 154738138854, 482586472060, 242498258819, 10178307621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

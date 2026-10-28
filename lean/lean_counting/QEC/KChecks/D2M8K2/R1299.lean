import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5196 = true := by
  decide +kernel

theorem tot5196 : totK PD2M8K2 D2M8K2.t5196 = [0, 0, 0, 274986205933, 500902941669, 125965212840, 3884009855, 0] := by
  decide +kernel

theorem rows5197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5197 = true := by
  decide +kernel

theorem tot5197 : totK PD2M8K2 D2M8K2.t5197 = [0, 0, 0, 189058261836, 480958269360, 181815937494, 4631785612, 0] := by
  decide +kernel

theorem rows5198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5198 = true := by
  decide +kernel

theorem tot5198 : totK PD2M8K2 D2M8K2.t5198 = [0, 0, 0, 216037708723, 478130545520, 181928790282, 4359462320, 0] := by
  decide +kernel

theorem rows5199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5199 = true := by
  decide +kernel

theorem tot5199 : totK PD2M8K2 D2M8K2.t5199 = [0, 0, 0, 178439111754, 459930136401, 226270600339, 19759852146, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

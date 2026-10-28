import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12872 = true := by
  decide +kernel

theorem tot12872 : totK PD2M8K2 D2M8K2.t12872 = [0, 0, 178988552995, 462383656569, 228056590148, 17080783126, 0, 0] := by
  decide +kernel

theorem rows12873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12873 = true := by
  decide +kernel

theorem tot12873 : totK PD2M8K2 D2M8K2.t12873 = [0, 0, 175525105897, 443456411018, 270600917174, 27211808630, 0, 0] := by
  decide +kernel

theorem rows12874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12874 = true := by
  decide +kernel

theorem tot12874 : totK PD2M8K2 D2M8K2.t12874 = [0, 0, 210794541055, 490373342645, 211451182796, 6761488205, 0, 0] := by
  decide +kernel

theorem rows12875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12875 = true := by
  decide +kernel

theorem tot12875 : totK PD2M8K2 D2M8K2.t12875 = [0, 0, 193262476082, 482194435233, 224547885739, 12889457677, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

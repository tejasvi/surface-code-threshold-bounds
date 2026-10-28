import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5160 = true := by
  decide +kernel

theorem tot5160 : totK PD2M8K2 D2M8K2.t5160 = [0, 0, 0, 288571878272, 503125385463, 86510164710, 1310517177, 0] := by
  decide +kernel

theorem rows5161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5161 = true := by
  decide +kernel

theorem tot5161 : totK PD2M8K2 D2M8K2.t5161 = [0, 0, 112050439025, 383582100197, 382523756648, 46531846786, 0, 0] := by
  decide +kernel

theorem rows5162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5162 = true := by
  decide +kernel

theorem tot5162 : totK PD2M8K2 D2M8K2.t5162 = [0, 0, 200678106423, 478945274010, 226903058381, 13579062837, 0, 0] := by
  decide +kernel

theorem rows5163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5163 = true := by
  decide +kernel

theorem tot5163 : totK PD2M8K2 D2M8K2.t5163 = [0, 0, 103021327743, 439226800135, 338337521217, 36304814517, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9724 = true := by
  decide +kernel

theorem tot9724 : totK PD2M8K2 D2M8K2.t9724 = [0, 90367468423, 250506513747, 341574506736, 208611357123, 18903156979, 0, 0] := by
  decide +kernel

theorem rows9725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9725 = true := by
  decide +kernel

theorem tot9725 : totK PD2M8K2 D2M8K2.t9725 = [0, 169452947277, 471796526478, 232207004854, 8865171003, 0, 0, 0] := by
  decide +kernel

theorem rows9726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9726 = true := by
  decide +kernel

theorem tot9726 : totK PD2M8K2 D2M8K2.t9726 = [0, 153692282375, 447814215970, 267211100972, 20321337899, 0, 0, 0] := by
  decide +kernel

theorem rows9727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9727 = true := by
  decide +kernel

theorem tot9727 : totK PD2M8K2 D2M8K2.t9727 = [0, 0, 271429125044, 500121031988, 100382577759, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

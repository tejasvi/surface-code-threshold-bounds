import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12600 = true := by
  decide +kernel

theorem tot12600 : totK PD2M8K2 D2M8K2.t12600 = [0, 0, 0, 300042953221, 473931367368, 88849830756, 1095107716, 0] := by
  decide +kernel

theorem rows12601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12601 = true := by
  decide +kernel

theorem tot12601 : totK PD2M8K2 D2M8K2.t12601 = [0, 141777946573, 295910850972, 166190328789, 197055260836, 88685288383, 3882006667, 0] := by
  decide +kernel

theorem rows12602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12602 = true := by
  decide +kernel

theorem tot12602 : totK PD2M8K2 D2M8K2.t12602 = [0, 176064715649, 455186185697, 232473511811, 17101706881, 0, 0, 0] := by
  decide +kernel

theorem rows12603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12603 = true := by
  decide +kernel

theorem tot12603 : totK PD2M8K2 D2M8K2.t12603 = [0, 100384071578, 414043451186, 346554226529, 38266614580, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

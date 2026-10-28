import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6084 = true := by
  decide +kernel

theorem tot6084 : totK PD2M8K2 D2M8K2.t6084 = [0, 0, 166517838695, 476093013218, 238467474121, 12443528988, 0, 0] := by
  decide +kernel

theorem rows6085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6085 = true := by
  decide +kernel

theorem tot6085 : totK PD2M8K2 D2M8K2.t6085 = [0, 0, 173639433955, 455304127707, 241738908753, 17142859432, 0, 0] := by
  decide +kernel

theorem rows6086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6086 = true := by
  decide +kernel

theorem tot6086 : totK PD2M8K2 D2M8K2.t6086 = [0, 0, 182580853904, 450620292374, 220713232438, 16702988424, 0, 0] := by
  decide +kernel

theorem rows6087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6087 = true := by
  decide +kernel

theorem tot6087 : totK PD2M8K2 D2M8K2.t6087 = [0, 0, 75082883077, 411303683076, 358067527592, 35245283490, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

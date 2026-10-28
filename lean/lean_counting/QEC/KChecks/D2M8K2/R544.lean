import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2176 = true := by
  decide +kernel

theorem tot2176 : totK PD2M8K2 D2M8K2.t2176 = [0, 0, 210763316433, 486915955170, 184505746192, 9587713104, 0, 0] := by
  decide +kernel

theorem rows2177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2177 = true := by
  decide +kernel

theorem tot2177 : totK PD2M8K2 D2M8K2.t2177 = [0, 84547450418, 311944385637, 385186733079, 98271379120, 3462014130, 0, 0] := by
  decide +kernel

theorem rows2178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2178 = true := by
  decide +kernel

theorem tot2178 : totK PD2M8K2 D2M8K2.t2178 = [0, 174719665843, 457169800558, 253390500251, 22307090722, 0, 0, 0] := by
  decide +kernel

theorem rows2179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2179 = true := by
  decide +kernel

theorem tot2179 : totK PD2M8K2 D2M8K2.t2179 = [0, 162653102018, 453453657306, 255782526891, 18116789228, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

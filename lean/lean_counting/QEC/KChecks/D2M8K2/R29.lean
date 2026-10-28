import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t116 = true := by
  decide +kernel

theorem tot116 : totK PD2M8K2 D2M8K2.t116 = [175716529357, 438034049531, 270045936247, 28683869737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t117 = true := by
  decide +kernel

theorem tot117 : totK PD2M8K2 D2M8K2.t117 = [72171601785, 366294792191, 370904816381, 68292503604, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t118 = true := by
  decide +kernel

theorem tot118 : totK PD2M8K2 D2M8K2.t118 = [0, 244230619427, 481484171386, 160068078756, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t119 = true := by
  decide +kernel

theorem tot119 : totK PD2M8K2 D2M8K2.t119 = [130114614269, 358479256362, 308904764095, 86084162299, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

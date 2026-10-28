import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7816 = true := by
  decide +kernel

theorem tot7816 : totK PD2M8K2 D2M8K2.t7816 = [0, 177769216434, 451823665587, 262196029946, 22060016520, 0, 0, 0] := by
  decide +kernel

theorem rows7817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7817 = true := by
  decide +kernel

theorem tot7817 : totK PD2M8K2 D2M8K2.t7817 = [0, 80669805643, 367518535765, 371120372037, 72591400227, 1163840124, 0, 0] := by
  decide +kernel

theorem rows7818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7818 = true := by
  decide +kernel

theorem tot7818 : totK PD2M8K2 D2M8K2.t7818 = [0, 0, 246280764678, 495886554883, 153150196619, 8417083954, 0, 0] := by
  decide +kernel

theorem rows7819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7819 = true := by
  decide +kernel

theorem tot7819 : totK PD2M8K2 D2M8K2.t7819 = [0, 141706202556, 375562790605, 297427522257, 82647362255, 3455941720, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

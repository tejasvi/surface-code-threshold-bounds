import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12764 = true := by
  decide +kernel

theorem tot12764 : totK PD2M8K2 D2M8K2.t12764 = [0, 183101924924, 463500640327, 260196340952, 24353463119, 0, 0, 0] := by
  decide +kernel

theorem rows12765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12765 = true := by
  decide +kernel

theorem tot12765 : totK PD2M8K2 D2M8K2.t12765 = [0, 173646908930, 475724485517, 239408334697, 12480931912, 0, 0, 0] := by
  decide +kernel

theorem rows12766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12766 = true := by
  decide +kernel

theorem tot12766 : totK PD2M8K2 D2M8K2.t12766 = [0, 0, 282472036919, 502901862228, 111810010986, 1164319620, 0, 0] := by
  decide +kernel

theorem rows12767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12767 = true := by
  decide +kernel

theorem tot12767 : totK PD2M8K2 D2M8K2.t12767 = [0, 0, 194463237048, 477163517313, 189094823044, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

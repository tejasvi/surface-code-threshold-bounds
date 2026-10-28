import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12948 = true := by
  decide +kernel

theorem tot12948 : totK PD2M8K2 D2M8K2.t12948 = [0, 0, 185079162298, 465709640561, 230194324519, 16931500750, 0, 0] := by
  decide +kernel

theorem rows12949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12949 = true := by
  decide +kernel

theorem tot12949 : totK PD2M8K2 D2M8K2.t12949 = [0, 0, 0, 361983652977, 487043354549, 50420754585, 0, 0] := by
  decide +kernel

theorem rows12950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12950 = true := by
  decide +kernel

theorem tot12950 : totK PD2M8K2 D2M8K2.t12950 = [0, 0, 108247971101, 348782330246, 351763004598, 85613368205, 1415142070, 0] := by
  decide +kernel

theorem rows12951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12951 = true := by
  decide +kernel

theorem tot12951 : totK PD2M8K2 D2M8K2.t12951 = [0, 0, 176036883041, 450632270818, 267919579228, 27343338882, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

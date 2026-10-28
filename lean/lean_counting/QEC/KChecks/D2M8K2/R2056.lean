import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8224 = true := by
  decide +kernel

theorem tot8224 : totK PD2M8K2 D2M8K2.t8224 = [0, 199890493300, 479196922025, 175361125472, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows8225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8225 = true := by
  decide +kernel

theorem tot8225 : totK PD2M8K2 D2M8K2.t8225 = [156794136647, 437227713651, 267519016639, 46011678991, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows8226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8226 = true := by
  decide +kernel

theorem tot8226 : totK PD2M8K2 D2M8K2.t8226 = [177386144956, 447532013468, 255066943235, 18345163188, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8227 = true := by
  decide +kernel

theorem tot8227 : totK PD2M8K2 D2M8K2.t8227 = [87186011136, 362400173031, 373968683764, 70020380495, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

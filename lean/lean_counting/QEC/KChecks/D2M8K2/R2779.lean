import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11116 = true := by
  decide +kernel

theorem tot11116 : totK PD2M8K2 D2M8K2.t11116 = [0, 69566023343, 254597955266, 390820116570, 136132156998, 10582051848, 0, 0] := by
  decide +kernel

theorem rows11117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11117 = true := by
  decide +kernel

theorem tot11117 : totK PD2M8K2 D2M8K2.t11117 = [0, 176292517463, 472414666152, 240473024916, 12608798092, 0, 0, 0] := by
  decide +kernel

theorem rows11118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11118 = true := by
  decide +kernel

theorem tot11118 : totK PD2M8K2 D2M8K2.t11118 = [0, 168696510211, 461409207595, 237875346919, 12597559134, 0, 0, 0] := by
  decide +kernel

theorem rows11119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11119 = true := by
  decide +kernel

theorem tot11119 : totK PD2M8K2 D2M8K2.t11119 = [0, 0, 279662651066, 512094070297, 101240228957, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4352 = true := by
  decide +kernel

theorem tot4352 : totK PD2M8K2 D2M8K2.t4352 = [0, 0, 0, 256123069195, 439546591793, 179394561019, 13845170594, 0] := by
  decide +kernel

theorem rows4353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4353 = true := by
  decide +kernel

theorem tot4353 : totK PD2M8K2 D2M8K2.t4353 = [0, 0, 0, 243913536006, 460912285733, 206107672125, 19811531983, 0] := by
  decide +kernel

theorem rows4354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4354 = true := by
  decide +kernel

theorem tot4354 : totK PD2M8K2 D2M8K2.t4354 = [0, 0, 0, 190322034718, 462377008607, 229733661849, 10262979375, 0] := by
  decide +kernel

theorem rows4355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4355 = true := by
  decide +kernel

theorem tot4355 : totK PD2M8K2 D2M8K2.t4355 = [0, 0, 0, 213253555948, 463265825680, 214614167305, 12496597301, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

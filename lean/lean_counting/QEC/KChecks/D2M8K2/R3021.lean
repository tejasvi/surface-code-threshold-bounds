import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12084 = true := by
  decide +kernel

theorem tot12084 : totK PD2M8K2 D2M8K2.t12084 = [0, 138246193677, 352285003229, 260599056896, 120935009686, 11591256473, 0, 0] := by
  decide +kernel

theorem rows12085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12085 = true := by
  decide +kernel

theorem tot12085 : totK PD2M8K2 D2M8K2.t12085 = [0, 189270964621, 464185109685, 218321644392, 12186818197, 0, 0, 0] := by
  decide +kernel

theorem rows12086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12086 = true := by
  decide +kernel

theorem tot12086 : totK PD2M8K2 D2M8K2.t12086 = [0, 84236580386, 371684588243, 354639669607, 58694490476, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12087 = true := by
  decide +kernel

theorem tot12087 : totK PD2M8K2 D2M8K2.t12087 = [0, 0, 298392962244, 511490465527, 71657872062, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

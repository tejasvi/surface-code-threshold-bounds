import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9948 = true := by
  decide +kernel

theorem tot9948 : totK PD2M8K2 D2M8K2.t9948 = [0, 0, 0, 237960158299, 510202558224, 144673099600, 2447226230, 0] := by
  decide +kernel

theorem rows9949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9949 = true := by
  decide +kernel

theorem tot9949 : totK PD2M8K2 D2M8K2.t9949 = [0, 0, 0, 204537167841, 480140966176, 172144499133, 9490596806, 0] := by
  decide +kernel

theorem rows9950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9950 = true := by
  decide +kernel

theorem tot9950 : totK PD2M8K2 D2M8K2.t9950 = [0, 0, 0, 198855692451, 458530406386, 191370006860, 12727931539, 0] := by
  decide +kernel

theorem rows9951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9951 = true := by
  decide +kernel

theorem tot9951 : totK PD2M8K2 D2M8K2.t9951 = [0, 0, 0, 214523973440, 475816200715, 151220536163, 9540878940, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

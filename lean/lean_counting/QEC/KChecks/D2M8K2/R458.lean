import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1832 = true := by
  decide +kernel

theorem tot1832 : totK PD2M8K2 D2M8K2.t1832 = [0, 0, 187015304326, 464097233199, 243206524045, 18610034112, 0, 0] := by
  decide +kernel

theorem rows1833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1833 = true := by
  decide +kernel

theorem tot1833 : totK PD2M8K2 D2M8K2.t1833 = [0, 0, 115491960739, 445806014829, 303606511394, 19136285970, 0, 0] := by
  decide +kernel

theorem rows1834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1834 = true := by
  decide +kernel

theorem tot1834 : totK PD2M8K2 D2M8K2.t1834 = [0, 0, 30981187624, 319108360164, 452505385689, 84560603103, 1415142070, 0] := by
  decide +kernel

theorem rows1835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1835 = true := by
  decide +kernel

theorem tot1835 : totK PD2M8K2 D2M8K2.t1835 = [0, 0, 194064849396, 461499367125, 239154351944, 21616626967, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

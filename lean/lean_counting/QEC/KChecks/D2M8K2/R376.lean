import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1504 = true := by
  decide +kernel

theorem tot1504 : totK PD2M8K2 D2M8K2.t1504 = [0, 182952986560, 465091062478, 244640645353, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows1505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1505 = true := by
  decide +kernel

theorem tot1505 : totK PD2M8K2 D2M8K2.t1505 = [0, 168057358828, 463580027830, 259370818424, 18959421031, 0, 0, 0] := by
  decide +kernel

theorem rows1506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1506 = true := by
  decide +kernel

theorem tot1506 : totK PD2M8K2 D2M8K2.t1506 = [0, 0, 277221102100, 515882144993, 110309628221, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1507 = true := by
  decide +kernel

theorem tot1507 : totK PD2M8K2 D2M8K2.t1507 = [0, 138273776836, 426598190628, 315987404320, 32696934811, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

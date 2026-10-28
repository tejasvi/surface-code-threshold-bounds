import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1804 = true := by
  decide +kernel

theorem tot1804 : totK PD2M8K2 D2M8K2.t1804 = [0, 0, 181193378363, 480083284220, 215363207661, 10372644569, 0, 0] := by
  decide +kernel

theorem rows1805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1805 = true := by
  decide +kernel

theorem tot1805 : totK PD2M8K2 D2M8K2.t1805 = [0, 0, 187718952986, 444978382013, 218727228330, 16861767938, 0, 0] := by
  decide +kernel

theorem rows1806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1806 = true := by
  decide +kernel

theorem tot1806 : totK PD2M8K2 D2M8K2.t1806 = [0, 0, 195597148711, 499828398575, 197382072158, 5265834820, 0, 0] := by
  decide +kernel

theorem rows1807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1807 = true := by
  decide +kernel

theorem tot1807 : totK PD2M8K2 D2M8K2.t1807 = [0, 0, 166404757313, 460761136452, 242796037331, 12210221822, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

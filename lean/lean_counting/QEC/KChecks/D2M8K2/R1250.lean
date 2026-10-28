import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5000 = true := by
  decide +kernel

theorem tot5000 : totK PD2M8K2 D2M8K2.t5000 = [0, 0, 0, 202620719322, 520909167161, 167111086043, 2484078857, 0] := by
  decide +kernel

theorem rows5001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5001 = true := by
  decide +kernel

theorem tot5001 : totK PD2M8K2 D2M8K2.t5001 = [0, 174993452374, 427731142439, 179290403495, 44022059309, 51815692439, 5679676912, 0] := by
  decide +kernel

theorem rows5002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5002 = true := by
  decide +kernel

theorem tot5002 : totK PD2M8K2 D2M8K2.t5002 = [0, 202180892012, 461478897322, 204942537198, 14001064343, 0, 0, 0] := by
  decide +kernel

theorem rows5003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5003 = true := by
  decide +kernel

theorem tot5003 : totK PD2M8K2 D2M8K2.t5003 = [0, 0, 288350835632, 493263281118, 100370649463, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
